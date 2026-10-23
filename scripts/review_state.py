"""Versioned editorial review state. Only metadata is writable; manuscripts are read-only.

The same command dispatcher backs the CLI and the local web application. No
third-party dependencies are required. Content checks and editorial judgement
remain separate: a digest is evidence of identity, never evidence of quality.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import uuid

CHECKS = {"context": "문장과 문맥", "content": "설명과 선수 지식", "structure": "구성과 배치",
          "proof": "예제와 증명", "exercise": "연습문제", "runtime": "실행과 화면", "boundary": "주변 범위와의 연결"}
LEVELS = {"book", "chapter", "section", "explanation", "paragraph", "sentence", "exercise", "code"}
PROTOCOL_FILES = ("REVIEW_PROCESS.md", "STYLE.md", "AGENTS.md", "REVIEW_TEMPLATE.md")
ID = re.compile(r"^[a-zA-Z0-9][a-zA-Z0-9_.-]{0,99}$")


class ReviewError(ValueError):
    """A user-actionable error; callers must preserve the previous state."""


def digest(value):
    data = json.dumps(value, sort_keys=True, ensure_ascii=False).encode("utf-8")
    return hashlib.sha256(data).hexdigest()


def now():
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def required(value, label):
    if not isinstance(value, str) or not value.strip():
        raise ReviewError(f"{label}을 입력하세요.")
    return value.strip()


class ReviewStore:
    def __init__(self, root):
        self.root = Path(root).resolve()
        self.path = self.root / "review/state.json"
        self.local = self.root / "review/local"

    def source_path(self, value):
        value = required(value, "파일 경로")
        p = Path(value)
        if p.is_absolute() or ".." in p.parts or "\\" in value or ":" in value:
            raise ReviewError("저장소 안의 상대 경로를 사용하세요.")
        resolved = (self.root / p).resolve()
        if not resolved.is_relative_to(self.root) or any(x in {".git", ".lake", "local"} for x in p.parts):
            raise ReviewError("이 경로는 검토 대상으로 사용할 수 없습니다.")
        return resolved

    def text(self, path):
        p = self.source_path(path)
        try:
            return p.read_text(encoding="utf-8-sig")
        except (OSError, UnicodeError) as ex:
            raise ReviewError(f"파일을 읽을 수 없습니다: {path}") from ex

    @staticmethod
    def bounds(text, selector):
        start, end = selector.get("after", ""), selector.get("before", "")
        for marker in (start, end):
            if marker and text.count(marker) != 1:
                raise ReviewError("경계 문구가 없거나 여러 번 나타납니다. 고유한 문구로 범위를 다시 지정하세요.")
        a = text.index(start) + len(start) if start else 0
        b = text.index(end) if end else len(text)
        if a > b:
            raise ReviewError("범위의 시작과 끝 순서가 바뀌었습니다.")
        return a, b

    def selected(self, selector):
        text = self.text(selector["path"])
        a, b = self.bounds(text, selector)
        return text[a:b]

    def signature(self, selectors):
        values, errors = [], []
        for selector in selectors:
            try:
                values.append([selector, self.selected(selector)])
            except ReviewError as ex:
                errors.append(str(ex) + " (" + selector.get("path", "?") + ")")
                values.append([selector, "ERROR", str(ex)])
        return digest(values), errors

    def unit_signature(self, s, uid):
        """Watch a unit's own text, excluding explicitly registered child regions.

        A parent still displays its entire passage for reading. Child changes
        affect the aggregate, not the parent's own checks, unless linked by an
        explicit dependency. This also permits progressively finer registration.
        """
        descendants, todo = [], [uid]
        while todo:
            parent = todo.pop()
            children = [k for k, u in s["units"].items() if u["parent"] == parent]
            descendants.extend(children)
            todo.extend(children)
        values, errors = [], []
        for source in s["units"][uid]["sources"]:
            try:
                text = self.text(source["path"])
                a, b = self.bounds(text, source)
                intervals = []
                for child in descendants:
                    for region in s["units"][child]["sources"]:
                        if region["path"] == source["path"]:
                            ca, cb = self.bounds(text, region)
                            if a <= ca <= cb <= b:
                                intervals.append((ca - a, cb - a))
                merged = []
                for ca, cb in sorted(intervals):
                    if merged and ca <= merged[-1][1]:
                        merged[-1][1] = max(cb, merged[-1][1])
                    else:
                        merged.append([ca, cb])
                content = text[a:b]
                for ca, cb in reversed(merged):
                    content = content[:ca] + "\0CHILD_SCOPE\0" + content[cb:]
                values.append([source, content])
            except ReviewError as ex:
                errors.append(str(ex) + " (" + source.get("path", "?") + ")")
                values.append([source, "ERROR", str(ex)])
        return digest(values), errors

    def load(self):
        if not self.path.exists():
            scopes = self.root / "review/scopes.json"
            try:
                config = json.loads(scopes.read_text(encoding="utf-8"))
                if config.get("schema") != 1 or not isinstance(config.get("units"), list):
                    raise ValueError("Invalid initial scopes")
                state = {"schema": 1, "revision": 0, "units": {},
                         "dependencies": [], "tasks": {}, "history": []}
                for unit in config["units"]:
                    self.register(state, unit)
                return state
            except (OSError, ValueError, TypeError) as ex:
                raise ReviewError("초기 검토 범위를 읽을 수 없습니다. review/scopes.json을 확인하세요.") from ex
        try:
            s = json.loads(self.path.read_text(encoding="utf-8"))
        except (OSError, ValueError) as ex:
            raise ReviewError("검토 상태를 읽을 수 없습니다. review/state.json을 확인하세요.") from ex
        if s.get("schema") != 1:
            raise ReviewError("지원하지 않는 검토 상태 형식입니다.")
        return s

    @staticmethod
    def check(s, key):
        try:
            unit, aspect = key.split("/", 1)
            return s["units"][unit]["checks"][aspect]
        except (KeyError, ValueError) as ex:
            raise ReviewError(f"검토 항목을 찾을 수 없습니다: {key}") from ex

    @staticmethod
    def event(s, action, **data):
        s["history"].append({"at": now(), "action": action, **data})

    @staticmethod
    def active(s):
        return next((t for t in s["tasks"].values() if t["status"] == "open"), None)

    def invalidate(self, s, keys, reason, origin):
        cause = {"id": uuid.uuid4().hex, "reason": reason, "origin": origin, "at": now()}
        queue, seen = list(keys), set()
        while queue:
            key = queue.pop(0)
            if key in seen:
                continue
            seen.add(key)
            c = self.check(s, key)
            c["state"] = "dirty"
            c["generation"] += 1
            c["causes"].append(cause)
            queue += [d["to"] for d in s["dependencies"] if d["from"] == key]
        task = self.active(s)
        if task:
            task["required"] = sorted(set(task["required"]) | seen)
        self.event(s, "invalidate", checks=sorted(seen), cause=cause)

    def scan(self, s):
        files = [[name, self.text(name) if (self.root / name).is_file() else None] for name in PROTOCOL_FILES]
        version = digest(files)
        previous = s.get("protocol")
        if previous is None or previous["signature"] != version:
            keys = [f"{uid}/{a}" for uid, unit in s["units"].items() for a in unit["checks"]]
            legacy = previous is None and any(c["receipt"] for u in s["units"].values() for c in u["checks"].values())
            changed = previous is not None or (legacy and any(value is not None for _, value in files))
            s["protocol"] = {"signature": version, "files": list(PROTOCOL_FILES),
                "changed_at": now() if changed else None, "targets": keys if changed else []}
            if changed:
                self.invalidate(s, keys, "검토 기준이 변경됨: 전역 재검토 후 현재 기준의 근거로 판정해야 함", "protocol")
        changed = []
        for uid, unit in s["units"].items():
            signature, errors = self.unit_signature(s, uid)
            unit["errors"] = errors
            if unit["observed"] != signature:
                unit["observed"] = signature
                changed.extend(f"{uid}/{a}" for a in unit["checks"])
        if changed:
            self.invalidate(s, changed, "등록 범위의 내용 또는 경계가 변경됨", "scan")
        task = self.active(s)
        if task:
            stamp, errors = self.signature(task["read_scope"])
            task["read_errors"] = errors
            if task["read_stamp"] != stamp:
                task["read_stamp"] = stamp
                self.invalidate(s, task["required"], "작업의 참조 범위가 변경됨", "read_scope")

    def inputs(self, s, key, seen=None):
        seen = set() if seen is None else seen
        if key in seen:
            raise ReviewError("검토 의존 관계에 순환이 있습니다.")
        seen = seen | {key}
        unit = s["units"][key.split("/")[0]]
        stamp, errors = self.unit_signature(s, key.split("/")[0])
        # A parent review reads its children even though their edits do not
        # automatically invalidate the parent's own editorial judgement.
        subtree, todo = [], [key.split("/")[0]]
        while todo:
            parent = todo.pop()
            children = [k for k, u in s["units"].items() if u["parent"] == parent]
            todo.extend(children)
            for child in children:
                child_stamp, child_errors = self.unit_signature(s, child)
                errors.extend(child_errors)
                subtree.append([child, child_stamp, [c["generation"] for c in s["units"][child]["checks"].values()]])
        incoming = []
        for edge in s["dependencies"]:
            if edge["to"] == key:
                dep_stamp, dep_errors = self.inputs(s, edge["from"], seen)
                incoming.append([edge["from"], dep_stamp])
                errors.extend(dep_errors)
        task = self.active(s)
        context = task["read_stamp"] if task and key in task["required"] else None
        c = self.check(s, key)
        return digest([stamp, subtree, incoming, c["generation"], context, s.get("protocol", {}).get("signature")]), errors

    def register(self, s, args):
        uid = required(args.get("id"), "범위 ID")
        if not ID.fullmatch(uid) or uid in s["units"]:
            raise ReviewError("범위 ID는 중복되지 않는 영문·숫자·점·밑줄·하이픈으로 지정하세요.")
        parent = args.get("parent") or None
        if parent and parent not in s["units"]:
            raise ReviewError("상위 범위를 찾을 수 없습니다.")
        level = args.get("level", "explanation")
        if level not in LEVELS:
            raise ReviewError("올바른 층위를 선택하세요.")
        sources = args.get("sources", [])
        for source in sources:
            self.selected(source)
        aspects = args.get("checks", ["context", "content"])
        if not aspects or any(a not in CHECKS for a in aspects):
            raise ReviewError("검토 항목을 선택하세요.")
        s["units"][uid] = {"title": required(args.get("title"), "범위 이름"), "level": level,
            "parent": parent, "sources": sources, "observed": self.signature(sources)[0], "errors": [],
            "checks": {a: {"state": "unknown", "generation": 0, "causes": [], "receipt": None} for a in aspects}}
        # Splitting an existing range adds unknown child checks; it is not an edit.
        ancestor = parent
        while ancestor:
            s["units"][ancestor]["observed"] = self.unit_signature(s, ancestor)[0]
            ancestor = s["units"][ancestor]["parent"]
        self.event(s, "register", unit=uid)

    def inventory(self):
        result = subprocess.run(["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"],
                                cwd=self.root, capture_output=True)
        if result.returncode:
            raise ReviewError("수정 범위를 비교하려면 Git 저장소가 필요합니다.")
        hashes = {}
        for name in result.stdout.decode("utf-8").split("\0"):
            # State changes and local snapshots are managed separately, not manuscript edits.
            if not name or name == "review/state.json" or name.startswith("review/local/"):
                continue
            p = self.root / name
            if p.is_file():
                self.source_path(name)
                hashes[name] = hashlib.sha256(p.read_bytes()).hexdigest()
        return hashes

    def snapshot(self, task):
        return {"hashes": self.inventory(), "texts": {x["path"]: self.source_path(x["path"]).read_bytes().decode("utf-8") for x in task["edit_scope"]}}

    @staticmethod
    def masked(text, selectors):
        # Match canonical LF anchors, but compare unedited text byte-faithfully:
        # changing a whole file from CRLF to LF is still an out-of-scope edit.
        normalized, offsets = [], []
        for i, char in enumerate(text):
            if char == "\r" and text[i:i + 2] == "\r\n":
                continue
            offsets.append(i - 1 if char == "\n" and i and text[i - 1] == "\r" else i)
            normalized.append(char)
        offsets.append(len(text))
        canonical = "".join(normalized)
        intervals = []
        for selector in selectors:
            a, b = ReviewStore.bounds(canonical, selector)
            intervals.append((offsets[a], offsets[b]))
        intervals.sort()
        merged = []
        for a, b in intervals:
            if merged and a <= merged[-1][1]:
                merged[-1][1] = max(b, merged[-1][1])
            else:
                merged.append([a, b])
        for a, b in reversed(merged):
            text = text[:a] + "\0EDIT_SCOPE\0" + text[b:]
        return text

    def audit(self, task):
        try:
            base = json.loads((self.local / (task["id"] + ".json")).read_text(encoding="utf-8"))
        except (OSError, ValueError) as ex:
            raise ReviewError("작업 시작 기준 파일이 없습니다. 다른 컴퓨터에서 만든 작업은 이곳에서 완료할 수 없습니다.") from ex
        current, violations, changed = self.inventory(), [], []
        for path in sorted(set(base["hashes"]) | set(current)):
            if base["hashes"].get(path) == current.get(path):
                continue
            changed.append(path)
            selectors = [x for x in task["edit_scope"] if x["path"] == path]
            if not selectors:
                violations.append({"path": path, "reason": "수정 허용 범위 밖의 파일"})
                continue
            if any(not x.get("after") and not x.get("before") for x in selectors):
                continue
            try:
                raw = self.source_path(path).read_bytes().decode("utf-8")
                if self.masked(base["texts"][path], selectors) != self.masked(raw, selectors):
                    violations.append({"path": path, "reason": "지정한 문구 경계 밖의 변경"})
            except (ReviewError, KeyError, OSError, UnicodeError) as ex:
                violations.append({"path": path, "reason": str(ex)})
        return {"changed": changed, "violations": violations}

    def task_scopes(self, s, ids):
        scopes = []
        for uid in ids:
            if uid not in s["units"]:
                raise ReviewError("범위를 찾을 수 없습니다: " + uid)
            if not s["units"][uid]["sources"]:
                raise ReviewError("파일 경계가 있는 하위 범위를 선택하세요: " + uid)
            scopes.extend(s["units"][uid]["sources"])
        return scopes

    def operate(self, s, action, a):
        if action == "register":
            self.register(s, a)
        elif action == "relocate":
            uid = a["unit"]
            if uid not in s["units"]:
                raise ReviewError("범위를 찾을 수 없습니다.")
            reason = required(a.get("reason"), "경계를 다시 지정하는 이유")
            sources = a["sources"]
            for selector in sources:
                self.selected(selector)
            unit = s["units"][uid]
            self.event(s, "relocate", unit=uid, previous=unit["sources"], sources=sources, reason=reason)
            unit["sources"] = sources
            unit["observed"], unit["errors"] = self.unit_signature(s, uid)
            self.invalidate(s, [f"{uid}/{c}" for c in unit["checks"]], reason, "relocate")
        elif action == "dirty":
            self.invalidate(s, a["checks"], required(a.get("reason"), "변경 이유"), "manual")
        elif action == "link":
            edge = {"from": a["from"], "to": a["to"], "reason": required(a.get("reason"), "의존 이유")}
            self.check(s, edge["from"])
            self.check(s, edge["to"])
            if any(d["from"] == edge["from"] and d["to"] == edge["to"] for d in s["dependencies"]):
                raise ReviewError("이미 연결된 검토 항목입니다.")
            s["dependencies"].append(edge)
            self.inputs(s, edge["to"])  # Reject cycles before persisting.
            self.invalidate(s, [edge["to"]], edge["reason"], "dependency")
        elif action == "unlink":
            edge = next((d for d in s["dependencies"] if d["from"] == a["from"] and d["to"] == a["to"]), None)
            if edge is None:
                raise ReviewError("해제할 의존 관계가 없습니다.")
            reason = required(a.get("reason"), "연결을 해제하는 이유")
            s["dependencies"].remove(edge)
            self.event(s, "unlink", edge=edge, reason=reason)
            self.invalidate(s, [edge["to"]], reason, "dependency_removed")
        elif action == "prepare":
            key = a["check"]
            stamp, errors = self.inputs(s, key)
            if errors:
                raise ReviewError(" / ".join(errors))
            return {"check": key, "stamp": stamp, "causes": [c["id"] for c in self.check(s, key)["causes"]]}
        elif action == "accept":
            key, ticket = a["check"], a["ticket"]
            stamp, errors = self.inputs(s, key)
            c = self.check(s, key)
            if errors or ticket.get("check") != key or ticket.get("stamp") != stamp:
                raise ReviewError("검토를 시작한 뒤 내용이나 의존 입력이 바뀌었습니다. 다시 확인하세요.")
            if set(ticket.get("causes", [])) != {x["id"] for x in c["causes"]}:
                raise ReviewError("확인하지 않은 변경 원인이 남아 있습니다.")
            pending = [d["from"] for d in s["dependencies"] if d["to"] == key and self.check(s, d["from"])["state"] != "clean"]
            if pending:
                raise ReviewError("먼저 의존 항목을 검토하세요: " + ", ".join(pending))
            evidence = required(a.get("evidence"), "검토 근거")
            reviewer = required(a.get("reviewer"), "검토자")
            verdict = a.get("verdict", "clean")
            if verdict not in {"clean", "not_applicable"}:
                raise ReviewError("검토 결과를 선택하세요.")
            receipt = {"stamp": stamp, "evidence": evidence, "reviewer": reviewer, "at": now(),
                       "verdict": verdict, "resolved": copy.deepcopy(c["causes"]),
                       "protocol": s.get("protocol", {}).get("signature")}
            c.update(state=verdict, causes=[], receipt=receipt)
            self.event(s, "accept", check=key, receipt=receipt)
        elif action == "begin":
            if self.active(s):
                raise ReviewError("진행 중인 수정 작업을 먼저 마치세요.")
            required_checks = list(a.get("required", []))
            for uid in a.get("edit_units", []):
                if uid not in s["units"]:
                    raise ReviewError("수정 범위를 찾을 수 없습니다.")
                unit = s["units"][uid]
                required_checks.extend(f"{uid}/{c}" for c in unit["checks"])
                parent = s["units"].get(unit["parent"])
                if parent:
                    boundary = "boundary" if "boundary" in parent["checks"] else "structure" if "structure" in parent["checks"] else None
                    if boundary:
                        required_checks.append(f"{unit['parent']}/{boundary}")
            if not required_checks:
                raise ReviewError("이 작업의 완료에 필요한 검토 항목을 선택하세요.")
            for key in required_checks:
                self.check(s, key)
            edit = self.task_scopes(s, a.get("edit_units", []))
            if not edit:
                raise ReviewError("수정할 범위를 선택하세요.")
            read = self.task_scopes(s, a.get("read_units", []))
            task = {"id": "task-" + uuid.uuid4().hex[:12], "title": required(a.get("title"), "작업 이름"),
                    "reason": required(a.get("reason"), "수정 목적"), "invariants": required(a.get("invariants"), "유지할 조건"),
                    "edit_scope": edit, "read_scope": read, "required": sorted(set(required_checks)),
                    "read_stamp": self.signature(read)[0], "status": "open", "started": now(), "expansions": []}
            self.local.mkdir(parents=True, exist_ok=True)
            (self.local / (task["id"] + ".json")).write_text(json.dumps(self.snapshot(task), ensure_ascii=False), encoding="utf-8")
            s["tasks"][task["id"]] = task
            self.invalidate(s, required_checks, task["reason"], task["id"])
            self.event(s, "begin", task=task["id"])
        elif action == "expand":
            task = self.active(s)
            if not task:
                raise ReviewError("진행 중인 수정 작업이 없습니다.")
            if self.audit(task)["violations"]:
                raise ReviewError("이미 범위 밖의 변경이 있습니다. 범위 확대는 수정 전에 기록해야 합니다.")
            scopes = self.task_scopes(s, a.get("edit_units", []))
            reason = required(a.get("reason"), "범위를 넓히는 이유")
            base_path = self.local / (task["id"] + ".json")
            base = json.loads(base_path.read_text(encoding="utf-8"))
            for x in scopes:
                base["texts"].setdefault(x["path"], self.source_path(x["path"]).read_bytes().decode("utf-8"))
            task["edit_scope"].extend(x for x in scopes if x not in task["edit_scope"])
            task["expansions"].append({"at": now(), "reason": reason, "scopes": scopes})
            base_path.write_text(json.dumps(base, ensure_ascii=False), encoding="utf-8")
            keys = [f"{u}/{c}" for u in a.get("edit_units", []) for c in s["units"][u]["checks"]]
            self.invalidate(s, keys, reason, "scope_expansion")
        elif action == "finish":
            task = self.active(s)
            if not task:
                raise ReviewError("진행 중인 수정 작업이 없습니다.")
            audit = self.audit(task)
            if audit["violations"]:
                raise ReviewError("허용 범위 밖의 변경이 남아 있습니다.")
            pending = [k for k in task["required"] if self.check(s, k)["state"] not in {"clean", "not_applicable"}]
            if pending or task.get("read_errors"):
                raise ReviewError("미완료 검토가 남아 있습니다: " + ", ".join(pending))
            task.update(status="complete", finished=now(), boundary=required(a.get("boundary"), "상위 경계에서 검토를 멈추는 근거"), audit=audit)
            self.event(s, "finish", task=task["id"], boundary=task["boundary"])
        elif action == "stop":
            task = self.active(s)
            if not task:
                raise ReviewError("진행 중인 수정 작업이 없습니다.")
            reason = required(a.get("reason"), "작업을 중단하는 이유")
            try:
                audit = self.audit(task)
            except ReviewError as ex:
                audit = {"changed": [], "violations": [{"path": "", "reason": str(ex)}]}
            task.update(status="stopped", stopped=now(), stop_reason=reason, audit=audit)
            self.event(s, "stop", task=task["id"], reason=reason)
        elif action not in {"scan", "status", "source"}:
            raise ReviewError("알 수 없는 관리 명령입니다.")
        if action == "source":
            unit = s["units"].get(a.get("unit"))
            if unit is None:
                raise ReviewError("범위를 찾을 수 없습니다.")
            return [{"selector": x, "text": self.selected(x)} for x in unit["sources"]]
        return None

    def view(self, s):
        view = copy.deepcopy(s)
        protocol = view.get("protocol", {})
        targets = protocol.get("targets", [])
        remaining = [key for key in targets if (self.check(s, key).get("receipt") or {}).get("protocol") != protocol.get("signature")]
        view["protocol_review"] = {"pending": len(remaining), "total": len(targets),
            "changed_at": protocol.get("changed_at"), "signature": protocol.get("signature")}
        for uid, unit in view["units"].items():
            descendants = set()
            todo = [uid]
            while todo:
                parent = todo.pop()
                children = [k for k, u in view["units"].items() if u["parent"] == parent]
                descendants.update(children)
                todo.extend(children)
            counts = {state: 0 for state in ("dirty", "unknown", "clean", "not_applicable")}
            for child in descendants:
                for check in view["units"][child]["checks"].values():
                    counts[check["state"]] += 1
            unit["descendants"] = counts
            unit["contains_dirty"] = counts["dirty"] > 0
        task = self.active(view)
        if task:
            try:
                task["audit"] = self.audit(task)
            except ReviewError as ex:
                task["audit"] = {"changed": [], "violations": [{"path": "", "reason": str(ex)}]}
        view["check_labels"] = CHECKS
        return view

    def execute(self, action="status", args=None, expected=None):
        """Serialize all callers; optimistic revisions protect different browser tabs."""
        self.local.mkdir(parents=True, exist_ok=True)
        lock = self.local / "write.lock"
        try:
            fd = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
        except FileExistsError as ex:
            raise ReviewError("다른 작업이 상태를 저장 중입니다. 잠시 후 다시 시도하세요.") from ex
        try:
            os.close(fd)
            original = self.load()
            s = copy.deepcopy(original)
            if expected is not None and expected != s["revision"]:
                raise ReviewError("다른 화면에서 상태가 바뀌었습니다. 새로 불러온 뒤 다시 확인하세요.")
            self.scan(s)
            result = self.operate(s, action, args or {})
            if s != original:
                s["revision"] += 1
                self.path.parent.mkdir(parents=True, exist_ok=True)
                (self.local / "state.previous.json").write_text(json.dumps(original, ensure_ascii=False, indent=2), encoding="utf-8")
                temp = self.local / "state.next.json"
                with temp.open("w", encoding="utf-8", newline="\n") as out:
                    json.dump(s, out, ensure_ascii=False, indent=2)
                    out.write("\n")
                    out.flush()
                    os.fsync(out.fileno())
                os.replace(temp, self.path)
            return {"state": self.view(s), "result": result}
        finally:
            lock.unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", nargs="?", default="status")
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--input", type=Path, help="JSON command arguments (UTF-8)")
    parser.add_argument("--revision", type=int)
    args = parser.parse_args()
    try:
        params = json.loads(args.input.read_text(encoding="utf-8")) if args.input else {}
        print(json.dumps(ReviewStore(args.root).execute(args.command, params, args.revision), ensure_ascii=False, indent=2))
    except ReviewError as ex:
        print(str(ex), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
