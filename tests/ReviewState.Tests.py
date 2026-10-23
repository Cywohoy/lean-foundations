"""Behavioral regression tests. No server is started and no book file is edited."""
import copy
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import types
import unittest

SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS))
from review_state import ReviewError, ReviewStore
from review_server import ReviewHandler


class ReviewTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        (self.root / ".gitignore").write_text("review/local/\n", encoding="utf-8")
        self.source = self.root / "chapter.lean"
        self.source.write_text("Before\nBEGIN\nOriginal paragraph.\nEND\nAfter\n", encoding="utf-8")
        (self.root / "other.lean").write_text("Earlier knowledge.\n", encoding="utf-8")
        self.store = ReviewStore(self.root)
        s = {"schema": 1, "revision": 0, "units": {}, "dependencies": [], "tasks": {}, "history": []}
        for config in [
            {"id": "book", "title": "Book", "level": "book", "checks": ["structure"]},
            {"id": "p", "title": "Paragraph", "parent": "book", "level": "paragraph", "sources": [{"path": "chapter.lean", "after": "BEGIN\n", "before": "END\n"}], "checks": ["context", "proof"]},
            {"id": "q", "title": "Exercise", "parent": "book", "level": "exercise", "sources": [{"path": "other.lean"}], "checks": ["exercise"]},
        ]:
            self.store.register(s, config)
        self.store.path.parent.mkdir(parents=True)
        self.store.path.write_text(json.dumps(s), encoding="utf-8")

    def run_action(self, action, **kwargs):
        return self.store.execute(action, kwargs)

    def pass_check(self, key):
        ticket = self.run_action("prepare", check=key)["result"]
        return self.run_action("accept", check=key, ticket=ticket, evidence="Read the paragraph with its neighbours; the reference still denotes the same premise.", reviewer="Test reviewer")

    def begin(self):
        return self.run_action("begin", title="Revise paragraph", reason="Clarify its subject", invariants="Keep statement and ordering", edit_units=["p"], read_units=["q"], required=["p/context"])

    def edit(self):
        self.source.write_text(self.source.read_text().replace("Original", "Revised"), encoding="utf-8")

    def test_first_run_uses_scopes_without_inheriting_personal_reviews(self):
        self.store.path.unlink()
        scopes = {"schema": 1, "units": [
            {"id": "first", "title": "First chapter", "level": "chapter",
             "sources": [{"path": "chapter.lean"}], "checks": ["content", "proof"]}
        ]}
        (self.root / "review/scopes.json").write_text(json.dumps(scopes), encoding="utf-8")
        state = self.run_action("status")["state"]
        self.assertEqual(set(state["units"]), {"first"})
        self.assertFalse(state["tasks"])
        for check in state["units"]["first"]["checks"].values():
            self.assertEqual(check["state"], "unknown")
            self.assertIsNone(check["receipt"])
        self.assertTrue(self.store.path.is_file())
        self.pass_check("first/content")
        self.assertEqual(self.run_action("status")["state"]["units"]["first"]["checks"]["content"]["state"], "clean")

    def test_existing_state_takes_precedence_over_initial_scopes(self):
        (self.root / "review/scopes.json").write_text("invalid seed", encoding="utf-8")
        self.pass_check("p/context")
        state = self.run_action("status")["state"]
        self.assertIn("q", state["units"])
        self.assertEqual(state["units"]["p"]["checks"]["context"]["state"], "clean")

    def test_published_scopes_resolve_in_a_fresh_checkout(self):
        self.store.path.unlink()
        project = SCRIPTS.parent
        scope_source = project / "review/scopes.json"
        config = json.loads(scope_source.read_text(encoding="utf-8"))
        (self.root / "review/scopes.json").write_bytes(scope_source.read_bytes())
        for relative in {source["path"] for unit in config["units"] for source in unit["sources"]}:
            target = self.root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((project / relative).read_bytes())
        state = self.run_action("status")["state"]
        self.assertEqual(len(state["units"]), len(config["units"]))
        self.assertTrue(state["units"])
        self.assertFalse(state["tasks"])
        for unit in state["units"].values():
            self.assertFalse(unit["errors"])
            self.assertTrue(all(check["state"] == "unknown" for check in unit["checks"].values()))

    def test_invalid_saved_state_is_not_replaced_by_initial_scopes(self):
        self.store.path.write_text("invalid saved state", encoding="utf-8")
        (self.root / "review/scopes.json").write_text('{"schema":1,"units":[]}', encoding="utf-8")
        with self.assertRaisesRegex(ReviewError, "review/state.json"):
            self.run_action("status")
        self.assertEqual(self.store.path.read_text(encoding="utf-8"), "invalid saved state")

    def test_unknown_is_not_clean_and_parent_is_only_aggregated(self):
        self.assertEqual(self.run_action("status")["state"]["units"]["book"]["checks"]["structure"]["state"], "unknown")
        self.pass_check("book/structure")
        self.edit()
        units = self.run_action("status")["state"]["units"]
        self.assertTrue(units["book"]["contains_dirty"])
        self.assertEqual(units["book"]["checks"]["structure"]["state"], "clean")
        self.assertEqual(units["q"]["checks"]["exercise"]["state"], "unknown")

    def test_finer_child_does_not_dirty_parent_text_or_clear_child_proof(self):
        self.run_action("register", id="child", title="Finer example", parent="p", level="code",
                        sources=[{"path": "chapter.lean", "after": "BEGIN\n", "before": "END\n"}], checks=["proof"])
        self.pass_check("p/context")
        self.edit()
        units = self.run_action("status")["state"]["units"]
        self.assertEqual(units["p"]["checks"]["context"]["state"], "clean")
        self.assertTrue(units["p"]["contains_dirty"])
        self.assertEqual(units["child"]["checks"]["proof"]["state"], "dirty")

    def test_dirty_dependency_propagates_and_cycle_is_rejected(self):
        self.run_action("link", **{"from": "p/context", "to": "q/exercise", "reason": "Uses this explanation"})
        self.pass_check("p/context")
        self.pass_check("q/exercise")
        self.run_action("dirty", checks=["p/context"], reason="Ambiguous premise")
        c = self.run_action("status")["state"]["units"]["q"]["checks"]["exercise"]
        self.assertEqual(c["state"], "dirty")
        before = self.store.path.read_bytes()
        with self.assertRaises(ReviewError):
            self.run_action("link", **{"from": "q/exercise", "to": "p/context", "reason": "cycle"})
        self.assertEqual(before, self.store.path.read_bytes())

    def test_dependent_review_waits_for_its_prerequisite(self):
        self.run_action("link", **{"from": "p/context", "to": "q/exercise", "reason": "Depends on introduction"})
        with self.assertRaisesRegex(ReviewError, "의존"):
            self.pass_check("q/exercise")

    def test_stale_ticket_rejects_content_change(self):
        ticket = self.run_action("prepare", check="p/context")["result"]
        self.edit()
        with self.assertRaisesRegex(ReviewError, "바뀌"):
            self.run_action("accept", check="p/context", ticket=ticket, evidence="done", reviewer="test")
        self.assertEqual(self.run_action("status")["state"]["units"]["p"]["checks"]["context"]["state"], "dirty")

    def test_parent_ticket_rejects_changes_to_children_while_reading(self):
        ticket = self.run_action("prepare", check="book/structure")["result"]
        self.edit()
        with self.assertRaisesRegex(ReviewError, "바뀌"):
            self.run_action("accept", check="book/structure", ticket=ticket, evidence="read", reviewer="test")

    def test_exclusion_requires_current_evidence_and_is_invalidated(self):
        ticket = self.run_action("prepare", check="p/proof")["result"]
        self.run_action("accept", check="p/proof", ticket=ticket, evidence="This passage contains no proof or example.", reviewer="test", verdict="not_applicable")
        self.assertEqual(self.store.load()["units"]["p"]["checks"]["proof"]["state"], "not_applicable")
        self.edit()
        self.assertEqual(self.run_action("status")["state"]["units"]["p"]["checks"]["proof"]["state"], "dirty")

    def test_unlink_keeps_target_dirty(self):
        edge = {"from": "p/context", "to": "q/exercise", "reason": "Uses result"}
        self.run_action("link", **edge)
        self.run_action("unlink", **{**edge, "reason": "Exercise now uses a different result"})
        self.assertEqual(self.store.load()["dependencies"], [])
        self.assertEqual(self.store.load()["units"]["q"]["checks"]["exercise"]["state"], "dirty")

    def test_stop_preserves_dirty_and_does_not_claim_completion(self):
        self.begin()
        result = self.run_action("stop", reason="Need a different chapter plan")["state"]
        self.assertIsNone(self.store.active(result))
        self.assertEqual(next(iter(result["tasks"].values()))["status"], "stopped")
        self.assertEqual(result["units"]["p"]["checks"]["context"]["state"], "dirty")

    def test_all_dirty_causes_must_be_acknowledged(self):
        self.run_action("dirty", checks=["p/context"], reason="First issue")
        self.run_action("dirty", checks=["p/context"], reason="Second issue")
        ticket = self.run_action("prepare", check="p/context")["result"]
        ticket["causes"].pop()
        with self.assertRaisesRegex(ReviewError, "원인"):
            self.run_action("accept", check="p/context", ticket=ticket, evidence="done", reviewer="test")
        self.pass_check("p/context")
        self.assertEqual(len(self.store.load()["units"]["p"]["checks"]["context"]["receipt"]["resolved"]), 2)

    def test_prose_completion_does_not_clear_proof(self):
        self.run_action("dirty", checks=["p/context", "p/proof"], reason="Example edited")
        self.pass_check("p/context")
        self.assertEqual(self.store.load()["units"]["p"]["checks"]["proof"]["state"], "dirty")

    def test_accept_requires_evidence_and_reviewer(self):
        ticket = self.run_action("prepare", check="p/context")["result"]
        with self.assertRaises(ReviewError):
            self.run_action("accept", check="p/context", ticket=ticket, evidence=" ", reviewer="test")

    def test_scan_does_not_repeat_the_same_cause(self):
        self.edit()
        first = self.run_action("status")["state"]
        second = self.run_action("status")["state"]
        self.assertEqual(first, second)

    def test_protocol_change_invalidates_all_and_rejects_old_ticket(self):
        for key in ['book/structure', 'p/context', 'p/proof', 'q/exercise']:
            self.pass_check(key)
        old = self.run_action('prepare', check='p/context')['result']
        (self.root / 'REVIEW_PROCESS.md').write_text('New first-example criterion', encoding='utf-8')
        view = self.run_action('status')['state']
        self.assertEqual(view['protocol_review']['pending'], 4)
        self.assertTrue(all(c['state'] == 'dirty' for u in view['units'].values() for c in u['checks'].values()))
        self.assertTrue(view['units']['p']['checks']['context']['receipt']['evidence'])
        with self.assertRaisesRegex(ReviewError, '바뀌'):
            self.run_action('accept', check='p/context', ticket=old, evidence='old', reviewer='test')
        self.pass_check('p/context')
        self.assertEqual(self.run_action('status')['state']['protocol_review']['pending'], 3)
        for key in ['p/proof', 'q/exercise', 'book/structure']:
            self.pass_check(key)
        self.assertEqual(self.run_action('status')['state']['protocol_review']['pending'], 0)
        self.edit()
        view = self.run_action('status')['state']
        self.assertEqual(view['protocol_review']['pending'], 0)
        self.assertEqual(view['units']['p']['checks']['context']['state'], 'dirty')

    def test_protocol_deletion_and_exclusion_need_new_receipts(self):
        guide = self.root / 'STYLE.md'
        guide.write_text('Initial style', encoding='utf-8')
        self.run_action('status')
        ticket = self.run_action('prepare', check='p/proof')['result']
        self.run_action('accept', check='p/proof', ticket=ticket, verdict='not_applicable',
                        evidence='The selected prose contains no proof.', reviewer='test')
        guide.unlink()
        view = self.run_action('status')['state']
        self.assertEqual(view['units']['p']['checks']['proof']['state'], 'dirty')
        self.assertEqual(view['protocol_review']['pending'], 4)

    def test_legacy_receipt_migration_with_existing_criteria(self):
        self.pass_check('p/context')
        state = self.store.load()
        state.pop('protocol')
        state['units']['p']['checks']['context']['receipt'].pop('protocol')
        self.store.path.write_text(json.dumps(state), encoding='utf-8')
        (self.root / 'AGENTS.md').write_text('Review changed criteria.', encoding='utf-8')
        first = self.run_action('status')['state']
        self.assertEqual(first['protocol_review']['pending'], 4)
        second = self.run_action('status')['state']
        self.assertEqual(first, second)

    def test_preexisting_edits_are_preserved_in_task_baseline(self):
        self.edit()
        self.begin()
        task = self.store.active(self.store.load())
        self.assertEqual(self.store.audit(task)["changed"], [])
        self.source.write_text(self.source.read_text().replace("Revised", "Final"), encoding="utf-8")
        self.assertEqual(self.store.audit(task)["violations"], [])

    def test_task_cannot_skip_edited_checks_or_parent_boundary(self):
        self.begin()
        task = self.store.active(self.store.load())
        self.assertEqual(set(task["required"]), {"p/context", "p/proof", "book/structure"})
        with self.assertRaisesRegex(ReviewError, "미완료"):
            self.run_action("finish", boundary="No change to chapter goal")

    def test_scope_violation_in_same_file_and_no_retroactive_expansion(self):
        self.begin()
        self.source.write_text(self.source.read_text().replace("Before", "Outside edit"), encoding="utf-8")
        self.assertEqual(len(self.store.audit(self.store.active(self.store.load()))["violations"]), 1)
        with self.assertRaisesRegex(ReviewError, "수정 전에"):
            self.run_action("expand", edit_units=["q"], reason="More changes")

    def test_scope_preserves_line_endings_outside_the_selected_region(self):
        self.source.write_bytes(self.source.read_bytes().replace(b"\r\n", b"\n").replace(b"\n", b"\r\n"))
        self.begin()
        original = self.source.read_bytes()
        self.source.write_bytes(original.replace(b"Original", b"Changed"))
        self.assertEqual(self.store.audit(self.store.active(self.store.load()))["violations"], [])
        self.source.write_bytes(original.replace(b"\r\n", b"\n"))
        self.assertTrue(self.store.audit(self.store.active(self.store.load()))["violations"])

    def test_scope_violation_in_other_file_including_new_file(self):
        self.begin()
        (self.root / "new.lean").write_text("New unrelated content", encoding="utf-8")
        self.assertEqual(self.store.audit(self.store.active(self.store.load()))["violations"][0]["path"], "new.lean")

    def test_scope_can_expand_before_edit(self):
        self.begin()
        self.run_action("expand", edit_units=["q"], reason="Update downstream exercise")
        (self.root / "other.lean").write_text("Revised exercise", encoding="utf-8")
        self.assertEqual(self.store.audit(self.store.active(self.store.load()))["violations"], [])

    def test_read_context_invalidates_review_without_granting_edit_permission(self):
        self.begin()
        self.pass_check("p/context")
        (self.root / "other.lean").write_text("Changed prerequisite", encoding="utf-8")
        result = self.run_action("status")["state"]
        self.assertEqual(result["units"]["p"]["checks"]["context"]["state"], "dirty")
        self.assertTrue(self.store.active(result)["audit"]["violations"])

    def test_successful_finish_retains_receipts_and_does_not_clear_unknown(self):
        self.begin(); self.edit()
        for key in ["p/context", "p/proof", "book/structure"]:
            self.pass_check(key)
        result = self.run_action("finish", boundary="Only subject wording changed; prerequisites and conclusions are unchanged.")["state"]
        self.assertIsNone(self.store.active(result))
        self.assertEqual(result["units"]["q"]["checks"]["exercise"]["state"], "unknown")
        self.assertEqual(next(iter(result["tasks"].values()))["audit"]["changed"], ["chapter.lean"])

    def test_multiple_tabs_cannot_overwrite_state(self):
        rev = self.store.load()["revision"]
        self.run_action("dirty", checks=["p/context"], reason="First tab")
        with self.assertRaisesRegex(ReviewError, "다른 화면"):
            self.store.execute("dirty", {"checks": ["q/exercise"], "reason": "Second tab"}, rev)

    def test_missing_or_ambiguous_anchors_block_completion(self):
        self.source.write_text("BEGIN\nBEGIN\nEND\n", encoding="utf-8")
        result = self.run_action("status")["state"]
        self.assertTrue(result["units"]["p"]["errors"])
        with self.assertRaises(ReviewError):
            self.pass_check("p/context")
        self.run_action("relocate", unit="p", sources=[{"path": "chapter.lean"}], reason="Replaced old paragraph boundaries")
        self.assertEqual(self.store.load()["units"]["p"]["checks"]["context"]["state"], "dirty")

    def test_path_traversal_rejected(self):
        for path in ("../outside", "/outside", "C:/outside", ".git/config", "review/local/secret"):
            with self.subTest(path=path), self.assertRaises(ReviewError):
                self.store.source_path(path)

    def test_lock_prevents_concurrent_cli_and_web_write(self):
        self.store.local.mkdir(parents=True)
        (self.store.local / "write.lock").touch()
        with self.assertRaisesRegex(ReviewError, "저장"):
            self.run_action("status")

    def test_missing_snapshot_blocks_close_without_overwriting_files(self):
        self.begin()
        task = self.store.active(self.store.load())
        (self.store.local / (task["id"] + ".json")).unlink()
        result = self.run_action("status")["state"]
        self.assertTrue(self.store.active(result)["audit"]["violations"])

    def http(self, payload, headers=None, path="/api"):
        handler = object.__new__(ReviewHandler)
        data = json.dumps(payload).encode()
        handler.server = types.SimpleNamespace(server_port=8766, token="test-token", store=self.store)
        handler.path = path
        handler.headers = {"Host": "127.0.0.1:8766", "Origin": "http://127.0.0.1:8766", "X-Review-Token": "test-token", "Content-Length": str(len(data)), **(headers or {})}
        handler.rfile = io.BytesIO(data)
        captured = []
        handler.send = lambda *args: captured.append(args)
        handler.do_POST()
        return captured[0]

    def test_http_state_roundtrip_without_opening_a_listener(self):
        code, body = self.http({"action": "status"})
        self.assertEqual(code, 200)
        rev = body["state"]["revision"]
        code, body = self.http({"action": "dirty", "revision": rev, "args": {"checks": ["p/context"], "reason": "UI report"}})
        self.assertEqual(code, 200)
        self.assertEqual(body["state"]["units"]["p"]["checks"]["context"]["state"], "dirty")

    def test_http_requires_revision_and_rejects_foreign_requests(self):
        self.assertEqual(self.http({"action": "dirty", "args": {}})[0], 409)
        for headers in ({"Origin": "https://other.example"}, {"Host": "other.example"}, {"X-Review-Token": "bad"}):
            self.assertEqual(self.http({"action": "status"}, headers)[0], 403)
        self.assertEqual(self.http({"action": "status"}, path="/elsewhere")[0], 404)


if __name__ == "__main__":
    unittest.main(verbosity=2)
