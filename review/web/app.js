/* The server owns state transitions. This UI never edits manuscript files. */
"use strict";
const $ = id => document.getElementById(id);
const labels = {dirty: "재검토 필요", unknown: "검토 전", clean: "검토 완료", not_applicable: "해당 없음"};
const levels = {book: "책", chapter: "장", section: "절", explanation: "설명 단위", paragraph: "문단", sentence: "문장", exercise: "문제", code: "코드"};
let state, selected, submitAction, loading = false, selectionSerial = 0;

function el(tag, text, attrs = {}) {
  const node = document.createElement(tag);
  if (text !== undefined && text !== null) node.textContent = text;
  for (const [key, value] of Object.entries(attrs)) node.setAttribute(key, value);
  return node;
}
function button(text, action, cls = "") {
  const node = el("button", text, {type: "button", class: cls});
  node.addEventListener("click", () => Promise.resolve().then(action).catch(showError));
  return node;
}
function showError(error) {
  $("notice").hidden = false;
  $("notice").textContent = error.message || String(error);
}
async function api(action, args = {}) {
  const response = await fetch("/api", {method: "POST", headers: {"Content-Type": "application/json", "X-Review-Token": document.querySelector('meta[name="review-token"]').content},
    body: JSON.stringify({action, args, revision: ["status", "scan", "source", "prepare"].includes(action) ? undefined : state?.revision})});
  const result = await response.json();
  if (!response.ok) throw new Error(result.error || "요청을 처리하지 못했습니다.");
  if (!state || result.state.revision >= state.revision) state = result.state;
  return result.result;
}
function activeTask() { return Object.values(state.tasks).find(t => t.status === "open"); }
function checkName(key) {
  const [unit, aspect] = key.split("/");
  return `${state.units[unit].title} · ${state.check_labels[aspect]}`;
}
function ownCounts(unit) {
  return Object.values(unit.checks).reduce((a, c) => { a[c.state]++; return a; }, {dirty: 0, unknown: 0, clean: 0, not_applicable: 0});
}
function renderTree() {
  const protocol = state.protocol_review;
  $("protocol-notice").hidden = !protocol?.pending;
  $("protocol-notice").textContent = protocol?.pending
    ? `검토 기준 변경 · 새 기준 확인 ${protocol.pending}/${protocol.total}개 남음 · ${protocol.changed_at.slice(0, 16).replace("T", " ")} UTC`
    : "";
  const search = $("search").value.trim().toLowerCase(), filter = $("filter").value;
  function branch(parent) {
    const list = el("ul");
    for (const [id, unit] of Object.entries(state.units).filter(([, u]) => u.parent === parent)) {
      const child = branch(id), counts = ownCounts(unit);
      const matches = (!search || unit.title.toLowerCase().includes(search)) && (filter === "all" || counts[filter]);
      if (!matches && !child.childElementCount) continue;
      const item = el("li"), link = el("a", null, {href: `#${encodeURIComponent(id)}`});
      if (id === selected) link.setAttribute("aria-current", "page");
      link.append(el("span", unit.title, {class: "tree-label"}));
      const dirty = counts.dirty + unit.descendants.dirty;
      if (dirty) link.append(el("small", `${dirty}`, {title: "자체 및 하위의 재검토 항목 수"}));
      item.append(link, child); list.append(item);
    }
    return list;
  }
  $("tree").replaceChildren(branch(null));
  const all = Object.values(state.units).flatMap(u => Object.values(u.checks));
  $("summary").textContent = `재검토 ${all.filter(c => c.state === "dirty").length} · 검토 전 ${all.filter(c => c.state === "unknown").length} · 완료 ${all.filter(c => c.state === "clean").length} · 해당 없음 ${all.filter(c => c.state === "not_applicable").length}`;
  $("task-button").textContent = activeTask() ? "진행 중인 수정 작업" : "수정 작업 시작";
}
async function renderDetail() {
  const serial = ++selectionSerial, unit = state.units[selected];
  if (!unit) return;
  const main = $("detail"); main.replaceChildren();
  const crumbs = []; let u = unit;
  while (u) { crumbs.unshift(u.title); u = state.units[u.parent]; }
  main.append(el("p", `${levels[unit.level]} · ${crumbs.slice(0, -1).join(" / ") || "전체 구성"}`, {class: "eyebrow"}), el("h1", unit.title));
  if (unit.contains_dirty || unit.descendants.unknown) {
    main.append(el("p", `하위 범위: 재검토 ${unit.descendants.dirty}, 검토 전 ${unit.descendants.unknown}. 아래 항목은 이 범위 자체의 검토 상태입니다.`, {class: "context-note"}));
  }
  const task = activeTask();
  if (task) {
    const box = el("div", null, {class: "task-summary"});
    box.append(el("strong", task.title), el("p", `수정 범위 ${task.edit_scope.length}곳 · 완료에 필요한 검토 ${task.required.length}개`));
    if (task.audit.violations.length) box.append(el("p", `허용 범위 밖의 변경 ${task.audit.violations.length}건`, {class: "violation"}));
    box.append(button("작업 범위 확인", taskDialog)); main.append(box);
  }
  const checks = el("div", null, {class: "checks"});
  for (const [aspect, check] of Object.entries(unit.checks)) {
    const key = `${selected}/${aspect}`, row = el("section", null, {class: "check"}), top = el("div", null, {class: "check-top"});
    top.append(el("h3", state.check_labels[aspect]), el("span", labels[check.state], {class: `status ${check.state}`}));
    const actions = el("div", null, {class: "actions"});
    actions.append(button(check.state === "clean" ? "다시 검토" : "검토 시작", () => reviewDialog(key)), button("문제 기록", () => dirtyDialog(key)));
    top.append(actions); row.append(top);
    if (check.causes.length) {
      const reasons = el("ul", null, {class: "reasons"});
      for (const cause of check.causes) reasons.append(el("li", `${cause.reason} · ${cause.at.slice(0, 16).replace("T", " ")} UTC`));
      row.append(reasons);
    }
    if (check.receipt) row.append(el("p", `${["clean", "not_applicable"].includes(check.state) ? "판정 근거" : "이전 검토"}: ${check.receipt.evidence}\n${check.receipt.reviewer} · ${check.receipt.at}`, {class: "evidence"}));
    checks.append(row);
  }
  main.append(checks);
  if (unit.errors.length) main.append(el("p", unit.errors.join(" / "), {class: "violation"}));
  if (unit.sources.length) {
    const head = el("div", null, {class: "source-head"});
    head.append(el("h2", "검토할 내용"), button("경계 수정", relocateDialog), button("이 범위에서 수정 작업", () => beginDialog())); main.append(head);
    const sourceContainer = el("div", "내용을 불러오는 중"); main.append(sourceContainer);
    try {
      const sources = await api("source", {unit: selected});
      if (serial !== selectionSerial) return;
      sourceContainer.replaceChildren();
      for (const source of sources) sourceContainer.append(el("p", source.selector.path, {class: "path"}), el("pre", source.text, {class: "source", tabindex: "0"}));
    } catch (error) { sourceContainer.replaceChildren(el("p", error.message, {class: "violation"})); }
  }
  const depsHead = el("div", null, {class: "section-head"});
  depsHead.append(el("h2", "검토 의존 관계"), button("연결", linkDialog)); main.append(depsHead);
  const edges = state.dependencies.filter(d => d.from.startsWith(selected + "/") || d.to.startsWith(selected + "/"));
  const deps = el("ul", null, {class: "dependencies"});
  for (const d of edges) {
    const item = el("li", `${checkName(d.from)} → ${checkName(d.to)}: ${d.reason} `);
    item.append(button("연결 해제", () => openDialog("의존 관계 해제", [el("p", `${checkName(d.from)} → ${checkName(d.to)}`), field("해제 이유", "reason", "", "textarea")], data => api("unlink", {from: d.from, to: d.to, reason: data.get("reason")}))));
    deps.append(item);
  }
  main.append(edges.length ? deps : el("p", "등록된 의존 관계가 없습니다. 새로운 내용의 사용처는 검토자가 연결해야 합니다.", {class: "empty"}));
  main.append(el("h2", "최근 기록"));
  const events = state.history.filter(h => h.unit === selected || h.check?.startsWith(selected + "/") || h.checks?.some(k => k.startsWith(selected + "/"))).slice(-8).reverse();
  const history = el("ul", null, {class: "history"});
  const eventNames = {register: "범위 등록", accept: "검토 완료", invalidate: "재검토 등록"};
  for (const event of events) history.append(el("li", `${event.at} · ${eventNames[event.action] || event.action}${event.cause ? " · " + event.cause.reason : ""}`));
  main.append(events.length ? history : el("p", "아직 기록이 없습니다.", {class: "empty"}));
}
async function render() { renderTree(); await renderDetail(); }
async function refresh() {
  if (loading) return;
  loading = true; $("scan").disabled = true;
  try {
    await api("status");
    const hash = decodeURIComponent(location.hash.slice(1));
    selected = state.units[hash] ? hash : selected && state.units[selected] ? selected : Object.keys(state.units)[0];
    await render(); $("notice").hidden = true;
  } catch (error) { showError(error); }
  finally { loading = false; $("scan").disabled = false; }
}
function field(label, name, value = "", type = "text") {
  const wrap = el("label", label, {class: "field"});
  const input = el(type === "textarea" ? "textarea" : "input", null, {name, required: ""});
  if (type !== "textarea") input.type = type;
  input.value = value; wrap.append(input); return wrap;
}
function selectField(label, name, entries, chosen, multiple = false) {
  const wrap = el("label", label, {class: "field"}), select = el("select", null, {name});
  if (multiple) { select.multiple = true; select.size = Math.min(7, entries.length); }
  for (const [key, title] of entries) {
    const option = el("option", title, {value: key}); option.selected = multiple ? chosen.includes(key) : key === chosen; select.append(option);
  }
  wrap.append(select); return wrap;
}
function allChecks() {
  return Object.entries(state.units).flatMap(([id, unit]) => Object.keys(unit.checks).map(a => [`${id}/${a}`, `${unit.title} · ${state.check_labels[a]}`]));
}
function sourceUnits() { return Object.entries(state.units).filter(([, u]) => u.sources.length).map(([id, u]) => [id, u.title]); }
function openDialog(title, nodes, onSubmit, submitLabel = "저장") {
  $("dialog-title").textContent = title; $("dialog-body").replaceChildren(...nodes); $("form-error").hidden = true;
  $("submit-dialog").textContent = submitLabel; submitAction = onSubmit;
  if (!$("dialog").open) $("dialog").showModal();
}
async function reviewDialog(key) {
  const ticket = await api("prepare", {check: key}), c = state.units[key.split("/")[0]].checks[key.split("/")[1]];
  const causes = el("ul", null, {class: "ticket-causes"});
  for (const cause of c.causes) causes.append(el("li", cause.reason));
  openDialog(checkName(key), [el("p", "내용과 앞뒤 맥락을 확인한 뒤 근거를 기록하세요. 아래 변경 원인을 모두 확인한 현재 버전에만 완료 기록이 남습니다."), causes,
    selectField("판정", "verdict", [["clean", "검토 완료"], ["not_applicable", "해당 없음 (이유 필요)"]], "clean"),
    field("검토 근거 — 확인한 내용, 결과, 필요하면 기록·검사 경로", "evidence", "", "textarea"), field("검토자", "reviewer", localStorage.getItem("review-reviewer") || "")], async data => {
    await api("accept", {check: key, ticket, evidence: data.get("evidence"), reviewer: data.get("reviewer"), verdict: data.get("verdict")});
    localStorage.setItem("review-reviewer", data.get("reviewer"));
  }, "검토 완료 기록");
}
function dirtyDialog(key) {
  openDialog("재검토가 필요한 이유", [el("p", checkName(key)), field("문제와 확인할 내용", "reason", "", "textarea")], data => api("dirty", {checks: [key], reason: data.get("reason")}));
}
function linkDialog() {
  const entries = allChecks(), first = entries.find(([key]) => key.startsWith(selected + "/"))?.[0];
  openDialog("검토 의존 관계", [el("p", "앞 항목이 변경되면 뒤 항목도 재검토 상태가 됩니다. 내용이나 검토 자체가 의존하는 경우에만 연결하세요."), selectField("먼저 확인할 항목", "from", entries, first), selectField("그 결과에 의존하는 항목", "to", entries, first), field("의존 이유", "reason")], data => api("link", Object.fromEntries(data)));
}
function beginDialog() {
  if (activeTask()) return taskDialog();
  const selectedChecks = Object.keys(state.units[selected].checks).map(a => `${selected}/${a}`);
  const parent = state.units[selected].parent;
  if (parent && state.units[parent].checks.structure) selectedChecks.push(`${parent}/structure`);
  openDialog("수정 작업 시작", [field("작업 이름", "title"), field("수정 목적과 허용할 변경", "reason", "", "textarea"),
    selectField("수정 허용 범위 (여러 항목 선택 가능)", "edit_units", sourceUnits(), [selected], true),
    selectField("함께 읽을 범위", "read_units", sourceUnits(), [], true),
    selectField("완료에 필요한 검토", "required", allChecks(), selectedChecks, true),
    field("유지할 조건", "invariants", "", "textarea")], data => api("begin", {title: data.get("title"), reason: data.get("reason"), invariants: data.get("invariants"), edit_units: data.getAll("edit_units"), read_units: data.getAll("read_units"), required: data.getAll("required")}), "시작 기준 저장");
}
function scopeText(x) { return x.path + (x.after || x.before ? ` [${x.after || "파일 시작"} … ${x.before || "파일 끝"}]` : " [파일 전체]"); }
function taskDialog() {
  const task = activeTask(); if (!task) return beginDialog();
  const nodes = [el("p", task.reason), el("h3", "유지할 조건"), el("p", task.invariants), el("h3", "수정 허용 범위")];
  for (const source of task.edit_scope) nodes.push(el("p", scopeText(source), {class: "path"}));
  nodes.push(button("범위 확대", () => expandDialog()));
  nodes.push(el("h3", "함께 읽을 범위"));
  for (const source of task.read_scope) nodes.push(el("p", scopeText(source), {class: "path"}));
  if (!task.read_scope.length) nodes.push(el("p", "별도 참조 범위가 지정되지 않았습니다."));
  nodes.push(el("h3", "완료에 필요한 검토"));
  for (const key of task.required) {
    const [uid, aspect] = key.split("/"); nodes.push(el("p", `${checkName(key)} — ${labels[state.units[uid].checks[aspect].state]}`));
  }
  nodes.push(el("h3", "변경 범위 확인"));
  nodes.push(el("p", `시작 이후 변경된 파일 ${task.audit.changed.length}개`));
  for (const v of task.audit.violations) nodes.push(el("p", `${v.path}: ${v.reason}`, {class: "violation"}));
  nodes.push(button("미완료로 중단", () => openDialog("수정 작업 중단", [el("p", "완료로 기록하지 않고 작업을 중단합니다. 재검토 항목과 변경 내역은 그대로 남습니다."), field("중단 이유", "reason", "", "textarea")], data => api("stop", {reason: data.get("reason")}), "미완료로 중단")));
  nodes.push(field("상위 범위에서 검토를 멈추는 근거와 유지 조건 확인", "boundary", "", "textarea"));
  openDialog(task.title, nodes, data => api("finish", {boundary: data.get("boundary")}), "작업 완료");
}
function expandDialog() {
  openDialog("수정 범위 확대", [el("p", "추가 범위를 수정하기 전에 기록하세요. 범위 밖의 변경이 이미 있으면 확대할 수 없습니다."), selectField("추가할 범위", "edit_units", sourceUnits(), [selected], true), field("확대 이유", "reason", "", "textarea")], data => api("expand", {edit_units: data.getAll("edit_units"), reason: data.get("reason")}));
}
function addUnitDialog() {
  const path = state.units[selected]?.sources[0]?.path || "";
  const checks = el("fieldset"); checks.append(el("legend", "검토 항목"));
  for (const [key, title] of Object.entries(state.check_labels)) {
    const wrap = el("label", null, {class: "check-option"}), input = el("input", null, {type: "checkbox", name: "checks", value: key});
    input.checked = ["context", "content"].includes(key); wrap.append(input, document.createTextNode(title)); checks.append(wrap);
  }
  const after = field("시작 경계 문구 (이 문구 다음부터)", "after", "", "textarea"); after.querySelector("textarea").required = false;
  const before = field("끝 경계 문구 (이 문구 전까지)", "before", "", "textarea"); before.querySelector("textarea").required = false;
  const file = field("파일 경로 (구성만 관리하는 범위라면 비워 둠)", "path", path); file.querySelector("input").required = false;
  openDialog("검토 범위 추가", [field("이름", "title"), field("ID (영문·숫자·하이픈)", "id"),
    selectField("상위 범위", "parent", [["", "없음"], ...Object.entries(state.units).map(([id, u]) => [id, u.title])], selected),
    selectField("층위", "level", Object.entries(levels), "explanation"), file, after, before,
    el("p", "경계 문구는 파일에서 한 번만 나타나야 합니다. 둘 다 비우면 파일 전체가 선택됩니다. 경계 문구 자체를 바꾸려면 바깥 범위를 먼저 지정하세요."), checks], data => {
    const source = {path: data.get("path").trim(), after: data.get("after"), before: data.get("before")};
    return api("register", {id: data.get("id"), title: data.get("title"), parent: data.get("parent"), level: data.get("level"), sources: source.path ? [source] : [], checks: data.getAll("checks")});
  });
}
function relocateDialog() {
  const unit = state.units[selected];
  const sources = field("파일과 경계 (JSON)", "sources", JSON.stringify(unit.sources, null, 2), "textarea");
  openDialog("범위 경계 수정", [el("p", "문단이 이동하거나 경계 문구가 바뀐 경우 새 위치를 지정하세요. 이 범위와 의존 항목은 다시 검토해야 합니다. 진행 중인 작업의 수정 허용 범위는 바뀌지 않습니다."), sources, field("경계를 바꾸는 이유", "reason", "", "textarea")], data => api("relocate", {unit: selected, sources: JSON.parse(data.get("sources")), reason: data.get("reason")}));
}
$("dialog-form").addEventListener("submit", async event => {
  event.preventDefault(); $("submit-dialog").disabled = true; $("form-error").hidden = true;
  try { await submitAction(new FormData(event.target)); $("dialog").close(); await render(); }
  catch (error) {
    $("form-error").textContent = error.message; $("form-error").hidden = false;
    // Refresh shared state without discarding typed evidence or replacing its old ticket.
    try { await api("status"); renderTree(); } catch (_) { /* Keep the original error visible. */ }
  } finally { $("submit-dialog").disabled = false; }
});
$("close-dialog").onclick = $("cancel-dialog").onclick = () => $("dialog").close();
$("scan").onclick = refresh;
$("task-button").onclick = () => state && taskDialog();
$("add-unit").onclick = () => state && addUnitDialog();
$("search").oninput = $("filter").onchange = () => state && renderTree();
window.addEventListener("hashchange", async () => { const id = decodeURIComponent(location.hash.slice(1)); if (state?.units[id]) { selected = id; await render(); } });
window.addEventListener("focus", () => { if (!$("dialog").open) refresh(); });
refresh();
