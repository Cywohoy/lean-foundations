"""Check four reading pages, section destinations, exercises and editorial constraints."""
from pathlib import Path
import json,re
from collections import Counter
root=Path(__file__).resolve().parents[1]
site=root/"_out/html-multi"
chapters={"proof":"Proof","sets-functions":"SetsFunctions","numbers-relations":"NumbersRelations","sizes":"CardinalityChapter"}
xrefs=json.loads((site/"xref.json").read_text(encoding="utf-8"))
sections=xrefs["Verso.Genre.Manual.section"]["contents"]
addresses={item["address"] for items in sections.values() for item in items}
allowed={"/","/proof/","/sets-functions/","/numbers-relations/","/sizes/","/tactics/","/symbols/"}
assert addresses<=allowed,(addresses-allowed)
for slug,module in chapters.items():
    html=(site/slug/"index.html").read_text(encoding="utf-8")
    assert 'class="book-example"' in html,slug
    assert 'data-exercise-unit="exercises"' in html,slug
    assert "Table of Contents" in html  # The reader replaces split navigation with one tree.
    text=(root/f"AlgebraBook/{module}.lean").read_text(encoding="utf-8")
    for flags,code in re.findall(r"```savedLean([^\n]*)\n(.*?)```",text,re.S):
        if "-keep" not in flags:
            assert not re.search(r"\b(sorry|axiom)\b",re.sub(r"--[^\n]*","",code)),module
    numbers=[int(n) for n in re.findall(r"\*문제 (\d+)\*",text)]
    assert numbers==list(range(1,len(numbers)+1)),(module,numbers)
manifest=json.loads((site/"playground.json").read_text(encoding="utf-8"))
names=[n for v in manifest.values() if v.get("exercise")
       for n in re.findall(r"^theorem\s+(\w+)",v["code"],re.M)]
assert len(names)==len(set(names)),"Exercise names must remain unique"
source="\n".join((root/f"AlgebraBook/{m}.lean").read_text(encoding="utf-8") for m in chapters.values())
expected=re.findall(r"^theorem\s+(exercise_\w+)",source,re.M)
assert set(expected)<=set(names),(set(expected)-set(names))
proof=(root/"AlgebraBook/Proof.lean").read_text(encoding="utf-8")
assert proof.index("#eval 2 + 3")<proof.index("def add")<proof.index("# 명제와 술어")<proof.index("# 계산 결과의 증명")<proof.index("# 정리의 사용")
assert "identityExplicit" not in proof
sets=(root/"AlgebraBook/SetsFunctions.lean").read_text(encoding="utf-8")
assert sets.index("theorem inter_comm_forward")<sets.index("# 동치와 두 방향")
assert "def cardinality_fin_three_last" not in sets
sizes=(root/"AlgebraBook/CardinalityChapter.lean").read_text(encoding="utf-8")
relations=(root/"AlgebraBook/NumbersRelations.lean").read_text(encoding="utf-8")
assert relations.index('theorem parityClass_zero_ne_one') < relations.index('theorem exercise_parityClass_three_one'), 'The parity exercise must follow the theorem its instructions require'
assert sizes.index("def Cardinal")<sizes.index("# 유한한 번호")<sizes.index("def IsFinite")
assert sizes.index("# 자연수와 같은 크기의 집합") < sizes.index("## 가장 작은 무한기수") < sizes.index("# 멱집합과 칸토어 정리")
assert "Advanced:" not in source
assert sizes.count("# 크기 비교의 자동화")==1
appendix=(root/"AlgebraBook/Tactics.lean").read_text(encoding="utf-8")
for syntax in ["apply goal","unpack goals","cases goal","induction at","wlog at"]:
    assert syntax not in appendix
print(f"Four chapter pages, two appendices, {len(names)} named exercise statements; structure checks passed.")
