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
assert proof.index("#eval 2 + 3") < proof.index("## 명제\n") < proof.index("## 계산 결과의 증명") < proof.index("# 함의")
assert proof.index('# 부정과 고전논리') < proof.index('theorem not_or_iff') < proof.index('# 술어와 양화사')
assert proof.index('# 술어와 양화사') < proof.index('def add') < proof.index('def positive') < proof.index('## 전칭명제\n')
assert proof.index('## 존재명제') < proof.index('theorem not_forall_iff') < proof.index('# 등식\n')
assert proof.index('# 등식\n') < proof.index('∀ F : A → Prop') < proof.index('theorem predicate_ext')
assert 'Nat → Prop' not in proof[:proof.index('# 술어와 양화사')]
assert proof.index('theorem exercise_four_square') < proof.index('# 함의')
assert proof.index('def solvesSquare') < proof.index('theorem exercise_four_solves_square')
assert "identityExplicit" not in proof
sets=(root/"AlgebraBook/SetsFunctions.lean").read_text(encoding="utf-8")
assert proof.index('tag := "logic-equivalence"') < proof.index('tag := "logic-quantifier-order"')
assert '# 논리식의 변형' not in proof
assert proof.index('theorem double_negation_elim') < proof.index('theorem implication_of_contrapositive') < proof.index('theorem not_forall_iff')
assert proof.index('theorem not_imp_iff') < proof.index('theorem exists_counterexample') < proof.index('theorem predicate_ext')
assert 'theorem not_forall_iff' not in sets and 'by_contra' not in sets[:sets.index('# 상과 역상')]
assert [len(re.findall(r'^# ', (root/f"AlgebraBook/{m}.lean").read_text(encoding="utf-8"), re.M)) for m in chapters.values()] == [6,7,6,7]
assert 'ProofExamples.predicate_ext' in sets and 'ProofExamples.exists_counterexample' in sets
assert sets.index('def preimage') < sets.index('theorem preimage_indexedUnion')
assert sets.index('theorem identity_inj_and_surj') < sets.index('structure Bijective') < sets.index('theorem identity_bijective') < sets.index('def compose') < sets.index('def Elem')
assert "def cardinality_fin_three_last" not in sets
sizes=(root/"AlgebraBook/CardinalityChapter.lean").read_text(encoding="utf-8")
assert sizes.index('theorem finite_cardinal_unique') < sizes.index('def cardinalityData') < sizes.index('def cardinality (')
assert sizes.index('theorem fin_injective_le') < sizes.index('theorem finite_injective_iff_surjective')
assert sizes.index('theorem finite_injective_iff_surjective') < sizes.index('namespace Cardinal\n\nnoncomputable def add')
assert sizes.index('theorem cardinal_nat_add') < sizes.index('theorem cardinal_fin_arrow') < sizes.index('theorem cardinal_set')
assert not any(name in sizes for name in ['Σ', 'cardinal_finiteSigma', 'cardinal_finitePi', 'Nat → Type'])
assert sets.index('def productMap') < sets.index('theorem productMap_bijective')
assert 'def productMap' not in sizes
relations=(root/"AlgebraBook/NumbersRelations.lean").read_text(encoding="utf-8")
assert relations.index('theorem parityClass_zero_ne_one') < relations.index('theorem exercise_parityClass_three_one'), 'The parity exercise must follow the theorem its instructions require'
assert sizes.index("def Cardinal") < sizes.index("## 유한한 번호") < sizes.index("def IsFinite")
assert sizes.index('def CardinalityLE') < sizes.index('def IsInfinite') < sizes.index('def IsCountablyInfinite')
assert sizes.index('theorem cantor_not_surjective') < sizes.index('def characteristic') < sizes.index('theorem cardinal_set')
deletion_steps = ['def eraseIndex', 'theorem eraseIndex_lt', 'theorem eraseIndex_injective',
                  'theorem fin_injection_remove', 'theorem fin_injective_le',
                  'theorem finite_cardinal_unique', 'theorem fin_injective_surjective']
assert [sizes.index(s) for s in deletion_steps] == sorted(sizes.index(s) for s in deletion_steps)
for flags,code in re.findall(r'```savedLean([^\n]*)\n(.*?)```', sizes, re.S):
    if any(re.search(r'^' + re.escape(step) + r'\b', code, re.M) for step in deletion_steps):
        assert '-show' not in flags, 'The finite counting proof must expose the mathematical steps it uses'
assert sizes.index('def finSum') < sizes.index('def finProduct') < sizes.index('noncomputable def add')
assert 'binaryData' not in sizes
shown_sizes = '\n'.join(code for flags, code in re.findall(
    r'```savedLean([^\n]*)\n(.*?)```', sizes, re.S)
    if '-show' not in flags.split() and '-keep' not in flags.split())
for operation in ['add', 'mul', 'power']:
    declaration = re.search(r'noncomputable def ' + operation + r'\b.*?(?=\n(?:noncomputable|theorem|end)\b|\Z)', shown_sizes, re.S)
    assert declaration and 'quotientLift' in declaration[0], f'{operation}: show its quotient-lift construction'
# A checked output may expose a theorem's type while its repetitive proof stays
# in complete hidden code. An unshown #check by itself is not a visible rule.
named_checks = dict(re.findall(
    r'```lean[^\n]*\(name := (\w+)\)[^\n]*\n(?:set_option format\.width \d+ in\n)?#check (\w+)\n```', sizes))
shown_outputs = {name: code for name, code in re.findall(
    r'```leanOutput (\w+)\n(.*?)```', sizes, re.S)}
def visible_rule(name):
    if re.search(r'^theorem ' + name + r'\b', shown_sizes, re.M):
        return True
    return any(result == name and re.search(r'^Ample\.' + name + r'\b', shown_outputs.get(output, ''), re.M)
               for output, result in named_checks.items())
for result in ['cardinal_sum', 'cardinal_product', 'cardinal_arrow',
               'sameCardinality_product', 'sameCardinality_arrow']:
    assert visible_rule(result), f'{result}: keep its hypotheses and conclusion visible'
assert 'apply cardinal_eq_of_sameCardinality' not in shown_sizes
assert 'apply sameCardinality_of_cardinal_eq' not in shown_sizes
assert sizes.index('theorem cardinal_empty_fin_arrow') < sizes.index('theorem cardinal_fin_arrow')
assert sizes.index('Fin.lastCases 7') < sizes.index('def finFunctionAppend')
for problem, notation in [('sum', '∑'), ('product', '∏')]:
    statement = re.search(r'theorem exercise_three_boxes_' + problem + r'\b.*?:= by', sizes, re.S)
    assert statement and notation in statement[0], 'Connect the three-box exercise to finite arithmetic'
assert sets.index('대괄호에 정의·정리·가정') < sets.index('theorem sumMap_bijective')
assert "Advanced:" not in source
assert sizes.count("# 크기 비교의 자동화")==1
appendix=(root/"AlgebraBook/Tactics.lean").read_text(encoding="utf-8")
assert not re.search(r'\bindisc!?\b', source + appendix), 'Use explicit function application or a named comparison theorem'
assert proof.index('"logic-applying-functions"') < proof.index('## 모든 술어에 대한 양화')
assert '유한한 집합족의 합과 곱에서' not in appendix
assert 'simp only' not in appendix
for syntax in ["apply goal","unpack goals","cases goal","induction at","wlog at"]:
    assert syntax not in appendix
print(f"Four chapter pages, two appendices, {len(names)} named exercise statements; structure checks passed.")
