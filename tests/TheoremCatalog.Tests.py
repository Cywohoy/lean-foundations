"""Check source chronology and the signatures exported from checked Lean contexts."""
import json
import re
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from theorem_catalog import chapter_names, declaration_positions, exercise_candidates, signature_body

assert signature_body({'name': 'Sample.ready', 'declaration': 'Sample.ready : True'}) == ': True'
assert signature_body({'name': 'Sample.id',
    'declaration': 'Sample.id.{u_1, u_2}\n {A : Type u_1} {B : Type u_2} (f : A → B) : A → B'}) == \
    '{A : Type u_1} {B : Type u_2} (f : A → B) : A → B'
assert signature_body({'name': 'Sample.ready', 'statement': 'True'}) == 'True', \
    'A type-only fallback must not lose its first token'
try:
    signature_body({'name': 'Sample.ready', 'declaration': 'Sample.readyElse : True'})
    raise AssertionError('A different name must not be stripped as a prefix')
except ValueError:
    pass

candidates = exercise_candidates()
positions = declaration_positions()
assert len(candidates) == 154
functions, function_names = chapter_names('SetsFunctions')
assert functions.index('theorem identity_inj_and_surj') < functions.index('structure Bijective') < functions.index('theorem identity_bijective')
assert 'Ample.identity_inj_and_surj' in candidates['exercise_injective_of_compose']
# Generated projections are taught on the hypothesis, not listed as earlier
# standalone theorems left over from the former conjunction wrappers.
assert 'Ample.Bijective.inj' not in candidates['exercise_injective_of_compose']
assert {'Int.add_comm', 'Int.sub_add_cancel'} <= set(candidates['exercise_congruent_one'])
assert 'Ample.congruent_add_right' in candidates['exercise_congruent_add_left']
assert 'Ample.congruent_add_right' in candidates['exercise_nextParity_respects']
assert 'Ample.parityClass_zero_ne_one' in candidates['exercise_parityClass_three_one']
assert 'Ample.quotientLift_unique' not in candidates['exercise_parityClass_three_one']
assert 'Nat.add_lt_add_right' in candidates['exercise_add_three_preserves_lt']
assert 'ProofExamples.not_imp_iff' in candidates['exercise_exists_forall_swap']
assert 'ProofExamples.not_forall_iff' in candidates['exercise_forall_implication']
assert 'ProofExamples.equality_iff_all_predicates' not in candidates['exercise_forall_implication']
assert 'Ample.fin_injective_surjective' in candidates['exercise_fin_injective_bijective']
assert 'Ample.cardinal_nat_add' in candidates['exercise_three_boxes_sum']
assert 'Ample.cardinal_nat_mul' in candidates['exercise_three_boxes_product']
assert 'Ample.cardinal_product' in candidates['exercise_cardinal_product_sum']
assert 'Ample.cardinal_arrow' in candidates['exercise_splitFunction_bijective']
sizes, size_names = chapter_names('CardinalityChapter')
for name, output in [('cardinal_product', 'cardinalProductType'),
                     ('cardinal_arrow', 'cardinalArrowType')]:
    introduction = next(position for position, full in size_names if full == 'Ample.' + name)
    assert introduction >= sizes.index('```leanOutput ' + output), 'A hidden proof alone does not introduce its result'
assert 'Ample.cardinal_set' in candidates['exercise_three_powerSet']
assert 'Ample.cardinal_nat_pow' not in candidates['exercise_two_to_three_functions']
assert 'Ample.sameBlock_class' in candidates['exercise_overlapping_not_partition']
assert all(not name.rsplit('.', 1)[-1].startswith('exercise_')
           for names in candidates.values() for name in names)

manifest = json.loads((ROOT / '_out/pages/foundations/playground.json').read_text(encoding='utf-8'))
for snippet in manifest.values():
    if not snippet.get('exercise'):
        continue
    name = re.search(r'^theorem\s+(exercise_\w+)\b', snippet['code'], re.M)[1]
    names = re.findall(r'^theorem\s+(exercise_\w+)\b', snippet['code'], re.M)
    assert snippet['theoremOrder'] == {name: positions[name] for name in names}
    assert snippet['preferredTheorems'] == sorted(set(snippet['preferredTheorems']))
    entries = snippet['theorems']
    assert len(entries) == len({entry['name'] for entry in entries})
    for entry in entries:
        assert entry['name'] in candidates[name], (name, entry)
        assert entry['order'] == positions[entry['name']]
        assert entry['order'] < min(snippet['theoremOrder'].values()), 'Only earlier introductions enter the catalog'
        assert entry['reference'] and entry['statement'], (name, entry)
        assert ':= by' not in entry['statement'], 'The panel shows propositions, not proofs'
        assert re.match(r'^(?:\(|\{|⦃|:)', entry['declaration']), (name, entry)
        assert not re.match(r'^u_\d+\}', entry['declaration']), 'No partial universe list may remain'
    if name == 'exercise_parityClass_three_one':
        assert entries[0]['name'] == 'Ample.parityClass_zero_ne_one'
        assert entries[0]['preferred']
        assert 'parityClass 0 ≠ parityClass 1' in entries[0]['statement']
    if name == 'exercise_add_three_preserves_lt':
        assert any(entry['reference'] == 'Nat.add_lt_add_right' for entry in entries)
print('PASS: taught theorem chronology, actual Lean signatures, prerequisite priority, and no exercise solutions')
