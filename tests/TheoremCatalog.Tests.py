"""Check source chronology and the signatures exported from checked Lean contexts."""
import json
import re
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from theorem_catalog import exercise_candidates

candidates = exercise_candidates()
assert len(candidates) == 148
assert {'Int.add_comm', 'Int.sub_add_cancel'} <= set(candidates['exercise_congruent_one'])
assert 'Ample.congruent_add_right' in candidates['exercise_congruent_add_left']
assert 'Ample.congruent_add_right' in candidates['exercise_nextParity_respects']
assert 'Ample.parityClass_zero_ne_one' in candidates['exercise_parityClass_three_one']
assert 'Ample.quotientLift_unique' not in candidates['exercise_parityClass_three_one']
assert 'Nat.add_lt_add_right' in candidates['exercise_add_three_preserves_lt']
assert 'Ample.fin_injective_surjective' in candidates['exercise_fin_injective_bijective']
assert 'Ample.cardinal_nat_add' in candidates['exercise_three_boxes_sum']
assert 'Ample.cardinal_nat_mul' in candidates['exercise_three_boxes_product']
assert 'Ample.cardinal_product' in candidates['exercise_cardinal_product_sum']
assert 'Ample.cardinal_arrow' in candidates['exercise_splitFunction_bijective']
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
    entries = snippet['theorems']
    assert len(entries) == len({entry['name'] for entry in entries})
    for entry in entries:
        assert entry['name'] in candidates[name], (name, entry)
        assert entry['reference'] and entry['statement'], (name, entry)
        assert ':= by' not in entry['statement'], 'The panel shows propositions, not proofs'
    if name == 'exercise_parityClass_three_one':
        assert entries[0]['name'] == 'Ample.parityClass_zero_ne_one'
        assert entries[0]['preferred']
        assert 'parityClass 0 ≠ parityClass 1' in entries[0]['statement']
    if name == 'exercise_add_three_preserves_lt':
        assert any(entry['reference'] == 'Nat.add_lt_add_right' for entry in entries)
print('PASS: taught theorem chronology, actual Lean signatures, prerequisite priority, and no exercise solutions')
