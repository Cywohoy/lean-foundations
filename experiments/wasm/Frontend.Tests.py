"""Check real cursor states with Lean 4.35 before building the browser binary."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
(ROOT / 'tmp').mkdir(parents=True, exist_ok=True)
LAKE = shutil.which('lake') or str(Path.home() / '.elan/bin' / ('lake.exe' if os.name == 'nt' else 'lake'))


def check(name, source, marker, expected, *, found=True, diagnostic=None):
    offset = source.index(marker) + len(marker)
    before = source[:offset]
    line = before.count('\n')
    character = len(before.rsplit('\n', 1)[-1].encode('utf-16-le')) // 2
    with tempfile.TemporaryDirectory(prefix='wasm-frontend-', dir=ROOT / 'tmp') as directory:
        source_path = Path(directory) / 'Probe.lean'
        source_path.write_text(source, encoding='utf-8')
        result = subprocess.run([LAKE, 'env', 'lean', '--run',
            'experiments/wasm/Frontend.lean', str(source_path), str(line), str(character)],
            cwd=ROOT, capture_output=True, encoding='utf-8', timeout=90)
        assert result.returncode == 0, (name, result.stdout, result.stderr)
        response = json.loads(result.stdout.strip().splitlines()[-1])
    assert response['state']['found'] is found, (name, response)
    goals = '\n'.join(response['state']['goals'])
    if not expected:
        assert response['state']['goals'] == [], (name, response)
    for text in expected:
        assert text in goals, (name, text, response)
    if diagnostic:
        assert any(diagnostic in entry['message'] for entry in response['diagnostics']), (name, response)
    elif found:
        assert not any(entry['severity'] == 'error' for entry in response['diagnostics']), (name, response)
    print(f'PASS: {name}')


check('before first tactic', 'theorem t (P : Prop) : P → P := by\n  intro hp\n  exact hp\n',
      ':= by\n  ', ['⊢ P → P'])
check('after intro', 'theorem t (P : Prop) : P → P := by\n  intro hp\n  exact hp\n',
      'intro hp', ['hp : P', '⊢ P'])
check('after exact', 'theorem t (P : Prop) : P → P := by\n  intro hp\n  exact hp\n',
      'exact hp', [])
check('empty proof', 'theorem t (P : Prop) : P → P := by\n  ',
      ':= by\n  ', ['⊢ P → P'], diagnostic='unsolved goals')
check('placeholder is reported', 'theorem t (P : Prop) : P → P := by\n  sorry\n',
      'sorry', [], diagnostic='declaration uses `sorry`')
check('module header', 'module\nimport Lean\nexample (P : Prop) : P → P := by\n  intro hp\n  exact hp\n',
      'intro hp', ['hp : P', '⊢ P'])
check('Unicode UTF-16 position', 'theorem t (P : Prop) : P → P := by\n  intro «증명😀»\n  exact «증명😀»\n',
      'intro «증명😀»', ['증명😀', '⊢ P'])
check('Ample automatic normalization', 'import Ample\nopen Ample\nopen scoped Ample.Auto\n'
      'example (n : Int) (h : ¬ n < 0) : 0 ≤ n := by\n  exact h\n',
      ':= by\n  ', ['h : 0 ≤ n', '⊢ 0 ≤ n'])
check('Ample ext subgoals', 'import Ample\nopen Ample\n'
      'example (x y : Nat × Nat) (h : x.1 = y.1 ∧ x.2 = y.2) : x = y := by\n'
      '  ext with first second\n  case first => exact h.left\n  case second => exact h.right\n',
      'ext with first second', ['⊢ x.fst = y.fst', '⊢ x.snd = y.snd'])
check('error remains visible', 'example : 2 + 2 = 5 := by\n  rfl\n',
      'rfl', ['⊢ 2 + 2 = 5'], diagnostic='failed')
check('unknown tactic parser error', 'example (P : Prop) : P → P := by\n  nonsense\n',
      'nonsense', ['⊢ P → P'], diagnostic='unknown tactic')
check('two unknown tactics retain parser diagnostics',
      'example (P : Prop) : P → P := by\n  nonsense\n  nonsense\n',
      'nonsense\n  nonsense', [], found=False, diagnostic='unknown tactic')
