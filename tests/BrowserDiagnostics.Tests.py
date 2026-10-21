"""Check the browser frontend's nested diagnostics with native Lean first."""
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
frontend = (ROOT / 'web/lean/BrowserFrontend.lean').read_text(encoding='utf-8')
runner = frontend + '''
def main (args : List String) : IO Unit := do
  let source ← IO.FS.readFile args.head!
  let document ← AmpleBrowser.elaborate source "<test>"
  IO.println (← AmpleBrowser.diagnostics document).compress
'''
cases = [
    ('missing theorem inside the learning guard',
     (ROOT / 'web/lean/LearningGuard.lean').read_text(encoding='utf-8')
     + '\nexample : True := by learning_guard "have,exact" in\n  have h := parityClass_zero_ne_one\n  exact True.intro\n',
     'Unknown identifier `parityClass_zero_ne_one`'),
    ('missing theorem with automatic normalization',
     'import Ample.Tactic.Auto\nopen scoped Ample.Auto\nexample : True := by\n  have h := parityClass_zero_ne_one\n  exact True.intro\n',
     'Unknown identifier `parityClass_zero_ne_one`'),
    ('missing theorem in have',
     'example : True := by\n  have h := parityClass_zero_ne_one\n  exact True.intro\n',
     'Unknown identifier `parityClass_zero_ne_one`'),
    ('wrong proof value in have',
     'example : True := by\n  have h : False := True.intro\n  exact True.intro\n',
     'True.intro'),
    ('failed nested proof',
     'example : True := by\n  have h : 1 = 2 := by\n    rfl\n  exact True.intro\n',
     'failed'),
    ('nested successful proof',
     'example : True := by\n  have h : True := by\n    exact True.intro\n  exact h\n',
     None),
]
(ROOT / 'tmp').mkdir(exist_ok=True)
with tempfile.TemporaryDirectory(prefix='diagnostics-', dir=ROOT / 'tmp') as directory:
    runner_path = Path(directory) / 'FrontendProbe.lean'
    runner_path.write_text(runner, encoding='utf-8')
    source_path = Path(directory) / 'Input.lean'
    for name, source, expected in cases:
        source_path.write_text(source, encoding='utf-8')
        result = subprocess.run(['lake', 'env', 'lean', '--run', str(runner_path), str(source_path)],
                                cwd=ROOT, capture_output=True, text=True, encoding='utf-8', timeout=90)
        assert result.returncode == 0, (name, result.stdout, result.stderr)
        diagnostics = json.loads(result.stdout.strip().splitlines()[-1])
        errors = [item for item in diagnostics if item['severity'] == 'error']
        if expected:
            matching = [item for item in errors if expected in item['message']]
            assert len(matching) == 1, (name, diagnostics)
        else:
            assert not errors, (name, diagnostics)
        print('PASS:', name)
