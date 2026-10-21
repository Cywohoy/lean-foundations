"""Resolve the taught tactic vocabulary at each exercise's current source position."""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def exercise_policies():
    stages = json.loads((ROOT / 'web/learning-tactics.json').read_text(encoding='utf-8'))
    learned, policies = set(), {}
    for chapter, entries in stages.items():
        source = (ROOT / f'AlgebraBook/{chapter}.lean').read_text(encoding='utf-8')
        events = []
        for tag, tactics in entries:
            markers = [f'tag := "{tag}"', f'{{anchor "{tag}"}}[]']
            positions = [source.index(marker) for marker in markers if marker in source]
            if not positions:
                raise ValueError(f'Tactic introduction is missing: {chapter}/{tag}')
            events.append((min(positions), tactics))
        for match in re.finditer(r'^theorem\s+(exercise_\w+)\b', source, re.M):
            events.append((match.start(), match[1]))
        for _, event in sorted(events):
            if isinstance(event, list):
                learned.update(event)
            else:
                policies[event] = sorted(learned)
    return policies
