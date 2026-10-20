import {AbbreviationProvider, AbbreviationRewriter, Range} from './lean-unicode.js';

/** Adapt the VS Code extension's unmodified input engine to a plain textarea. */
export function attachUnicodeInput(input, onChange) {
  const config = {abbreviationCharacter: '\\', customTranslations: {}, eagerReplacementEnabled: true};
  let previous = input.value;
  let composing = false;
  let applying = false;
  let selecting = false;
  const source = {
    async replaceAbbreviations(changes) {
      applying = true;
      try {
        for (const {range, newText} of [...changes].sort((a, b) => b.range.offset - a.range.offset)) {
          // Native text insertion preserves the browser's undo history. The
          // fallback also supports replacement when the input has lost focus.
          input.setSelectionRange(range.offset, range.offset + range.length);
          if (document.activeElement !== input || !document.execCommand('insertText', false, newText)) {
            input.setRangeText(newText, range.offset, range.offset + range.length, 'end');
          }
        }
        previous = input.value;
        rewriter.changeInput(changes);
        return true;
      } finally { applying = false; }
    },
    selectionMoveMode() { return {kind: 'MoveAllSelections'}; },
    collectSelections() { return [new Range(input.selectionStart, input.selectionEnd - input.selectionStart)]; },
    setSelections(selections) {
      const selection = selections[0];
      if (selection) {
        selecting = true;
        input.setSelectionRange(selection.offset, selection.offset + selection.length);
        selecting = false;
      }
    },
  };
  const rewriter = new AbbreviationRewriter(config, new AbbreviationProvider(config), source);

  async function edited(event) {
    if (applying || composing || event?.isComposing) return;
    const current = input.value;
    if (current === previous) return;
    let start = 0;
    while (start < previous.length && start < current.length && previous[start] === current[start]) ++start;
    let oldEnd = previous.length, newEnd = current.length;
    while (oldEnd > start && newEnd > start && previous[oldEnd - 1] === current[newEnd - 1]) { --oldEnd; --newEnd; }
    const change = {range: new Range(start, oldEnd - start), newText: current.slice(start, newEnd)};
    previous = current;
    rewriter.changeInput([change]);
    await rewriter.triggerAbbreviationReplacement();
    onChange();
  }
  async function selectionChanged() {
    if (applying || selecting || composing || document.activeElement !== input) return;
    const before = input.value;
    await rewriter.changeSelections(source.collectSelections());
    if (input.value !== before) onChange();
  }
  async function flush() {
    const before = input.value;
    await rewriter.replaceAllTrackedAbbreviations();
    if (input.value !== before) onChange();
  }
  input.addEventListener('input', edited);
  input.addEventListener('compositionstart', () => { composing = true; });
  input.addEventListener('compositionend', () => { composing = false; edited(); });
  input.addEventListener('select', selectionChanged);
  input.addEventListener('click', selectionChanged);
  input.addEventListener('keyup', event => { if (event.key.startsWith('Arrow')) selectionChanged(); });
  input.addEventListener('blur', flush);
  return {
    edited, flush,
    hasPending() { return rewriter.getTrackedAbbreviations().size > 0; },
    reset() { previous = input.value; rewriter.resetTrackedAbbreviations(); },
  };
}
