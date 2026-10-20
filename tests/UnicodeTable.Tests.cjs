const assert = require('node:assert/strict');
const fs = require('node:fs');

(async () => {
  const source = fs.readFileSync('assets/web/lean-unicode.js', 'utf8');
  const {AbbreviationProvider} = await import('data:text/javascript;base64,' + Buffer.from(source).toString('base64'));
  const provider = new AbbreviationProvider({customTranslations: {}});
  const table = JSON.parse(fs.readFileSync('assets/web/vendor/lean-unicode-input/abbreviations.json', 'utf8'));
  assert.equal(Object.keys(table).length, 1857);
  assert.deepEqual(provider.getSymbolsByAbbreviation(), table);
  assert.equal(provider.getSymbolForAbbreviation('equiv'), '≃');
  assert.equal(provider.getSymbolForAbbreviation('=='), '≡');
  const appendix = fs.readFileSync('AlgebraBook/Symbols.lean', 'utf8').split(':::table')[1].split(':::')[0];
  const slash = String.fromCharCode(92);
  let checked = 0;
  for (const row of appendix.split(/^\*[ \t]*\r?$/m)) {
    const columns = [...row.matchAll(/^  \* (.*)$/gm)].map(match => match[1]);
    if (columns.length !== 4) continue;
    const symbols = [...columns[1].matchAll(/`([^`]+)`/g)].map(match => match[1]);
    for (const [, code] of columns[3].matchAll(/`([^`]+)`/g)) {
      if (!code.startsWith(slash)) continue;
      const key = code.slice(1);
      assert(symbols.includes(provider.getSymbolForAbbreviation(key)), `${code} does not produce ${symbols.join(', ')}`);
      ++checked;
    }
  }
  assert(checked >= 30, checked);
  const numbers = fs.readFileSync('AlgebraBook/NumbersRelations.lean', 'utf8');
  assert(numbers.includes('기호 `≡`는 `' + slash + '==`로 입력한다.'));
  console.log(`PASS: 1857 upstream abbreviations and ${checked} appendix aliases agree with VS Code`);
})().catch(error => {console.error(error); process.exitCode = 1;});
