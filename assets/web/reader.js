/* Interactive reading and browser-local Lean execution. */
(() => {
  'use strict';
  const siteRoot = new URL('.', document.baseURI);
  const assetsRoot = new URL(document.querySelector('meta[name="book-assets-base"]')?.content || '.', siteRoot);
  const staticReading = document.querySelector('meta[name="book-mode"]')?.content === 'static';
  const browserLean = document.querySelector('meta[name="book-mode"]')?.content === 'wasm';
  let browserBackend;
  const snippets = new Map();
  let activeEditor;
  const openEditors = new Map();
  let panelCounter = 0;
  const element = (tag, className, text) => {
    const node = document.createElement(tag);
    if (className) node.className = className;
    if (text !== undefined) node.textContent = text;
    return node;
  };
  const button = (text, action, className = '') => {
    const node = element('button', `book-button ${className}`, text);
    node.type = 'button';
    node.addEventListener('click', action);
    return node;
  };
  const plain = node => {
    const clone = node.cloneNode(true);
    clone.querySelectorAll('.tactic-state, .tactic-toggle, .hover-container, .hover-info').forEach(el => el.remove());
    return clone.textContent;
  };
  async function snippet(key) {
    if (!snippets.has(key)) {
      snippets.set(key, fetch(new URL(`playground/${key}.json`, assetsRoot)).then(response => {
        if (!response.ok) throw new Error('코드를 불러오지 못했습니다. 페이지를 새로고침해 주세요.');
        return response.json();
      }).catch(error => { snippets.delete(key); throw error; }));
    }
    return snippets.get(key);
  }
  function stored(key) { try { return localStorage.getItem(key); } catch { return null; } }
  function store(key, value) { try { localStorage.setItem(key, value); } catch { /* Private browsing may disable storage. */ } }
  function exerciseStorageId(original, key) { return original.storageKey || key; }
  const progressEpochKey = 'lean-algebra.progress-reset';
  function progressEpoch() { return stored(progressEpochKey); }
  function exerciseDraft(original, key) {
    return stored(`lean-algebra.code.${exerciseStorageId(original, key)}`)
      ?? (original.legacyKeys || [key]).map(old => stored(`lean-algebra.code.${old}`)).find(value => value != null);
  }
  function exerciseVersion(original) {
    return JSON.stringify([original.code, original.allowedTactics,
      original.contextFiles?.map(file => file.sha256)]);
  }
  function checkedExercise(original, key, code) {
    try {
      const saved = JSON.parse(stored(`lean-algebra.result.${exerciseStorageId(original, key)}`));
      if (saved?.code !== code) return null;
      if (saved.version === exerciseVersion(original)) return saved;
      // Keep historical results only when the exercise itself is unchanged.
      const previous = JSON.parse(saved.version);
      if (previous[0] !== original.code) return null;
      return {...saved, stale: true};
    } catch { return null; }
  }
  let draftManifest;
  function exerciseManifest() {
    draftManifest ||= fetch(new URL('exercises.json', assetsRoot)).then(response => {
      if (!response.ok) throw new Error('Exercise metadata is unavailable.');
      return response.json();
    }).catch(error => { draftManifest = undefined; throw error; });
    return draftManifest;
  }
  function hasExerciseDrafts() {
    try { return Object.keys(localStorage).some(key => key.startsWith('lean-algebra.code.')); }
    catch { return false; }
  }
  function tabSession(value) {
    try {
      if (value) sessionStorage.setItem('lean-algebra.session', value);
      return sessionStorage.getItem('lean-algebra.session');
    } catch { return null; }
  }
  async function call(path, payload) {
    if (!browserLean) throw new Error('WASM 실행 환경이 준비되지 않았습니다. 미리보기를 다시 시작해 주세요.');
    browserBackend ||= import(new URL('assets/web/wasm-reader.js', assetsRoot))
      .then(module => module.createBrowserBackend(siteRoot));
    return (await browserBackend).call(path, payload);
  }

  let rechecking = false;
  async function recheckStoredExercises() {
    // Do not trigger a service-worker reload merely to restore progress.
    if (!browserLean || !crossOriginIsolated || rechecking) return;
    rechecking = true;
    try {
      const manifest = await exerciseManifest();
      const {exerciseModel} = await import(new URL('assets/web/exercise-model.js', assetsRoot));
      for (const [key, data] of Object.entries(manifest)) {
        const code = exerciseDraft(data, key);
        if (code == null || !checkedExercise(data, key, code)?.stale) continue;
        const epoch = progressEpoch();
        const original = await snippet(key);
        const model = exerciseModel(original.code, code);
        const result = await call('/api/lean/check', {snippet: key, code, background: true,
          proofNames: model.parts.map(part => part.name)});
        if (epoch !== progressEpoch() || exerciseDraft(data, key) !== code) continue;
        if (result.contextErrors?.length) continue;
        const {verification} = verifyExercise(original, code, result, model);
        store(`lean-algebra.result.${exerciseStorageId(data, key)}`, JSON.stringify(verification));
        window.dispatchEvent(new CustomEvent('book-exercise-verified', {detail: {key}}));
        window.dispatchEvent(new Event('book-exercise-progress'));
        // Let foreground editing requests run before the next saved proof.
        await new Promise(resolve => setTimeout(resolve, 300));
      }
    } catch { /* Retain historical results if the runtime is unavailable. */ }
    finally { rechecking = false; }
  }
  window.addEventListener('book-lean-ready', recheckStoredExercises);

  function verifyExercise(original, code, result, exercise) {
    const errors = result.diagnostics.filter(item => item.severity === 1 && item.kind !== 'unfinished');
    const holes = result.diagnostics.some(item => item.kind === 'unfinished');
    const allowed = new Set(['propext', 'Classical.choice', 'Quot.sound']);
    const bodies = exercise?.parse(code);
    const audited = exercise?.parts.map(part => result.proofs?.find(proof =>
      proof.name === part.name || proof.name.endsWith('.' + part.name)));
    const forbidden = proof => proof?.axioms.filter(name => !allowed.has(name)) || [];
    const complete = audited?.map((proof, index) => {
      if (!bodies || !proof || forbidden(proof).length) return false;
      const start = exercise.start(bodies, index);
      const startLine = code.slice(0, start).split('\n').length;
      const endLine = code.slice(0, start + bodies[index].length).split('\n').length;
      return !errors.some(error => error.line >= startLine && error.line <= endLine);
    }) || [];
    const count = complete.filter(Boolean).length;
    const verification = {code, version: exerciseVersion(original),
      done: count, total: exercise?.parts.length || 0, parts: complete};
    return {errors, holes, bodies, audited, forbidden, complete, count, verification};
  }

  // Keep both branch-local states and the outer state after a nested `have`.
  function proofSteps(code) {
    const steps = [];
    const walk = tactic => {
      const label = tactic.querySelector(':scope > label');
      const state = tactic.querySelector(':scope > .tactic-state');
      if (!label || !state) return;
      const children = [...label.querySelectorAll('.tactic')].filter(child => child.parentElement.closest('.tactic') === tactic);
      children.forEach(walk);
      const first = plain(label).trim().split('\n')[0].trim();
      let nested = false;
      for (let parent = tactic.parentElement.closest('.tactic'); parent; parent = parent.parentElement.closest('.tactic')) {
        const heading = parent.querySelector(':scope > label');
        if (heading && /^(have|suffices|let|replace)\b/.test(plain(heading).trim())) nested = true;
      }
      if (!children.length || /^(have|suffices|let|replace)\b/.test(first)) steps.push({label, state, title: first, nested});
    };
    [...code.querySelectorAll('.tactic')].filter(node => !node.parentElement.closest('.tactic')).forEach(walk);
    return steps;
  }

  function decorate(wrapper) {
    const source = wrapper.querySelector('.hl.lean.block');
    if (!source || wrapper.dataset.readerReady) return;
    wrapper.dataset.readerReady = 'true';
    const key = wrapper.dataset.snippet;
    const exercise = !!wrapper.dataset.exerciseUnit;
    if (exercise) wrapper.id = `exercise-${key}`;
    wrapper.classList.toggle('book-exercise', exercise);
    const steps = proofSteps(source);
    const originalNodes = exercise ? [...source.childNodes].map(node => node.cloneNode(true)) : [];
    let inlineCode = null;
    let exerciseResult;
    let progressState;
    const toolbar = element('div', 'book-toolbar');
    toolbar.setAttribute('aria-label', '예제 도구');
    const body = element('div', 'book-example-body');
    source.before(body);
    body.append(source);
    wrapper.prepend(toolbar);
    const panel = element('section', 'book-reader-panel');
    panel.id = `book-panel-${++panelCounter}`;
    panel.hidden = true;
    body.append(panel);
    let workspace;
    const problemParagraphs = [];
    let problemNumber = '연습문제';
    let problemCaption = '';
    if (exercise) {
      workspace = element('dialog', 'book-exercise-workspace');
      const heading = element('div', 'book-exercise-heading');
      const title = element('strong', '', '연습문제 풀이');
      title.id = `book-exercise-${panelCounter}`;
      workspace.setAttribute('aria-labelledby', title.id);
      heading.append(title, button('본문으로', () => setMode(null)));
      const statement = element('div', 'book-exercise-statement');
      for (let node = wrapper.previousElementSibling; node?.tagName === 'P'; node = node.previousElementSibling) {
        problemParagraphs.unshift(node);
        if (/^(?:보충\s+)?문제\s*\d/.test(node.textContent.trim())) break;
      }
      const first = problemParagraphs[0];
      const number = first?.querySelector('strong');
      if (number) {
        problemNumber = number.textContent;
        number.remove();
        const caption = first.textContent.trim().match(/^\(([^\n]+)\)$/);
        if (caption) {
          problemCaption = caption[1];
          problemParagraphs.shift();
          first.remove();
        }
      }
      title.textContent = problemCaption ? `${problemNumber} (${problemCaption})` : problemNumber;
      for (const paragraph of problemParagraphs) {
        const clone = paragraph.cloneNode(true);
        clone.querySelectorAll('[id]').forEach(node => node.removeAttribute('id'));
        statement.append(clone);
      }
      workspace.append(heading, statement, panel);
      wrapper.append(workspace);
      workspace.addEventListener('cancel', event => { event.preventDefault(); setMode(null); });
    }
    let mode = null;
    let stepIndex = 0;
    let editor;
    let selectStep;
    const status = element('span', 'book-toolbar-status');
    status.setAttribute('role', 'status');
    let copyStatusTimer;
    function copyStatus(text) {
      clearTimeout(copyStatusTimer);
      status.textContent = text;
      copyStatusTimer = setTimeout(() => { status.textContent = ''; }, 1600);
    }
    let stepButton;
    const editButton = exercise ? button('풀기', () => setMode(mode === 'edit' ? null : 'edit')) : null;
    if (editButton && browserLean) editButton.title = '브라우저에서 Lean을 실행합니다. 첫 실행 시 약 300 MB를 내려받습니다.';
    const copyButton = button('', async () => {
      try {
        const text = exercise && inlineCode !== null ? inlineCode
          : mode === 'edit' && editor ? editor.code() : key ? (await snippet(key)).code : plain(source);
        await navigator.clipboard.writeText(text);
        copyStatus('복사됨');
      } catch { copyStatus('복사 실패'); }
    }, 'book-copy');
    copyButton.setAttribute('aria-label', '복사');
    copyButton.title = '코드 복사';
    const copyIcon = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
    copyIcon.setAttribute('viewBox', '0 0 24 24');
    copyIcon.setAttribute('width', '16'); copyIcon.setAttribute('height', '16');
    copyIcon.setAttribute('fill', 'none'); copyIcon.setAttribute('stroke', 'currentColor');
    copyIcon.setAttribute('stroke-width', '1.5'); copyIcon.setAttribute('aria-hidden', 'true');
    const outline = document.createElementNS('http://www.w3.org/2000/svg', 'path');
    outline.setAttribute('d', 'M8 8h12v13H8z M16 8V3H3v13h5');
    copyIcon.append(outline); copyButton.append(copyIcon);
    if (steps.length && !exercise) {
      stepButton = button('단계 보기', () => setMode(mode === 'steps' ? null : 'steps'), 'book-step-button');
      stepButton.title = '각 전술에서 가정과 목표가 어떻게 바뀌는지 확인합니다.';
      toolbar.classList.add('book-proof-toolbar');
      body.before(toolbar);
      toolbar.prepend(stepButton);

    }
    if (exercise) {
      const card = element('section', 'book-exercise-card');
      const heading = element('div', 'book-exercise-card-heading');
      const problemTitle = element('div', 'book-problem-title');
      problemTitle.append(element('strong', '', problemNumber));
      if (problemCaption) problemTitle.append(element('span', 'book-problem-caption', `(${problemCaption})`));
      heading.append(problemTitle);
      exerciseResult = element('span', 'book-exercise-result');
      exerciseResult.setAttribute('role', 'status');
      heading.append(exerciseResult);
      editButton.classList.add('book-solve-button');
      if (!staticReading) heading.append(editButton);
      const disclosures = [];
      for (let next = wrapper.nextElementSibling; next?.matches('details.book-disclosure'); next = next.nextElementSibling) {
        disclosures.push(next);
      }
      wrapper.before(card);
      card.append(heading, ...problemParagraphs, wrapper);
      card.append(...disclosures);
    }
    toolbar.append(copyButton, status);
    if (exercise) openEditors.set(key, () => setMode('edit'));
    function showDraft(data, code, verification = checkedExercise(data, key, code)) {
      inlineCode = code;
      const written = code.trimEnd() !== data.code.trimEnd();
      source.classList.toggle('book-draft-code', written);
      if (written) source.textContent = code.trimEnd();
      else source.replaceChildren(...originalNodes.map(node => node.cloneNode(true)));
      const done = verification?.done || 0;
      const total = verification?.total || 0;
      const complete = total > 0 && done === total;
      const nextProgressState = `${done}/${total}/${written}`;
      if (nextProgressState !== progressState) {
        progressState = nextProgressState;
        window.dispatchEvent(new Event('book-exercise-progress'));
      }
      const label = complete ? (verification.stale ? '✓ 완료 · 재검사 대기' : '✓ 완료')
        : done ? `${done}/${total} 완료${verification.stale ? ' · 재검사 대기' : ''}` : written ? '작성 중' : '';
      if (exerciseResult.textContent !== label) exerciseResult.textContent = label;
      exerciseResult.classList.toggle('book-exercise-complete', complete);
      editButton.textContent = complete ? '풀이 보기' : written ? '이어서 풀기' : '풀기';
    }
    if (exercise && hasExerciseDrafts()) {
      exerciseManifest().then(manifest => {
        if (editor) return;
        const data = manifest[key];
        if (!data) return;
        const draft = exerciseDraft(data, key);
        if (draft != null) showDraft(data, draft);
      }).catch(() => { /* Keep the original problem readable if restoration fails. */ });
    }
    function refreshStoredExercise(event) {
      const reset = event.type === 'book-exercise-reset' || event.key === progressEpochKey;
      if (mode === 'edit' || (!reset && event.key && !/^lean-algebra\.(code|result)\./.test(event.key))) return;
      exerciseManifest().then(manifest => {
        if (mode === 'edit') return;
        const data = manifest[key];
        if (!data) return;
        const id = exerciseStorageId(data, key);
        if (!reset && event.key && ![`lean-algebra.code.${id}`, `lean-algebra.result.${id}`].includes(event.key)) return;
        editor?.dispose();
        editor = undefined;
        const draft = exerciseDraft(data, key) ?? data.code.trimEnd();
        showDraft(data, draft);
      }).catch(() => {});
    }
    if (exercise) {
      window.addEventListener('storage', refreshStoredExercise);
      window.addEventListener('book-exercise-reset', refreshStoredExercise);
      window.addEventListener('book-exercise-verified', event => {
        if (event.detail.key === key) refreshStoredExercise(event);
      });
    }
    for (const control of [stepButton, editButton].filter(Boolean)) {
      control.setAttribute('aria-controls', panel.id);
      control.setAttribute('aria-expanded', 'false');
    }

    function showSteps() {
      const heading = element('div', 'book-panel-heading');
      heading.append(element('strong', '', '가정과 목표'));
      const state = element('div', 'book-step-state hl lean');
      state.setAttribute('aria-live', 'polite');
      const controls = element('div', 'book-step-controls');
      const previous = button('← 이전', () => show(stepIndex - 1));
      const next = button('다음 →', () => show(stepIndex + 1));
      const count = element('span', 'book-step-count');
      const title = element('code', 'book-step-title');
      controls.append(previous, count, next);
      const header = element('div', 'book-step-header');
      header.append(heading, controls);
      panel.append(header, title, state);
      function show(index) {
        stepIndex = Math.max(0, Math.min(index, steps.length - 1));
        source.querySelectorAll('.book-current-step').forEach(node => node.classList.remove('book-current-step'));
        const step = steps[stepIndex];
        step.label.classList.add('book-current-step');
        const selected = step.label.getBoundingClientRect();
        const viewport = source.getBoundingClientRect();
        if (selected.top < viewport.top) source.scrollTop -= viewport.top - selected.top;
        else if (selected.bottom > viewport.bottom) source.scrollTop += selected.bottom - viewport.bottom;
        const clone = step.state.cloneNode(true);
        clone.removeAttribute('id');
        clone.querySelectorAll('[id]').forEach(node => node.removeAttribute('id'));
        clone.style.display = 'block';
        if (!clone.querySelector('.goal')) clone.textContent = step.nested ? '보조 증명 완료' : '남은 목표 없음';
        state.replaceChildren(clone);
        title.textContent = step.title;
        count.textContent = `${stepIndex + 1} / ${steps.length}`;
        previous.disabled = stepIndex === 0;
        next.disabled = stepIndex === steps.length - 1;
      }
      selectStep = show;
      show(stepIndex);
    }

    async function setMode(next) {
      if (mode === 'edit' && next !== 'edit' && editor) editor.snapshot();
      if (next === 'edit') {
        if (activeEditor && activeEditor.wrapper !== wrapper) activeEditor.close();
        activeEditor = {wrapper, close: () => setMode(null)};
      } else if (activeEditor?.wrapper === wrapper) activeEditor = null;
      mode = next;
      wrapper.classList.toggle('book-reading', mode === 'steps');
      wrapper.classList.toggle('book-editing', mode === 'edit');
      if (workspace) {
        if (mode === 'edit' && !workspace.open) workspace.showModal();
        else if (mode !== 'edit' && workspace.open) { workspace.close(); editButton.focus(); }
        document.documentElement.classList.toggle('book-solving', mode === 'edit');
      }
      panel.hidden = !mode;
      if (stepButton) stepButton.setAttribute('aria-expanded', String(mode === 'steps'));
      editButton?.setAttribute('aria-expanded', String(mode === 'edit'));
      source.querySelectorAll('.tactic-toggle').forEach(toggle => { toggle.checked = false; });
      source.querySelectorAll('.book-current-step').forEach(node => node.classList.remove('book-current-step'));
      panel.replaceChildren();
      if (mode === 'steps') showSteps();
      if (mode === 'edit') {
        panel.append(element('p', 'book-help', '불러오는 중…'));
        try {
          const data = await snippet(key);
          if (mode !== 'edit') return;
          panel.replaceChildren();
          if (!editor) {
            const model = exercise ? await import(new URL('assets/web/exercise-model.js', assetsRoot)) : null;
            const unicode = await import(new URL('assets/web/unicode-input.js', assetsRoot));
            if (mode !== 'edit') return;
            editor = createEditor(key, data, model?.exerciseModel, unicode.attachUnicodeInput,
              (code, verification) => showDraft(data, code, verification));
          }
          panel.append(editor.root);
          editor.input.focus();
          editor.activate();
        } catch (error) { panel.replaceChildren(element('p', 'book-error', error.message)); }
      }
    }
    source.addEventListener('click', event => {
      if ((!steps.length && !exercise) || event.target.closest('a[href]') || event.ctrlKey || event.metaKey) return;
      if (window.getSelection()?.toString()) return;
      if (exercise) {
        event.preventDefault(); event.stopPropagation(); setMode('edit'); return;
      }
      const label = event.target.closest('.tactic > label');
      const index = steps.findIndex(step => step.label === label);
      event.preventDefault();
      event.stopPropagation();
      if (mode !== 'steps') setMode('steps');
      selectStep(index >= 0 ? index : stepIndex);
    }, true);
    if (steps.length || exercise) {
      source.tabIndex = 0;
      source.setAttribute('aria-label', exercise ? 'Lean 연습문제. 누르면 풀이 화면이 열립니다.'
        : 'Lean 증명. 누르면 단계별 가정과 목표를 볼 수 있습니다.');
      source.addEventListener('keydown', event => {
        if (event.target !== source || !['Enter', ' '].includes(event.key)) return;
        event.preventDefault();
        setMode(exercise ? 'edit' : mode === 'steps' ? null : 'steps');
      });
    }
  }

  function createEditor(key, original, makeExercise, attachUnicodeInput, onDraft) {
    const root = element('div', 'book-live-editor');
    const controls = element('div', 'book-editor-controls');
    const input = element('textarea', 'book-code-input');
    input.setAttribute('aria-label', '수정할 Lean 코드');
    input.spellcheck = false;
    input.autocapitalize = 'off';
    input.autocomplete = 'off';
    input.wrap = 'off';
    const storageKey = `lean-algebra.code.${exerciseStorageId(original, key)}`;
    const draft = exerciseDraft(original, key) ?? original.code.trimEnd();
    const exercise = makeExercise?.(original.code, draft);
    let fullCode = exercise?.full || false;
    let toggleCode;
    let selectedProof = 0;
    let unicodeInput;
    let refreshTheorems = () => {};
    const declaration = element('pre', 'book-exercise-declaration');
    const support = element('details', 'book-exercise-support');
    support.open = true;
    const supportCode = element('pre', 'book-exercise-declaration');
    support.append(element('summary', '', '사용할 정의'), supportCode);
    const proofControls = element('div', 'book-proof-controls');
    function currentCode() {
      if (!exercise || fullCode) return input.value;
      exercise.bodies[selectedProof] = exercise.sourceBody(input.value);
      return exercise.source(exercise.bodies);
    }
    function editableStart() { return exercise && !fullCode ? exercise.start(exercise.bodies, selectedProof) : 0; }
    function loadProof() {
      input.value = exercise.editorBody(exercise.bodies[selectedProof]);
      unicodeInput?.reset();
      declaration.textContent = exercise.parts[selectedProof].header.trimEnd();
      supportCode.textContent = exercise.parts.slice(0, selectedProof + 1).map(part => part.prefix).join('').trim();
      support.hidden = fullCode || !supportCode.textContent;
      declaration.hidden = fullCode;
      proofControls.hidden = fullCode || exercise.parts.length === 1;
      input.setAttribute('aria-label', fullCode ? '연습문제 전체 코드' : `풀이 ${selectedProof + 1}`);
      [...proofControls.children].forEach((node, i) => node.setAttribute('aria-pressed', String(i === selectedProof)));
      showSubproofs(checkedExercise(original, key, currentCode()));
      refreshTheorems();
    }
    function showSubproofs(verification) {
      [...proofControls.children].forEach((control, index) => {
        const complete = verification?.parts?.[index]
          ?? (verification?.total > 0 && verification.done === verification.total);
        control.dataset.complete = String(!!complete);
        control.setAttribute('aria-label', `(${index + 1})`);
        control.setAttribute('aria-description', complete ? '완료' : '미완료');
        control.title = `소문제 ${index + 1}${complete ? ' · 완료' : ''}`;
      });
    }
    if (exercise) {
      for (const [index] of exercise.parts.entries()) proofControls.append(button(`(${index + 1})`, () => {
        currentCode(); selectedProof = index; loadProof(); input.focus(); changed();
      }));
      if (fullCode) input.value = draft;
      else loadProof();
    } else input.value = draft;
    const message = element('span', 'book-run-status', '대기 중');
    message.setAttribute('role', 'status');
    const run = button(exercise ? '검사' : '실행', check, 'book-primary');
    const reset = button('초기화', () => {
      if (exercise) {
        exercise.bodies = exercise.parts.map(part => part.body);
        if (fullCode) input.value = original.code.trimEnd();
        else loadProof();
      } else input.value = original.code.trimEnd();
      unicodeInput?.reset();
      changed();
      input.focus();
    });
    controls.append(run, reset, message);
    if (exercise) {
      toggleCode = button(fullCode ? '증명만 편집' : '전체 코드', () => {
        const source = currentCode();
        if (fullCode) {
          const bodies = exercise.parse(source);
          if (!bodies) {
            message.textContent = '정리의 선언이나 보조 정의를 수정한 코드는 전체 코드에서 편집할 수 있습니다.';
            return;
          }
          exercise.bodies = bodies;
        }
        fullCode = !fullCode;
        if (fullCode) input.value = source;
        else loadProof();
        unicodeInput?.reset();
        declaration.hidden = fullCode;
        support.hidden = fullCode || !supportCode.textContent;
        proofControls.hidden = fullCode || exercise.parts.length === 1;
        toggleCode.textContent = fullCode ? '증명만 편집' : '전체 코드';
        refreshTheorems();
        input.setAttribute('aria-label', fullCode ? '연습문제 전체 코드' : `풀이 ${selectedProof + 1}`);
        input.focus(); changed();
      });
      const download = button('풀이 내려받기', () => {
        let source = (original.sourceBefore || original.before).trimEnd() + '\n\n' + currentCode() + '\n';
        const scopes = [];
        for (const line of source.split('\n')) {
          const open = /^(namespace|section)(?:\s+(\S+))?\s*$/.exec(line);
          if (open) scopes.push(open[2] || '');
          else if (/^end(?:\s+\S+)?\s*$/.test(line)) scopes.pop();
        }
        source += scopes.reverse().map(name => `end${name ? ' ' + name : ''}\n`).join('');
        const url = URL.createObjectURL(new Blob([source], {type: 'text/plain;charset=utf-8'}));
        const link = element('a'); link.href = url; link.download = exercise.parts[0].name + '.lean';
        link.click(); setTimeout(() => URL.revokeObjectURL(url), 1000);
      });
      controls.insertBefore(toggleCode, message);
      controls.insertBefore(download, message);
      root.append(proofControls, support, declaration);
      declaration.hidden = fullCode;
      support.hidden = fullCode || !supportCode.textContent;
      proofControls.hidden = fullCode || exercise.parts.length === 1;
    }
    const columns = element('div', 'book-editor-columns');
    const codePane = element('div', 'book-edit-code');
    const gutter = element('pre', 'book-line-numbers');
    gutter.setAttribute('aria-hidden', 'true');
    codePane.append(gutter, input);
    const output = element('section', 'book-live-output');
    output.setAttribute('aria-label', 'Lean 실행 결과');
    const outputHeading = element('strong', 'book-panel-heading', '가정과 목표');
    const goal = element('pre', 'book-live-goal', '실행 후 코드 위치를 선택하면 가정과 목표가 표시됩니다.');
    const diagnostics = element('div', 'book-diagnostics');
    output.append(outputHeading, goal, diagnostics);
    if (exercise && original.theorems) {
      const reference = element('section', 'book-theorems');
      reference.setAttribute('aria-label', '사용할 수 있는 정리');
      const heading = element('div', 'book-theorems-heading');
      const count = element('span', 'book-theorems-count');
      heading.append(element('strong', '', '찾기'), count);
      const search = element('input', 'book-theorems-search');
      search.type = 'search'; search.placeholder = '이름 또는 명제';
      search.setAttribute('aria-label', '정리 검색');
      const list = element('div', 'book-theorems-list');
      reference.append(heading, search, list);
      output.append(reference);
      refreshTheorems = () => {
        const earlier = fullCode ? [] : exercise.parts.slice(0, selectedProof).map(part => ({
          name: part.name, reference: part.name,
          statement: part.header.trim().replace(/^theorem\s+\S+\s*/, '').replace(/\s*:=\s*by$/, ''),
        }));
        const available = [...earlier, ...original.theorems];
        const query = search.value.trim().toLocaleLowerCase();
        const words = query.split(/\s+/).filter(Boolean);
        const found = available.filter(item => words.every(word =>
          `${item.name} ${item.reference} ${item.statement} ${item.declaration || ''}`.toLocaleLowerCase().includes(word)));
        count.textContent = query ? `${found.length} / ${available.length}` : String(available.length);
        list.replaceChildren();
        for (const item of found) {
          const row = element('article', 'book-theorem');
          const name = button(item.reference, async () => {
            try {
              await navigator.clipboard.writeText(item.reference);
              name.title = '복사됨';
              setTimeout(() => { name.title = '정리 이름 복사'; }, 1200);
            } catch { name.title = '복사하지 못했습니다.'; }
          }, 'book-theorem-name');
          name.title = '정리 이름 복사';
          name.setAttribute('aria-label', `${item.reference} 이름 복사`);
          row.append(name, element('pre', 'book-theorem-statement', item.declaration || item.statement));
          list.append(row);
        }
        if (!found.length) list.append(element('p', 'book-theorems-empty', '일치하는 정리가 없습니다.'));
      };
      search.addEventListener('input', refreshTheorems);
      refreshTheorems();
    }
    columns.append(codePane, output);
    root.append(controls, columns, element('p', 'book-help',
      '자동 검사 · Ctrl+Enter 즉시 검사 · \\forall → ∀ 자동 입력'));
    if (browserLean) window.addEventListener('book-lean-progress', event => {
      if (busy && root.isConnected) message.textContent = event.detail;
    });
    let session;
    let version;
    let checkedCode;
    let busy = false;
    let timer;
    let compileTimer;
    let activated = false;
    let disposed = false;
    let requestNumber = 0;
    let documentQueue = Promise.resolve();
    function resetProgress(event) {
      if (event.type === 'storage' && event.key !== progressEpochKey) return;
      if (!exercise) return;
      clearTimeout(compileTimer);
      clearTimeout(timer);
      checkedCode = undefined;
      ++requestNumber;
      exercise.bodies = exercise.parts.map(part => part.body);
      fullCode = false;
      toggleCode.textContent = '전체 코드';
      loadProof();
      showSubproofs(null);
      onDraft?.(currentCode(), null);
      diagnostics.replaceChildren();
      outputHeading.textContent = '가정과 목표';
      goal.textContent = '풀이를 작성하면 가정과 목표가 표시됩니다.';
      lines();
      message.textContent = '풀이가 초기화되었습니다.';
      message.className = 'book-run-status';
    }
    window.addEventListener('book-exercise-reset', resetProgress);
    window.addEventListener('storage', resetProgress);
    // Serialize edits to the same LSP document. Skip queued requests for text
    // that has already changed instead of sending an older document to Lean.
    function documentCall(path, code, payload) {
      const task = documentQueue.catch(() => {}).then(async () => {
        if (currentCode() !== code || !root.isConnected) return null;
        const result = await call(path, {snippet: key, code, session: session || tabSession(),
          proofRange: proofRange(), proofNames: exercise?.parts.map(part => part.name), ...payload});
        session = result.session;
        tabSession(session);
        version = result.version;
        return result;
      });
      documentQueue = task;
      return task;
    }
    function position() {
      const visible = input.value.slice(0, input.selectionStart);
      const offset = exercise && !fullCode ? exercise.sourceBody(visible).length : input.selectionStart;
      const before = currentCode().slice(0, editableStart() + offset);
      const lines = before.split('\n');
      return {line: lines.length - 1, character: lines.at(-1).length};
    }
    function proofRange() {
      if (!exercise || fullCode) return null;
      const source = currentCode();
      const start = editableStart() - exercise.parts[selectedProof].header.length;
      const end = editableStart() + exercise.bodies[selectedProof].length;
      return {startLine: source.slice(0, start).split('\n').length - 1,
        endLine: source.slice(0, end).split('\n').length - 1};
    }
    function lines() {
      gutter.textContent = Array.from({length: input.value.split('\n').length}, (_, i) => i + 1).join('\n');
      const narrow = window.matchMedia('(max-width: 640px)').matches;
      input.wrap = narrow ? 'soft' : 'off';
      input.style.height = narrow ? 'auto' : `${Math.min(680, Math.max(200, input.value.split('\n').length * 28 + 24))}px`;
      if (narrow) input.style.height = `${Math.min(680, Math.max(200, input.scrollHeight))}px`;
    }
    function scheduleCheck(delay = 650) {
      clearTimeout(compileTimer);
      compileTimer = setTimeout(check, delay);
    }
    function changed() {
      if (disposed) return;
      store(storageKey, currentCode());
      const verification = checkedExercise(original, key, currentCode());
      showSubproofs(verification);
      onDraft?.(currentCode(), verification);
      message.textContent = '수정됨';
      message.className = 'book-run-status';
      outputHeading.textContent = '이전 검사 결과 · 수정 내용 검사 대기 중';
      ++requestNumber;
      lines();
      scheduleCheck();

    }
    function showGoal(value, note) {
      outputHeading.textContent = note || '가정과 목표';
      goal.textContent = value === null ? '이 위치에는 표시할 목표가 없습니다.'
        : value.length ? value.join('\n\n') : '남은 목표 없음';
    }
    async function check() {
      clearTimeout(compileTimer);
      if (disposed || busy || !root.isConnected) return;
      busy = true;
      run.disabled = true;
      message.textContent = '실행 중…';
      message.className = 'book-run-status';
      const code = currentCode();
      const epoch = progressEpoch();
      ++requestNumber;
      try {
        const result = await documentCall('/api/lean/check', code, {position: position()});
        if (!result || disposed || epoch !== progressEpoch()) return;
        checkedCode = code;
        if (code !== currentCode()) return;
        showGoal(result.goal, result.goalNote);
        diagnostics.replaceChildren();
        for (const item of result.diagnostics) {
          if (item.kind === 'unfinished' || (item.isSilent && item.severity !== 1)) continue;
          const start = code.split('\n').slice(0, item.line - 1).reduce((n, line) => n + line.length + 1, 0) + item.column - 1;
          const proofIndex = exercise && !fullCode
            ? exercise.parts.findLastIndex((_, i) => exercise.start(exercise.bodies, i) <= start) : -1;
          const row = proofIndex < 0 ? item.line
            : code.slice(exercise.start(exercise.bodies, proofIndex), start).split('\n').length;
          const label = proofIndex >= 0 && exercise.parts.length > 1 ? `풀이 (${proofIndex + 1}) ` : '';
          const column = proofIndex < 0 ? item.column : Math.max(1, item.column - 2);
          const diagnostic = button(`${label}${row}:${column}  ${item.message}`, () => {
            if (exercise && !fullCode) {
              const index = exercise.parts.findLastIndex((_, i) => exercise.start(exercise.bodies, i) <= start);
              if (index >= 0) { selectedProof = index; loadProof(); lines(); }
            }
            input.focus();
            const offset = Math.max(0, start - editableStart());
            const cursor = exercise && !fullCode
              ? exercise.editorBody(exercise.bodies[selectedProof].slice(0, offset)).length : offset;
            input.setSelectionRange(cursor, cursor);
            updateGoal();
          }, item.severity === 1 ? 'book-error' : 'book-warning');
          diagnostics.append(diagnostic);
        }
        if (result.contextErrors.length) {
          throw new Error('이 예제에 필요한 정의를 불러오지 못했습니다.\n' + result.contextErrors.join('\n'));
        }
        const {errors, holes, bodies, audited, forbidden, complete, count, verification} =
          verifyExercise(original, code, result, exercise);
        store(`lean-algebra.result.${exerciseStorageId(original, key)}`, JSON.stringify(verification));
        showSubproofs(verification);
        onDraft?.(code, verification);
        const selected = audited?.[selectedProof];
        const blocked = forbidden(selected);
        let success = false;
        if (errors.length) message.textContent = `오류 ${errors.length}개`;
        else if (bodies && count === exercise.parts.length) {
          message.textContent = '풀이 완료'; success = true;
        } else if (bodies && complete[selectedProof]) {
          message.textContent = `증명 완료 (${count}/${exercise.parts.length} 완료)`; success = true;
        } else if (blocked.some(name => name !== 'sorryAx')) {
          message.textContent = '미완성 · 허용되지 않은 공리: ' + blocked.join(', ');
        } else if (holes || blocked.includes('sorryAx')) message.textContent = '증명 중';
        else if (exercise && !bodies) message.textContent = '코드 검사 통과';
        else message.textContent = exercise ? '완결 여부 확인 불가' : '오류 없음';
        if (blocked.includes('sorryAx') && !errors.length) {
          diagnostics.append(element('p', 'book-warning',
            '이 증명은 sorry 또는 미완성 정리에 의존하므로 아직 완결되지 않았습니다.'));
        }
        message.classList.toggle('book-error', !!errors.length);
        message.classList.toggle('book-success', success);
      } catch (error) {
        if (!disposed && code === currentCode()) {
          message.textContent = '실행 실패';
          diagnostics.replaceChildren(element('p', 'book-error', error.message));
        }
      } finally {
        busy = false;
        run.disabled = false;
        if (!disposed && epoch === progressEpoch()) {
          if (currentCode() !== code) scheduleCheck(250);
          else if (checkedCode === code) updateGoal();
        }
      }
    }
    async function updateGoal() {
      clearTimeout(timer);
      if (disposed || busy || !root.isConnected || !session || checkedCode !== currentCode()) return;
      const current = ++requestNumber;
      timer = setTimeout(async () => {
        try {
          const result = await call('/api/lean/goal', {session, version, position: position(), proofRange: proofRange()});
          if (current === requestNumber && checkedCode === currentCode()) showGoal(result.goal, result.goalNote);
        } catch (error) {
          if (root.isConnected && /Run this example|code changed/.test(error.message)) {
            checkedCode = undefined;
            scheduleCheck(50);
          }
        }
      }, 180);
    }
    unicodeInput = attachUnicodeInput(input, changed);
    input.addEventListener('click', updateGoal);
    input.addEventListener('select', updateGoal);
    input.addEventListener('keyup', event => { if (event.key.startsWith('Arrow')) updateGoal(); });
    input.addEventListener('scroll', () => { gutter.scrollTop = input.scrollTop; });
    input.addEventListener('keydown', async event => {
      if (event.isComposing) return;
      if ((event.ctrlKey || event.metaKey) && event.key === 'Enter') {
        event.preventDefault(); await unicodeInput.flush(); check(); return;
      }
      if (event.key === 'Tab') {
        event.preventDefault();
        if (unicodeInput.hasPending()) { await unicodeInput.flush(); return; }
        const start = input.selectionStart;
        if (!event.shiftKey) input.setRangeText('  ', start, input.selectionEnd, 'end');
        await unicodeInput.edited();
      }
      if (event.key === 'Enter' && !event.ctrlKey && !event.metaKey) {
        event.preventDefault();
        const before = input.value.slice(0, input.selectionStart).split('\n').at(-1);
        const code = before.split('--')[0].trimEnd();
        const branch = /^[\t ]*[·.](?:\s|$)/.test(code);
        const nested = /\bby$|=>$/.test(code);
        const indent = before.match(/^[\t ]*/)[0] + '  '.repeat(Number(branch) + Number(nested));
        input.setRangeText('\n' + indent, input.selectionStart, input.selectionEnd, 'end');
        await unicodeInput.edited();
      }
    });
    lines();
    function activate() {
      lines();
      if (!activated) {
        const hole = input.value.search(/\bsorry\b/);
        const position = hole < 0 ? input.value.length : hole;
        input.setSelectionRange(position, position);
        activated = true;
      }
      if (checkedCode !== currentCode()) scheduleCheck(50);
      else updateGoal();
    }
    const resize = () => { if (root.isConnected) lines(); };
    window.addEventListener('resize', resize);
    function snapshot() {
      const code = currentCode();
      store(storageKey, code);
      const verification = checkedExercise(original, key, code);
      showSubproofs(verification);
      onDraft?.(code, verification);
    }
    snapshot();
    function dispose() {
      window.removeEventListener('book-exercise-reset', resetProgress);
      window.removeEventListener('storage', resetProgress);
      disposed = true;
      clearTimeout(compileTimer);
      clearTimeout(timer);
      ++requestNumber;
      window.removeEventListener('resize', resize);
    }
    return {root, input, activate, code: currentCode, snapshot, dispose};
  }

  function foldLegacyHints() {
    for (const paragraph of document.querySelectorAll('main p')) {
      if (paragraph.closest('.book-disclosure')) continue;
      if (!/^힌트\s/.test(paragraph.textContent.trim())) continue;
      const details = element('details', 'book-disclosure');
      details.append(element('summary', '', '힌트'));
      paragraph.before(details);
      details.append(paragraph);
    }
  }
  function trackReadingPosition(sections) {
    if (!sections.length) return;
    let active;
    let pending = false;
    const update = () => {
      pending = false;
      // A heading stays current until the next major section reaches the reading line.
      const line = Math.min(120, window.innerHeight * 0.2);
      let current;
      for (const section of sections) {
        if (section.heading.getBoundingClientRect().top > line) break;
        current = section;
      }
      if (current === active) return;
      active?.link.removeAttribute('aria-current');
      active = current;
      active?.link.setAttribute('aria-current', 'location');
    };
    const schedule = () => {
      if (pending) return;
      pending = true;
      requestAnimationFrame(update);
    };
    // Capture scrolling inside a reading pane as well as ordinary window scrolling.
    window.addEventListener('scroll', schedule, {passive: true, capture: true});
    window.addEventListener('resize', schedule, {passive: true});
    window.addEventListener('hashchange', schedule);
    window.addEventListener('pageshow', schedule);
    window.addEventListener('load', schedule, {once: true});
    document.fonts?.ready.then(schedule);
    const main = document.querySelector('main');
    if (main && typeof ResizeObserver !== 'undefined') {
      new ResizeObserver(schedule).observe(main);
    }
    schedule();
  }

  function openLinkedExercise() {
    const match = /^#exercise-(\d+)$/.exec(location.hash);
    if (!match || !openEditors.has(match[1])) return false;
    document.getElementById(`exercise-${match[1]}`)?.scrollIntoView({block: 'start'});
    openEditors.get(match[1])();
    return true;
  }

  async function startExerciseProgress(tree) {
    try {
      const manifest = await exerciseManifest();
      const exercises = Object.entries(manifest).filter(([, data]) =>
        data.exercise && data.exerciseChapter && Number.isInteger(data.exerciseOrder))
        .sort((a, b) => a[1].exerciseOrder - b[1].exerciseOrder);
      if (!exercises.length) return;
      const panel = element('section', 'book-progress');
      panel.setAttribute('aria-label', '연습문제 진행도');
      const summary = element('div', 'book-progress-summary');
      const total = element('span', 'book-progress-total');
      total.setAttribute('role', 'status');
      summary.append(element('span', '', '연습문제'), total);
      const next = button('미완료 문제로 이동', () => {
        const remaining = exercises.filter(([key]) => !completed.has(key));
        const selected = remaining.find(([, data]) => data.exerciseChapter === currentChapter) || remaining[0];
        if (!selected) return;
        const [key, data] = selected;
        const target = new URL(`${data.exerciseChapter}/#exercise-${key}`, siteRoot);
        if (target.pathname === location.pathname) {
          history.replaceState(null, '', target);
          openLinkedExercise();
        } else location.assign(target.href);
      }, 'book-progress-next');
      const note = element('small', 'book-progress-storage');
      note.setAttribute('role', 'status');
      const reset = button('진행 상황 초기화', () => {
        if (!window.confirm('이 책에 저장한 풀이와 완료 기록을 모두 지웁니다. 초기화할까요?')) return;
        try {
          for (const [key, data] of exercises) {
            const ids = new Set([exerciseStorageId(data, key), key, ...(data.legacyKeys || [])]);
            for (const id of ids) {
              localStorage.removeItem(`lean-algebra.code.${id}`);
              localStorage.removeItem(`lean-algebra.result.${id}`);
            }
          }
          localStorage.setItem(progressEpochKey, `${Date.now()}-${Math.random()}`);
        } catch {
          note.textContent = '초기화하지 못했습니다.';
          return;
        }
        window.dispatchEvent(new Event('book-exercise-reset'));
        refresh();
        note.textContent = '초기화됨';
      }, 'book-progress-reset');
      reset.title = '이 책에 저장한 풀이와 완료 기록을 모두 지웁니다.';
      const footer = element('div', 'book-progress-footer');
      footer.append(next, reset);
      panel.append(summary, footer, note);
      tree.after(panel);
      const chapters = new Map();
      for (const anchor of tree.querySelectorAll(':scope > li > a')) {
        const chapter = exercises.find(([, data]) =>
          new URL(`${data.exerciseChapter}/`, siteRoot).pathname === new URL(anchor.href).pathname)?.[1].exerciseChapter;
        if (!chapter) continue;
        const count = element('span', 'book-chapter-progress');
        anchor.classList.add('book-chapter-link');
        anchor.append(count);
        chapters.set(chapter, count);
      }
      const currentChapter = [...chapters.keys()].find(chapter =>
        new URL(`${chapter}/`, siteRoot).pathname === location.pathname);
      let completed = new Set();
      let pending = false;
      function refresh() {
        pending = false;
        completed = new Set(exercises.filter(([key, data]) => {
          const code = exerciseDraft(data, key);
          if (code == null) return false;
          const checked = checkedExercise(data, key, code);
          const parts = (data.code.match(/^theorem\s+/gm) || []).length;
          return parts > 0 && checked?.total === parts && checked.done === parts;
        }).map(([key]) => key));
        const label = `${completed.size} / ${exercises.length}`;
        if (total.textContent !== label) total.textContent = label;
        for (const [chapter, count] of chapters) {
          const items = exercises.filter(([, data]) => data.exerciseChapter === chapter);
          const done = items.filter(([key]) => completed.has(key)).length;
          count.textContent = `${done}/${items.length}`;
          count.setAttribute('aria-label', `연습문제 ${items.length}개 중 ${done}개 완료`);
        }
        next.disabled = completed.size === exercises.length;
        next.textContent = next.disabled ? '모든 문제 완료' : '미완료 문제로 이동';
      }
      function schedule() {
        if (pending) return;
        pending = true;
        requestAnimationFrame(refresh);
      }
      window.addEventListener('book-exercise-progress', schedule);
      window.addEventListener('book-exercise-reset', schedule);
      window.addEventListener('storage', event => {
        if (!event.key || /^lean-algebra\.(code|result)\./.test(event.key)) schedule();
      });
      window.addEventListener('pageshow', schedule);
      refresh();
      setTimeout(recheckStoredExercises, 1500);
    } catch { /* Reading remains available without local progress metadata. */ }
  }

  function start() {
    for (const link of document.querySelectorAll('main .permalink-widget a')) {
      link.textContent = '#';
      link.title = '이 절의 링크';
      link.setAttribute('aria-label', '이 절의 링크');
    }
    function prepareSearch() {
      const search = document.querySelector('#search-wrapper [role="searchbox"]');
      if (!search) return false;
      if (document.querySelector('meta[name="book-assets-base"]') && search.dataset.searchReady !== 'true') return false;
      search.setAttribute('placeholder', '본문 검색');
      search.setAttribute('aria-label', '본문 검색');
      // Verso searches on keyup. Pasting and mobile composition also need to
      // refresh results, even when they produce no physical keyboard event.
      const refreshSearch = () => queueMicrotask(() =>
        search.dispatchEvent(new KeyboardEvent('keyup', {key: 'Process', bubbles: true})));
      search.addEventListener('input', event => { if (!event.isComposing) refreshSearch(); });
      search.addEventListener('compositionend', refreshSearch);
      return true;
    }
    if (!prepareSearch()) {
      // Verso inserts its search widget asynchronously after the reader starts.
      const ready = new MutationObserver(() => { if (prepareSearch()) ready.disconnect(); });
      ready.observe(document.querySelector('header') || document.body, {childList:true, attributes:true, subtree:true});
    }
    const tocToggle = document.getElementById('toggle-toc');
    const tocButton = document.getElementById('toggle-toc-click');
    if (tocToggle && tocButton) {
      tocButton.tabIndex = 0;
      tocButton.setAttribute('role', 'button');
      tocButton.setAttribute('aria-label', '목차');
      tocButton.setAttribute('aria-controls', 'toc');
      const mobile = window.matchMedia('(max-width: 700px)');
      const update = () => {
        tocButton.setAttribute('aria-expanded', String(tocToggle.checked));
        // Hidden mobile navigation must not receive keyboard focus.
        for (const content of document.querySelectorAll('#toc > :not(input)')) {
          content.inert = mobile.matches && !tocToggle.checked;
        }
      };
      const close = () => { tocToggle.checked = false; update(); };
      tocToggle.addEventListener('change', update);
      mobile.addEventListener('change', update);
      tocButton.addEventListener('keydown', event => {
        if (!['Enter', ' '].includes(event.key)) return;
        event.preventDefault();
        tocButton.click();
      });
      document.addEventListener('click', event => {
        if (event.target.closest('#toc a, #toc .book-progress-next')) close();
      });
      document.addEventListener('keydown', event => {
        if (event.key !== 'Escape' || !mobile.matches || !tocToggle.checked) return;
        close();
        tocButton.focus();
      });
      update();
    }
    for (const table of document.querySelectorAll('main table')) {
      if (table.closest('.book-table-scroll')) continue;
      const scroll = element('div', 'book-table-scroll');
      scroll.tabIndex = 0;
      scroll.setAttribute('role', 'region');
      scroll.setAttribute('aria-label', '표 · 가로로 스크롤할 수 있습니다.');
      table.before(scroll);
      scroll.append(table);
    }
    // Keep the chapter list and current chapter's sections in one navigation tree.
    const splitTocs = document.querySelector('#toc .split-tocs');
    const bookTable = splitTocs?.querySelector('.split-toc.book table');
    if (bookTable) {
      const tree = element('ol', 'book-toc-tree');
      tree.setAttribute('aria-label', '목차');
      const readingSections = [];
      for (const row of bookTable.rows) {
        const link = row.querySelector('a');
        if (!link) continue;
        const item = element('li');
        const anchor = link.cloneNode(true);
        const number = row.querySelector('.num')?.textContent.trim();
        if (number) anchor.prepend(`${number} `);
        item.append(anchor);
        tree.append(item);
        if (!row.classList.contains('current')) continue;
        anchor.setAttribute('aria-current', 'page');
        const children = element('ol');
        item.append(children);
        // Chapter sections belong in the sidebar; smaller headings stay in the text.
        for (const heading of document.querySelectorAll('main h2')) {
          const permalink = heading.querySelector('.permalink-widget a');
          if (!permalink) continue;
          const tag = new URL(permalink.href).searchParams.get('name');
          if (!tag) continue;
          const child = element('li');
          const section = element('a');
          const title = heading.cloneNode(true);
          title.querySelectorAll('.permalink-widget').forEach(node => node.remove());
          section.textContent = title.textContent.trim();
          const target = new URL(link.href);
          target.hash = tag;
          section.href = target.href;
          child.append(section);
          children.append(child);
          readingSections.push({heading, link: section});
        }
      }
      splitTocs.replaceWith(tree);
      trackReadingPosition(readingSections);
    } else {
      // Prepared pages already contain this tree, including when JS is delayed.
      const sections = [...document.querySelectorAll('.book-toc-tree [aria-current="page"] + ol a')]
        .map(link => ({link, heading: document.getElementById(decodeURIComponent(new URL(link.href).hash.slice(1)))}))
        .filter(section => section.heading);
      trackReadingPosition(sections);
    }
    foldLegacyHints();
    // Plain Verso `lean` blocks have checked tactic states too, but no playground key.
    // Give them the same reading controls without creating an execution context.
    document.querySelectorAll('main .hl.lean.block').forEach(source => {
      if (source.closest('.book-example, .tactic-state, .hover-container')) return;
      const wrapper = element('div', 'book-example');
      source.before(wrapper);
      wrapper.append(source);
    });
    document.querySelectorAll('.book-example').forEach(decorate);
    if (browserLean) {
      const tree = document.querySelector('.book-toc-tree');
      if (tree) startExerciseProgress(tree);
      window.addEventListener('hashchange', openLinkedExercise);
      const reopen = sessionStorage.getItem('lean-algebra.reopen');
      sessionStorage.removeItem('lean-algebra.reopen');
      if (!openLinkedExercise() && reopen) openEditors.get(reopen)?.();
    }
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', start);
  else start();
})();
