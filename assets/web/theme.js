/* Apply before stylesheets/first paint. Share the preference across the portal
   and book, independently of exercise drafts and progress. */
(() => {
  'use strict';
  const key = 'lean-foundations.theme';
  const root = document.documentElement;
  const system = window.matchMedia('(prefers-color-scheme: dark)');
  const valid = value => ['system', 'light', 'dark'].includes(value);
  function read() {
    try {
      const value = localStorage.getItem(key);
      return valid(value) ? value : 'system';
    } catch { return 'system'; }
  }
  let preference = read();
  function apply() {
    root.dataset.theme = preference === 'system' ? (system.matches ? 'dark' : 'light') : preference;
    root.dataset.themePreference = preference;
    document.querySelectorAll('[data-book-theme]').forEach(select => {select.value = preference;});
  }
  apply();
  system.addEventListener('change', () => {if (preference === 'system') apply();});
  window.addEventListener('storage', event => {
    if (event.key === key || event.key === null) {preference = read(); apply();}
  });
  function connect() {
    document.querySelectorAll('[data-book-theme]').forEach(select => {
      select.value = preference;
      select.addEventListener('change', () => {
        if (!valid(select.value)) return;
        preference = select.value;
        try {
          if (preference === 'system') localStorage.removeItem(key);
          else localStorage.setItem(key, preference);
        } catch { /* The current page remains usable when storage is blocked. */ }
        apply();
      });
      select.closest('.book-theme-control').hidden = false;
    });
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', connect, {once:true});
  else connect();
})();
