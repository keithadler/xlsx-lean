// The verdict on a real file: which checks pass, where the rules break, and what the
// reader read but the model does not describe. All data comes from Lean.
import * as React from 'react';
const h = React.createElement;

const fg = 'var(--vscode-editor-foreground, currentColor)';
const mono = 'var(--vscode-editor-font-family, ui-monospace, Menlo, monospace)';
const muted = { opacity: 0.65 };
const GREEN = '#16a34a', RED = '#dc2626', AMBER = '#d97706', BLUE = '#2563eb';
const box = { border: '1px solid rgba(127,127,127,0.25)', borderRadius: 10, padding: 12 };

function Check({ ok, na, name, fn, what }) {
  const c = na ? 'rgba(127,127,127,0.6)' : ok === 'warn' ? AMBER : ok ? GREEN : RED;
  return h('div', { style: { display: 'flex', gap: 10, alignItems: 'baseline', padding: '5px 0', borderBottom: '1px solid rgba(127,127,127,0.12)' } },
    h('span', { style: { color: c, fontWeight: 800, width: 16, textAlign: 'center' } }, na ? '–' : ok === 'warn' ? '!' : ok ? '✓' : '✗'),
    h('span', { style: { fontWeight: 600, minWidth: 96 } }, name),
    h('span', { style: { fontFamily: mono, fontSize: 11.5, minWidth: 150, color: BLUE } }, fn),
    h('span', { style: { fontSize: 12, ...muted } }, what));
}

export default function CheckReport(p) {
  if (p.unreadable) {
    return h('div', { style: { ...box, color: fg, fontFamily: 'var(--vscode-font-family, system-ui, sans-serif)' } },
      h('div', { style: { fontWeight: 700, fontSize: 15 } }, p.path),
      h('div', { style: { color: RED, marginTop: 6 } }, '✗ unreadable: ' + p.unreadable));
  }
  const ok = p.package_check && p.conforms_check && p.workbook_check && p.reader_errors === 0;
  const byRule = {};
  for (const x of p.problems) (byRule[x.rule] = byRule[x.rule] || []).push(x);
  return h('div', { style: { fontFamily: 'var(--vscode-font-family, system-ui, sans-serif)', color: fg, display: 'flex', flexDirection: 'column', gap: 10 } },
    h('div', { style: { display: 'flex', alignItems: 'baseline', gap: 12, flexWrap: 'wrap' } },
      h('div', { style: { fontSize: 15, fontWeight: 700, fontFamily: mono } }, p.path),
      h('div', { style: { fontSize: 12, ...muted } }, p.summary)),
    h('div', { style: { ...box, borderColor: ok ? GREEN + '88' : RED + '88', background: ok ? 'rgba(22,163,74,0.07)' : 'rgba(220,38,38,0.06)' } },
      h('div', { style: { fontSize: 16, fontWeight: 800, color: ok ? GREEN : RED, marginBottom: 6 } },
        ok ? 'Follows every rule of the spec' : 'Breaks the spec'),
      h(Check, { ok: p.package_check, name: 'package', fn: 'Package.check', what: 'names, content types, relationships, one main document' }),
      h(Check, { ok: p.conforms_check, na: !p.has_main, name: 'spreadsheet', fn: 'conformsCheck', what: 'the main document is a workbook; one typed worksheet per sheet' }),
      h(Check, { ok: p.workbook_check, name: 'workbook', fn: 'Workbook.check', what: "sheets, rows, cells, merges, formats, dates, Excel's limits" }),
      h(Check, { ok: p.orphan_check ? true : 'warn', name: 'writer rule', fn: 'Package.orphanCheck', what: 'every part reachable (readers ignore orphans)' }),
      p.reader_errors ? h(Check, { ok: false, name: 'reader', fn: 'Read.load', what: `${p.reader_errors} problem(s) reading the file` }) : null,
      h('div', { style: { fontSize: 11, marginTop: 8, ...muted } }, 'The verdict comes from checkers proved sound in Lean; the list below says where.')),
    p.problems.length ? h('div', { style: box },
      h('div', { style: { fontWeight: 600, fontSize: 12.5, marginBottom: 6 } }, `Where (${p.problems.length})`),
      ...Object.entries(byRule).map(([rule, xs]) => h('div', { key: rule, style: { marginBottom: 8 } },
        h('div', { style: { fontFamily: mono, fontSize: 12, color: rule === 'NoOrphans' ? AMBER : RED, fontWeight: 700 } }, rule, h('span', { style: { ...muted, fontWeight: 400 } }, `  ${xs.length}`)),
        ...xs.slice(0, 12).map((x, i) => h('div', { key: i, style: { fontSize: 12, padding: '1px 0 1px 14px' } },
          h('span', { style: { fontFamily: mono } }, x.place), h('span', { style: muted }, '  ' + x.text))),
        xs.length > 12 ? h('div', { style: { fontSize: 11, paddingLeft: 14, ...muted } }, `… and ${xs.length - 12} more`) : null))) : null,
    p.notes.length ? h('div', { style: box },
      h('div', { style: { fontWeight: 600, fontSize: 12.5, marginBottom: 6 } }, 'Read, but not in the model'),
      ...p.notes.slice(0, 20).map((n, i) => h('div', { key: i, style: { fontSize: 12, padding: '1px 0', display: 'flex', gap: 8 } },
        h('span', { style: { color: n.severity === 'error' ? RED : n.severity === 'info' ? BLUE : AMBER, fontFamily: mono, minWidth: 86 } }, n.severity),
        h('span', { style: { fontFamily: mono } }, n.place), h('span', { style: muted }, n.text)))) : null);
}
