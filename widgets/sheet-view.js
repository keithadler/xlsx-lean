// The sheets as a reader sees them, and what each cell is underneath: how it is stored,
// the XML Lean writes for it, and the shared string it points into. All data comes from Lean.
import * as React from 'react';
const h = React.createElement;

const fg = 'var(--vscode-editor-foreground, currentColor)';
const mono = 'var(--vscode-editor-font-family, ui-monospace, Menlo, monospace)';
const muted = { opacity: 0.65 };
const TEAL = '#0d9488', GREEN = '#16a34a', BLUE = '#2563eb', AMBER = '#d97706';
const KIND = {
  shared: { color: TEAL, label: 'shared string' },
  inline: { color: AMBER, label: 'inline string' },
  number: { color: BLUE, label: 'number' },
  bool:   { color: '#9333ea', label: 'boolean' },
};
const grid = 'rgba(127,127,127,0.28)';

function Grid({ sheet, sel, setSel, sstHover }) {
  const byRef = {};
  for (const c of sheet.cells) byRef[c.ref] = c;
  const head = { background: 'rgba(127,127,127,0.10)', fontWeight: 500, fontSize: 11, textAlign: 'center', padding: '3px 6px', border: `1px solid ${grid}`, ...muted };
  const rows = [];
  for (let r = 1; r < sheet.rows + 1; r++) {
    rows.push(h('tr', { key: r },
      h('td', { style: { ...head, minWidth: 26 } }, r),
      ...sheet.cols.map((col, ci) => {
        const ref = col + r, c = byRef[ref];
        const isSel = sel && sel.ref === ref;
        const lit = c && c.kind === 'shared' && sstHover !== null && +c.raw === sstHover;
        const k = c ? KIND[c.kind] : null;
        return h('td', {
          key: ref, onMouseEnter: () => c && setSel(c),
          style: {
            border: `1px solid ${grid}`, padding: '4px 8px', fontSize: 12.5, whiteSpace: 'nowrap',
            maxWidth: 300, overflow: 'hidden', textOverflow: 'ellipsis', position: 'relative',
            textAlign: c && (c.value.kind === 'number') ? 'right' : c && c.value.kind === 'bool' ? 'center' : 'left',
            fontWeight: c && c.style === 1 ? 700 : 400,
            background: lit ? TEAL + '33' : isSel ? 'rgba(37,99,235,0.14)' : 'transparent',
            outline: isSel ? `2px solid ${BLUE}` : 'none', outlineOffset: -2, cursor: c ? 'pointer' : 'default',
          } },
          c ? c.value.text : '',
          k ? h('span', { title: k.label, style: { position: 'absolute', top: 0, right: 0, width: 0, height: 0, borderTop: `7px solid ${k.color}`, borderLeft: '7px solid transparent' } }) : null);
      })));
  }
  return h('table', { style: { borderCollapse: 'collapse', fontFamily: 'var(--vscode-font-family, system-ui, sans-serif)' } },
    h('thead', null, h('tr', null, h('th', { style: head }), ...sheet.cols.map(c => h('th', { key: c, style: { ...head, minWidth: 60 } }, c)))),
    h('tbody', null, ...rows));
}

function Inspector({ c, sst }) {
  if (!c) return h('div', { style: { fontSize: 12, ...muted } }, 'Point at a cell.');
  const k = KIND[c.kind];
  const row = (label, content) => h('div', { style: { display: 'flex', gap: 10, padding: '3px 0', fontSize: 12 } },
    h('div', { style: { minWidth: 72, ...muted } }, label), h('div', { style: { flex: 1, minWidth: 0 } }, content));
  return h('div', null,
    h('div', { style: { display: 'flex', alignItems: 'baseline', gap: 10, marginBottom: 6 } },
      h('span', { style: { fontFamily: mono, fontSize: 18, fontWeight: 700 } }, c.ref),
      h('span', { style: { fontSize: 11, ...muted } }, `column ${c.col}, row ${c.row}`)),
    row('stored as', h('span', null, h('span', { style: { color: k.color, fontWeight: 600 } }, k.label),
      c.kind === 'shared' ? h('span', { style: { fontFamily: mono } }, `  index ${c.raw}`) : null)),
    c.kind === 'shared' ? row('looks up', h('span', { style: { fontFamily: mono } },
      `sst[${c.raw}] = "${sst[+c.raw]}"`)) : null,
    row('reads as', h('span', { style: { fontWeight: 600 } }, c.value.text, h('span', { style: { fontWeight: 400, ...muted } }, `  (${c.value.kind})`))),
    row('format', c.style === 0 ? 'default (cellXfs 0)' : `bold (cellXfs ${c.style})`),
    row('XML', h('code', { style: { fontFamily: mono, fontSize: 11, wordBreak: 'break-all', display: 'block', background: 'rgba(127,127,127,0.10)', padding: '5px 7px', borderRadius: 5 } }, c.xml)));
}

export default function SheetView(props) {
  const [tab, setTab] = React.useState(0);
  const [sel, setSel] = React.useState(null);
  const [sstHover, setSstHover] = React.useState(null);
  const sheet = props.sheets[Math.min(tab, props.sheets.length - 1)];
  const used = new Set();
  for (const s of props.sheets) for (const c of s.cells) if (c.kind === 'shared') used.add(+c.raw);
  const box = { border: '1px solid rgba(127,127,127,0.25)', borderRadius: 10, padding: 12 };
  const counts = {};
  for (const c of sheet.cells) counts[c.kind] = (counts[c.kind] || 0) + 1;
  const pointed = sel && sel.kind === 'shared' ? +sel.raw : null;
  return h('div', { style: { fontFamily: 'var(--vscode-font-family, system-ui, sans-serif)', color: fg, display: 'flex', flexDirection: 'column', gap: 10 } },
    h('div', { style: { display: 'flex', alignItems: 'baseline', gap: 12, flexWrap: 'wrap' } },
      h('div', { style: { fontSize: 15, fontWeight: 700 } }, 'example.xlsx, as a reader sees it'),
      h('div', { style: { fontSize: 12, color: props.check ? GREEN : '#dc2626' } },
        props.check ? '✓ Workbook.check = true, so Workbook.WellFormed' : '✗ Workbook.check = false')),
    h('div', { style: { display: 'flex', gap: 10, flexWrap: 'wrap', alignItems: 'flex-start' } },
      h('div', { style: { ...box, flex: '1 1 440px', minWidth: 0 } },
        h('div', { style: { display: 'flex', justifyContent: 'space-between', fontSize: 11, marginBottom: 8, ...muted } },
          h('span', { style: { fontFamily: mono } }, '/' + sheet.entry),
          h('span', null, Object.entries(counts).map(([k, v]) => `${v} ${KIND[k].label}`).join(' · '))),
        h('div', { style: { overflowX: 'auto' }, onMouseLeave: () => setSstHover(null) }, h(Grid, { sheet, sel, setSel, sstHover })),
        h('div', { style: { display: 'flex', gap: 2, marginTop: 8, borderTop: `1px solid ${grid}` } },
          ...props.sheets.map((s, i) => h('button', { key: s.name, onClick: () => { setTab(i); setSel(null); },
            style: { border: 'none', borderBottom: i === tab ? `2px solid ${GREEN}` : '2px solid transparent', background: i === tab ? 'rgba(22,163,74,0.10)' : 'transparent',
              color: fg, padding: '5px 12px', fontSize: 12, fontWeight: i === tab ? 700 : 400, cursor: 'pointer', borderRadius: '0 0 6px 6px' } },
            s.name, s.ok ? h('span', { style: { color: GREEN, marginLeft: 6 } }, '✓') : null))),
        h('div', { style: { display: 'flex', gap: 14, marginTop: 10, fontSize: 11, flexWrap: 'wrap' } },
          ...Object.entries(KIND).map(([k, v]) => h('span', { key: k, style: { display: 'inline-flex', alignItems: 'center', gap: 5 } },
            h('span', { style: { width: 0, height: 0, borderTop: `8px solid ${v.color}`, borderLeft: '8px solid transparent' } }), v.label)),
          h('span', { style: muted }, 'Rows sorted, one cell per reference: Sheet.WellFormed.refs_nodup.'))),
      h('div', { style: { display: 'flex', flexDirection: 'column', gap: 10, flex: '1 1 300px', minWidth: 260 } },
        h('div', { style: box }, h(Inspector, { c: sel, sst: props.sst })),
        h('div', { style: box },
          h('div', { style: { display: 'flex', justifyContent: 'space-between', marginBottom: 6 } },
            h('span', { style: { fontWeight: 600, fontSize: 12.5 } }, 'Shared strings'),
            h('span', { style: { fontFamily: mono, fontSize: 11, ...muted } }, '/xl/sharedStrings.xml')),
          ...props.sst.map((s, i) => h('div', { key: i, onMouseEnter: () => setSstHover(i), onMouseLeave: () => setSstHover(null),
              style: { display: 'flex', gap: 8, fontSize: 11.5, padding: '2px 6px', borderRadius: 4, cursor: 'default',
                background: pointed === i || sstHover === i ? TEAL + '2e' : 'transparent', opacity: used.has(i) ? 1 : 0.5 } },
            h('span', { style: { fontFamily: mono, minWidth: 22, textAlign: 'right', color: TEAL, fontWeight: 600 } }, i),
            h('span', { style: { overflow: 'hidden', textOverflow: 'ellipsis', whiteSpace: 'nowrap' } }, s))),
          h('div', { style: { fontSize: 11, marginTop: 6, lineHeight: 1.45, ...muted } },
            'Every index a cell stores is in range, so no cell reads #REF!: Cell.WellFormed.resolves. Point at a string to light up the cells that use it.')))));
}
