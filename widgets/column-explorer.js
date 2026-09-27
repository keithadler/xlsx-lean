// Column names in bijective base 26. Type any number: Lean's own colName answers over
// RPC, and parseCol reads the name back. The JavaScript only draws.
import * as React from 'react';
import { useRpcSession } from '@leanprover/infoview';
const h = React.createElement;

const fg = 'var(--vscode-editor-foreground, currentColor)';
const mono = 'var(--vscode-editor-font-family, ui-monospace, Menlo, monospace)';
const muted = { opacity: 0.65 };
const BLUE = '#2563eb', GREEN = '#16a34a', AMBER = '#d97706', RED = '#dc2626';
const box = { border: '1px solid rgba(127,127,127,0.25)', borderRadius: 10, padding: 12 };

// The bands of name lengths: 1 letter up to 26, 2 up to 702, 3 up to 18278.
const BANDS = [
  { len: 1, lo: 1, hi: 26 }, { len: 2, lo: 27, hi: 702 }, { len: 3, lo: 703, hi: 18278 }, { len: 4, lo: 18279, hi: 475254 },
];

function Bands({ n, maxCol }) {
  const W = 560, H = 58, L = Math.log10;
  const x = v => 10 + (L(v) / L(475254)) * (W - 20);
  const colors = ['#94a3b8', '#60a5fa', '#34d399', '#fbbf24'];
  return h('svg', { width: '100%', viewBox: `0 0 ${W} ${H + 24}`, style: { display: 'block', maxWidth: W } },
    ...BANDS.map((b, i) => h('g', { key: b.len },
      h('rect', { x: x(b.lo), y: 14, width: x(b.hi) - x(b.lo), height: 20, fill: colors[i], fillOpacity: 0.35, stroke: colors[i] }),
      h('text', { x: (x(b.lo) + x(b.hi)) / 2, y: 28, fontSize: 10.5, textAnchor: 'middle', fill: fg }, `${b.len} letter${b.len > 1 ? 's' : ''}`),
      h('text', { x: x(b.hi), y: 48, fontSize: 9.5, textAnchor: i === BANDS.length - 1 ? 'end' : 'middle', fill: fg, style: muted, fontFamily: mono }, b.hi))),
    h('line', { x1: x(maxCol), x2: x(maxCol), y1: 6, y2: 40, stroke: RED, strokeWidth: 2 }),
    h('text', { x: x(maxCol), y: 64, fontSize: 10, textAnchor: 'middle', fill: RED, fontWeight: 600 }, 'XFD, the last column'),
    n >= 1 && n <= 475254 ? h('g', null,
      h('circle', { cx: x(n), cy: 24, r: 5.5, fill: BLUE, stroke: 'white', strokeWidth: 1.5 }),
      h('text', { x: x(n), y: 9, fontSize: 10, textAnchor: 'middle', fill: BLUE, fontWeight: 700 }, n)) : null,
    h('text', { x: 10, y: 80, fontSize: 9.5, fill: fg, style: muted }, 'log scale. Every name of k letters exists: the bijection has no gaps (encodeCol_decodeCol).'));
}

export default function ColumnExplorer(props) {
  const rs = useRpcSession();
  const [t, setT] = React.useState(props);
  const [input, setInput] = React.useState(String(props.n));
  const [busy, setBusy] = React.useState(false);
  React.useEffect(() => { setT(props); setInput(String(props.n)); }, [props]);
  const ask = k => {
    if (!Number.isFinite(k) || k < 0) return;
    setInput(String(k)); setBusy(true);
    rs.call('Xlsx.Visuals.colTraceRpc', { n: Math.floor(k) }).then(r => { setT(r); setBusy(false); }).catch(() => setBusy(false));
  };
  const steps = t.steps; // least significant first
  const letters = steps.slice().reverse();
  const ok = t.parsed === t.n;
  const exists = t.n >= 1 && t.n <= t.maxCol;
  const presets = [[1, 'A'], [26, 'Z'], [27, 'AA'], [702, 'ZZ'], [703, 'AAA'], [16384, 'XFD'], [18278, 'ZZZ']];
  // The fold that reads the name back: ((0·26 + d₁)·26 + d₂)·26 + d₃
  let acc = 0; const fold = [];
  for (const s of letters) { const d = s.r + 1; const next = acc * 26 + d; fold.push({ acc, d, next, letter: s.letter }); acc = next; }
  return h('div', { style: { fontFamily: 'var(--vscode-font-family, system-ui, sans-serif)', color: fg, display: 'flex', flexDirection: 'column', gap: 10 } },
    h('div', { style: { display: 'flex', alignItems: 'baseline', gap: 12, flexWrap: 'wrap' } },
      h('div', { style: { fontSize: 15, fontWeight: 700 } }, 'Column names, by Lean'),
      h('div', { style: { fontSize: 12, ...muted } }, 'colName answers over RPC; parseCol reads it back')),
    h('div', { style: { ...box, display: 'flex', gap: 8, alignItems: 'center', flexWrap: 'wrap' } },
      h('input', { value: input, onChange: e => setInput(e.target.value.replace(/[^0-9]/g, '')),
        onKeyDown: e => { if (e.key === 'Enter') ask(+input); },
        style: { width: 110, fontFamily: mono, fontSize: 14, padding: '4px 8px', borderRadius: 6, border: '1px solid rgba(127,127,127,0.4)', background: 'transparent', color: fg } }),
      h('button', { onClick: () => ask(+input), style: { padding: '4px 10px', borderRadius: 6, border: `1px solid ${BLUE}`, background: BLUE, color: 'white', cursor: 'pointer', fontSize: 12 } }, busy ? '…' : 'Ask Lean'),
      h('button', { onClick: () => ask(Math.max(1, t.n - 1)), style: { padding: '4px 8px', borderRadius: 6, border: '1px solid rgba(127,127,127,0.4)', background: 'transparent', color: fg, cursor: 'pointer' } }, '−'),
      h('button', { onClick: () => ask(t.n + 1), style: { padding: '4px 8px', borderRadius: 6, border: '1px solid rgba(127,127,127,0.4)', background: 'transparent', color: fg, cursor: 'pointer' } }, '+'),
      h('span', { style: { width: 8 } }),
      ...presets.map(([k, name]) => h('button', { key: k, onClick: () => ask(k),
        style: { padding: '3px 8px', borderRadius: 999, border: '1px solid rgba(127,127,127,0.35)', background: t.n === k ? 'rgba(37,99,235,0.15)' : 'transparent', color: fg, fontFamily: mono, fontSize: 11, cursor: 'pointer' } }, name))),
    h('div', { style: { display: 'flex', gap: 10, flexWrap: 'wrap' } },
      h('div', { style: { ...box, flex: '1 1 300px', display: 'flex', flexDirection: 'column', alignItems: 'center', justifyContent: 'center', gap: 6 } },
        h('div', { style: { fontSize: 12, ...muted } }, `colName ${t.n} =`),
        h('div', { style: { display: 'flex', gap: 5 } },
          ...(t.name.length ? t.name.split('') : ['∅']).map((ch, i) => h('div', { key: i,
            style: { width: 46, height: 58, borderRadius: 8, display: 'flex', alignItems: 'center', justifyContent: 'center',
              fontFamily: mono, fontSize: 32, fontWeight: 700, background: 'rgba(37,99,235,0.12)', border: `1.5px solid ${BLUE}` } }, ch))),
        h('div', { style: { fontSize: 12, marginTop: 4, color: ok ? GREEN : RED } },
          ok ? `✓ parseCol "${t.name}" = ${t.parsed}` : t.n === 0 ? 'column 0 does not exist: it has no letters' : `✗ parseCol gave ${t.parsed}`),
        h('div', { style: { fontSize: 11.5, color: exists ? GREEN : AMBER } },
          exists ? `a real XLSX column; cell ${t.a1} names its first row` : t.n > t.maxCol ? `past XFD (${t.maxCol}): Excel stops here` : '')),
      h('div', { style: { ...box, flex: '1 1 340px' } },
        h('div', { style: { fontWeight: 600, fontSize: 12.5, marginBottom: 8 } }, 'Writing it: encodeCol, one step per letter'),
        steps.length === 0 ? h('div', { style: { fontSize: 12, ...muted } }, 'encodeCol 0 = [ ]') : null,
        ...steps.map((s, i) => h('div', { key: i, style: { display: 'flex', gap: 8, alignItems: 'center', fontFamily: mono, fontSize: 12, padding: '2px 0' } },
          h('span', { style: { minWidth: 70, textAlign: 'right' } }, s.n),
          h('span', { style: muted }, '−1 ='),
          h('span', null, `26 × ${s.q} + ${s.r}`),
          h('span', { style: muted }, '→'),
          h('span', { style: { fontWeight: 700, color: BLUE, fontSize: 14 } }, s.letter),
          i + 1 < steps.length ? h('span', { style: { ...muted, fontSize: 11 } }, `then ${s.q}`) : h('span', { style: { ...muted, fontSize: 11 } }, 'then 0: stop'))),
        h('div', { style: { fontWeight: 600, fontSize: 12.5, margin: '12px 0 6px' } }, 'Reading it back: decodeCol'),
        h('div', { style: { fontFamily: mono, fontSize: 12, lineHeight: 1.7 } },
          ...fold.map((f, i) => h('div', { key: i }, `${f.acc} × 26 + ${f.d} (${f.letter}) = `, h('b', null, f.next)))),
        h('div', { style: { fontSize: 11, marginTop: 8, ...muted } }, 'Each step undoes the other: decodeCol_encodeCol.'))),
    h('div', { style: box },
      h('div', { style: { fontWeight: 600, fontSize: 12.5, marginBottom: 4 } }, 'Where it sits'),
      h(Bands, { n: t.n, maxCol: t.maxCol }),
      h('div', { style: { display: 'flex', gap: 6, marginTop: 8, flexWrap: 'wrap' } },
        ...t.near.map(x => h('button', { key: x.n, onClick: () => ask(x.n),
          style: { fontFamily: mono, fontSize: 11.5, padding: '3px 8px', borderRadius: 6, cursor: 'pointer', color: fg,
            border: x.n === t.n ? `1.5px solid ${BLUE}` : '1px solid rgba(127,127,127,0.3)', background: x.n === t.n ? 'rgba(37,99,235,0.12)' : 'transparent' } },
          h('span', { style: muted }, x.n, ' '), h('b', null, x.name))))));
}
