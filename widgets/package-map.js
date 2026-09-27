// The package map: every entry of the archive, how it gets its content type, and every
// relationship, laid out by how far it is from the package. All data comes from Lean.
import * as React from 'react';
import { useRpcSession } from '@leanprover/infoview';
const h = React.createElement;

const ROLE = {
  package:       { color: '#64748b', label: 'package' },
  workbook:      { color: '#2563eb', label: 'workbook' },
  worksheet:     { color: '#16a34a', label: 'worksheet' },
  styles:        { color: '#9333ea', label: 'styles' },
  sharedStrings: { color: '#0d9488', label: 'shared strings' },
  rels:          { color: '#d97706', label: 'relationships' },
  types:         { color: '#64748b', label: 'content types' },
  other:         { color: '#64748b', label: 'other' },
  untyped:       { color: '#dc2626', label: 'NO CONTENT TYPE' },
};
const REL_COLOR = {
  officeDocument: '#2563eb', worksheet: '#16a34a', styles: '#9333ea',
  sharedStrings: '#0d9488',
};
const fg = 'var(--vscode-editor-foreground, currentColor)';
const muted = { opacity: 0.65 };
const mono = 'var(--vscode-editor-font-family, ui-monospace, Menlo, monospace)';

function fileName(entry) { const i = entry.lastIndexOf('/'); return i < 0 ? entry : entry.slice(i + 1); }
function folder(entry) { const i = entry.lastIndexOf('/'); return i < 0 ? '' : entry.slice(0, i + 1); }

// Depth of each entry by breadth-first search from the package, over relationships.
function layers(pkg) {
  const edges = [];
  for (const g of pkg.rels) for (const r of g.items) edges.push({ from: g.source, to: r.target, rel: r, rels: g.relsPart });
  const depth = { package: 0 };
  let frontier = ['package'];
  while (frontier.length) {
    const next = [];
    for (const f of frontier) for (const e of edges) if (e.from === f && depth[e.to] === undefined) {
      depth[e.to] = depth[f] + 1; next.push(e.to);
    }
    frontier = next;
  }
  return { edges, depth };
}

function Node({ x, y, w, hgt, role, title, sub, active, dim, onEnter, onLeave }) {
  const c = (ROLE[role] || ROLE.other).color;
  return h('g', { onMouseEnter: onEnter, onMouseLeave: onLeave, style: { cursor: 'default', opacity: dim ? 0.35 : 1, transition: 'opacity 120ms' } },
    h('rect', { x, y, width: w, height: hgt, rx: 7, fill: c, fillOpacity: active ? 0.28 : 0.13, stroke: c, strokeWidth: active ? 2.2 : 1.2 }),
    h('rect', { x, y, width: 5, height: hgt, rx: 2, fill: c }),
    h('text', { x: x + 13, y: y + (sub ? 15 : hgt / 2 + 4), fontSize: 12.5, fontWeight: 600, fill: fg, fontFamily: mono }, title),
    sub ? h('text', { x: x + 13, y: y + 29, fontSize: 10.5, fill: fg, style: muted, fontFamily: mono }, sub) : null);
}

function Graph({ pkg, hover, setHover }) {
  const { edges, depth } = layers(pkg);
  const parts = pkg.parts.filter(p => p.role !== 'rels');
  const relsParts = pkg.parts.filter(p => p.role === 'rels');
  const cols = [[{ entry: 'package', role: 'package' }]];
  const unreachable = [];
  for (const p of parts) {
    const d = depth[p.entry];
    if (d === undefined) { unreachable.push(p); continue; }
    (cols[d] = cols[d] || []).push(p);
  }
  if (unreachable.length) cols.push(unreachable);
  const W = 190, H = 38, GAPX = 110, GAPY = 16, TAG = 22;
  // Each node that has relationships carries its .rels part as a tag underneath.
  const relsOf = {};
  for (const g of pkg.rels) relsOf[g.source] = g.relsPart;
  const pos = {};
  let height = 0;
  cols.forEach((col, ci) => {
    let y = 34;
    col.forEach(p => {
      pos[p.entry] = { x: 16 + ci * (W + GAPX), y };
      y += H + GAPY + (relsOf[p.entry] ? TAG + 6 : 0);
    });
    height = Math.max(height, y);
  });
  const width = 16 + cols.length * (W + GAPX) - GAPX + 16;
  const related = new Set();
  if (hover) {
    related.add(hover);
    for (const e of edges) {
      if (e.from === hover) related.add(e.to);
      if (e.to === hover) related.add(e.from);
      if (e.rels === hover) { related.add(e.from); related.add(e.to); }
    }
    for (const g of pkg.rels) if (g.source === hover) related.add(g.relsPart);
  }
  const dim = key => hover && !related.has(key);
  const heads = ['the package', 'found from /_rels/.rels', 'found from the workbook', 'deeper'];
  return h('svg', { width, height: height + 8, style: { display: 'block', maxWidth: '100%', overflow: 'visible' }, viewBox: `0 0 ${width} ${height + 8}` },
    h('defs', null, ...Object.entries(REL_COLOR).map(([k, c]) =>
      h('marker', { key: k, id: `arrow-${k}`, viewBox: '0 0 10 10', refX: 9, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto-start-reverse' },
        h('path', { d: 'M 0 0 L 10 5 L 0 10 z', fill: c })))),
    ...cols.map((col, ci) => h('text', { key: 'head' + ci, x: 16 + ci * (W + GAPX), y: 16, fontSize: 11, fill: fg, style: muted, letterSpacing: 0.3 },
      ci === cols.length - 1 && unreachable.length ? 'UNREACHABLE' : (heads[ci] || heads[3]).toUpperCase())),
    ...edges.map((e, i) => {
      const a = pos[e.from], b = pos[e.to];
      if (!a || !b) return null;
      const x1 = a.x + W, y1 = a.y + H / 2, x2 = b.x - 2, y2 = b.y + H / 2;
      const mx = (x1 + x2) / 2;
      const c = REL_COLOR[e.rel.type] || '#64748b';
      const on = hover && (hover === e.from || hover === e.to || hover === e.rels);
      return h('g', { key: 'e' + i, style: { opacity: hover && !on ? 0.15 : 1, transition: 'opacity 120ms' } },
        h('path', { d: `M ${x1} ${y1} C ${mx} ${y1}, ${mx} ${y2}, ${x2} ${y2}`, fill: 'none', stroke: c, strokeWidth: on ? 2.4 : 1.4, markerEnd: `url(#arrow-${e.rel.type})` }),
        h('text', { x: x2 - 10, y: y2 - 6, fontSize: 10, textAnchor: 'end', fill: c, fontFamily: mono, fontWeight: 600 }, e.rel.id));
    }),
    ...cols.flatMap((col, ci) => col.flatMap(p => {
      const { x, y } = pos[p.entry];
      const isPkg = p.entry === 'package';
      const out = [h(Node, {
        key: p.entry, x, y, w: W, hgt: H, role: p.role,
        title: isPkg ? 'example.xlsx' : fileName(p.entry),
        sub: isPkg ? 'the ZIP archive itself' : '/' + folder(p.entry),
        active: hover === p.entry, dim: dim(p.entry),
        onEnter: () => setHover(p.entry), onLeave: () => setHover(null) })];
      const rp = relsOf[p.entry];
      if (rp) {
        const c = ROLE.rels.color;
        out.push(h('g', { key: rp, onMouseEnter: () => setHover(rp), onMouseLeave: () => setHover(null), style: { opacity: dim(rp) ? 0.35 : 1 } },
          h('path', { d: `M ${x + 14} ${y + H} L ${x + 14} ${y + H + 6 + TAG / 2} L ${x + 22} ${y + H + 6 + TAG / 2}`, stroke: c, fill: 'none', strokeDasharray: '2 2' }),
          h('rect', { x: x + 22, y: y + H + 6, width: W - 22, height: TAG, rx: 5, fill: c, fillOpacity: hover === rp ? 0.3 : 0.12, stroke: c, strokeWidth: 1 }),
          h('text', { x: x + 30, y: y + H + 6 + 15, fontSize: 10.5, fill: fg, fontFamily: mono }, '/' + rp)));
      }
      return out;
    })));
}

function TypesTable({ pkg, hover, setHover }) {
  const rows = [{ entry: '[Content_Types].xml', role: 'types', contentType: '(not a part: it types the others)', via: '' }]
    .concat(pkg.parts);
  const cell = { padding: '3px 10px 3px 0', verticalAlign: 'top' };
  return h('table', { style: { borderCollapse: 'collapse', fontSize: 11.5, width: '100%' } },
    h('thead', null, h('tr', { style: { textAlign: 'left', ...muted } },
      h('th', { style: cell }, 'Entry'), h('th', { style: cell }, 'Content type'), h('th', { style: cell }, 'From'))),
    h('tbody', null, ...rows.map(p => {
      const c = (ROLE[p.role] || ROLE.other).color;
      const on = hover === p.entry;
      return h('tr', { key: p.entry, onMouseEnter: () => setHover(p.entry), onMouseLeave: () => setHover(null),
          style: { background: on ? c + '22' : 'transparent', opacity: hover && !on ? 0.55 : 1 } },
        h('td', { style: { ...cell, fontFamily: mono, whiteSpace: 'nowrap' } },
          h('span', { style: { display: 'inline-block', width: 8, height: 8, borderRadius: 2, background: c, marginRight: 7 } }), p.entry),
        h('td', { style: { ...cell, fontFamily: mono, wordBreak: 'break-all', color: p.contentType ? undefined : '#dc2626' } },
          p.contentType ? p.contentType.replace('application/vnd.openxmlformats-', '…') : 'none'),
        h('td', { style: { ...cell, whiteSpace: 'nowrap' } }, p.via));
    })));
}

const RULES = [
  ['names_unique', 'no two entries share a name, ignoring case'],
  ['typed', 'every entry has a content type'],
  ['sources_exist', 'relationships come from real parts'],
  ['targets_exist', 'every relationship lands on a part'],
  ['ids_unique', 'relationship ids unique per .rels'],
  ['one_main', 'exactly one main document'],
];

export default function PackageMap(props) {
  const rs = useRpcSession();
  const [pkg, setPkg] = React.useState(props);
  const [n, setN] = React.useState(null);
  const [hover, setHover] = React.useState(null);
  const [err, setErr] = React.useState(null);
  React.useEffect(() => { setPkg(props); setN(null); }, [props]);
  const sheets = pkg.parts.filter(p => p.role === 'worksheet').length;
  const ask = k => {
    setN(k);
    rs.call('Xlsx.Visuals.layoutRpc', { n: k }).then(setPkg).catch(e => setErr(String(e && e.message || e)));
  };
  const box = { border: '1px solid rgba(127,127,127,0.25)', borderRadius: 10, padding: 12 };
  return h('div', { style: { fontFamily: 'var(--vscode-font-family, system-ui, sans-serif)', color: fg, display: 'flex', flexDirection: 'column', gap: 10 } },
    h('div', { style: { display: 'flex', alignItems: 'baseline', gap: 12, flexWrap: 'wrap' } },
      h('div', { style: { fontSize: 15, fontWeight: 700 } }, pkg.title),
      h('div', { style: { fontSize: 12, ...muted } }, `${pkg.parts.length + 1} ZIP entries · ${pkg.rels.reduce((a, g) => a + g.items.length, 0)} relationships`)),
    h('div', { style: { ...box, display: 'flex', alignItems: 'center', gap: 10, fontSize: 12 } },
      h('span', null, 'Sheets'),
      h('input', { type: 'range', min: 1, max: 12, value: n ?? sheets, onChange: e => ask(+e.target.value), style: { flex: '0 1 220px' } }),
      h('b', { style: { minWidth: 18 } }, n ?? sheets),
      h('span', { style: muted }, n === null ? 'drag to lay out a workbook with more sheets: Lean computes each layout' : 'laid out by Lean: Workbook.toPackage, i.e. layout ' + n)),
    err ? h('div', { style: { color: '#dc2626', fontSize: 12 } }, err) : null,
    h('div', { style: { ...box, overflowX: 'auto' } }, h(Graph, { pkg, hover, setHover })),
    h('div', { style: { display: 'flex', gap: 10, flexWrap: 'wrap' } },
      h('div', { style: { ...box, flex: '1 1 380px' } },
        h('div', { style: { fontWeight: 600, fontSize: 12.5, marginBottom: 6 } }, '[Content_Types].xml, resolved'),
        h(TypesTable, { pkg, hover, setHover }),
        h('div', { style: { fontSize: 11, marginTop: 6, ...muted } },
          'Defaults: ', pkg.defaults.map(d => `.${d.ext}`).join(', '), '. An Override names one part; a Default covers an extension.')),
      h('div', { style: { ...box, flex: '1 1 260px' } },
        h('div', { style: { fontWeight: 600, fontSize: 12.5, marginBottom: 6 } },
          pkg.check ? '✓ Package.check = true' : '✗ Package.check = false'),
        ...RULES.map(([k, t]) => h('div', { key: k, style: { display: 'flex', gap: 8, fontSize: 11.5, padding: '2px 0' } },
          h('span', { style: { color: pkg.check ? '#16a34a' : '#dc2626', fontWeight: 700 } }, pkg.check ? '✓' : '?'),
          h('span', { style: { fontFamily: mono, minWidth: 104 } }, k), h('span', { style: muted }, t))),
        h('div', { style: { display: 'flex', gap: 8, fontSize: 11.5, padding: '6px 0 2px', borderTop: '1px solid rgba(127,127,127,0.2)', marginTop: 6 } },
          h('span', { style: { color: pkg.conforms ? '#16a34a' : '#dc2626', fontWeight: 700 } }, pkg.conforms ? '✓' : '✗'),
          h('span', { style: { fontFamily: mono, minWidth: 104 } }, 'conformsCheck'), h('span', { style: muted }, 'main document is a workbook; one typed worksheet per sheet')),
        h('div', { style: { display: 'flex', gap: 8, fontSize: 11.5, padding: '2px 0' } },
          h('span', { style: { color: pkg.orphans ? '#16a34a' : '#d97706', fontWeight: 700 } }, pkg.orphans ? '✓' : '!'),
          h('span', { style: { fontFamily: mono, minWidth: 104 } }, 'NoOrphans'), h('span', { style: muted }, 'writer rule: every part reachable (readers ignore orphans, §9.1.4)')),
        h('div', { style: { fontSize: 11, marginTop: 8, lineHeight: 1.45, ...muted } },
          'Package.check_sound turns this run into a proof of WellFormed. ',
          'Workbook.toPackage_wellFormed proves it for every number of sheets at once, with no run at all.'))));
}
