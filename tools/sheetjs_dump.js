// Read each .xlsx named on the command line with SheetJS and print what it saw as JSON lines.
const XLSX = require('xlsx');
// SheetJS builds dates in local time, so read them back in local time.
const p2 = n => String(n).padStart(2, '0');
function localIso(d) {
  const day = `${d.getFullYear()}-${p2(d.getMonth() + 1)}-${p2(d.getDate())}`;
  const t = d.getHours() * 3600 + d.getMinutes() * 60 + d.getSeconds();
  return t === 0 ? day : `${day}T${p2(d.getHours())}:${p2(d.getMinutes())}:${p2(d.getSeconds())}`;
}
for (const path of process.argv.slice(2)) {
  let out;
  try {
    const wb = XLSX.readFile(path, { cellFormula: false, cellHTML: false, cellText: false, cellDates: true });
    const names = ((wb.Workbook || {}).Names || []).map(n => n.Name);
    out = { path, names, sheets: wb.SheetNames.map(name => {
      const ws = wb.Sheets[name];
      const cells = {};
      for (const k of Object.keys(ws)) if (k[0] !== '!') {
        const v = ws[k].v;
        cells[k] = { t: ws[k].t, v: v instanceof Date ? localIso(v) : v };
      }
      return { name, cells };
    }) };
  } catch (e) {
    out = { path, error: String(e && e.message || e).slice(0, 300) };
  }
  process.stdout.write(JSON.stringify(out) + '\n');
}
