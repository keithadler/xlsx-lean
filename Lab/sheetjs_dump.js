// Read each .xlsx named on the command line with SheetJS and print what it saw as JSON lines.
const XLSX = require('xlsx');
for (const path of process.argv.slice(2)) {
  let out;
  try {
    const wb = XLSX.readFile(path, { cellFormula: false, cellHTML: false, cellText: false });
    out = { path, sheets: wb.SheetNames.map(name => {
      const ws = wb.Sheets[name];
      const cells = {};
      for (const k of Object.keys(ws)) if (k[0] !== '!') cells[k] = { t: ws[k].t, v: ws[k].v };
      return { name, cells };
    }) };
  } catch (e) {
    out = { path, error: String(e && e.message || e).slice(0, 300) };
  }
  process.stdout.write(JSON.stringify(out) + '\n');
}
