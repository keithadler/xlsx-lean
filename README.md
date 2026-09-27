# xlsx-lean

**The XLSX file format, as a Lean proof.** A model of what is inside an `.xlsx` file (the package, its content types and relationships, the workbook, sheets, rows, cells and shared strings), the rules a reader needs, checkers for those rules proved sound, and one theorem about every workbook at once:

> **Every workbook, with any number of sheets, lays out as a well-formed package**, and follows the SpreadsheetML rules on top of that.

Lean writes real `.xlsx` files from the model, the same files open in openpyxl, calamine, SheetJS and macOS Quick Look, and the pictures below are drawn from the model inside [Lean Studio](https://github.com/keithadler/leanstudio). The spec was then attacked with 342 hostile files and four independent readers. That turned up a crash in one reader, silent data loss in another, three gaps in the first version of the spec, and one rule that was stricter than the standard. All four are fixed and proved.

![The package of example.xlsx, drawn in Lean Studio's infoview from Workbook.toPackage](docs/images/package-map.png)

As far as I could find, nobody has formalized XLSX before. The nearest work: [EtherCalc](https://github.com/audreyt/ethercalc) has a generated Lean model of the column-letter codec (its integer steps, checked in Dafny), and [lean-zip](https://github.com/kim-em/lean-zip) proves DEFLATE correct, with [lean-archive](https://github.com/kim-em/lean-archive) reading and writing ZIP on top. Neither looks inside the archive.

## What is proved

Everything is plain Lean 4 (v4.34.0) with no dependencies: no Mathlib, no `sorry`, no `native_decide`. The main theorems rest on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and the concrete limits such as `colName_maxCol` on none at all. [Tenet](https://github.com/keithadler/tenet), an independent implementation of Lean's kernel, re-checks every declaration: **976 checked, 0 failed.**

| Theorem | What it says |
|---|---|
| [`Workbook.toPackage_wellFormed`](Xlsx/Build.lean#L237) | For **every** workbook: no two entries share a name (ignoring case, as OPC requires), every entry has a content type, every relationship comes from a real part and lands on one, relationship ids are unique, and there is exactly one main document. |
| [`Workbook.toPackage_conforms`](Xlsx/Build.lean#L326) | The main document is typed as a workbook, and there is one worksheet relationship per sheet, each landing on a part typed as a worksheet. |
| [`Workbook.toPackage_noOrphans`](Xlsx/Build.lean#L257) | Every part can be reached by following relationships from the package. |
| [`Package.check_sound`](Xlsx/Package.lean#L258), [`conformsCheck_sound`](Xlsx/Build.lean#L287), [`Workbook.check_sound`](Xlsx/Workbook.lean#L275) | The checkers that run are sound: a package or workbook they accept follows every rule. |
| [`Cell.WellFormed.resolves`](Xlsx/Workbook.lean#L146) | In a well-formed workbook every cell has a value: no shared string index dangles. |
| [`Sheet.WellFormed.refs_nodup`](Xlsx/Workbook.lean#L190) | No two cells of a well-formed sheet have the same reference, so "the cell at B7" always means one cell. |
| [`decodeCol_encodeCol`](Xlsx/CellRef.lean#L61), [`encodeCol_decodeCol`](Xlsx/CellRef.lean#L72) | Column names (`A` … `Z`, `AA` …) are *bijective* base 26: every number has one name and every string of capitals is some column. |
| [`parseA1_toA1`](Xlsx/CellRef.lean#L311), [`toA1_injective`](Xlsx/CellRef.lean#L324) | Every cell reference reads back from its A1 form, and two cells never share a name. |
| [`colName_maxCol`](Xlsx/CellRef.lean#L164), [`toA1_last`](Xlsx/CellRef.lean#L331) | Column 16384 is `XFD`, and the last cell of every sheet is `XFD1048576`. |
| [`example_wellFormed`](Xlsx/Example.lean#L50) | The example workbook follows every rule, checked by the kernel running the checker. |

## The rules, and where each comes from

A rule is only as good as its source, so every rule in the spec says where it comes from.

- **ECMA-376 (the standard):** part names unique without regard to ASCII case (Part 2), content types from Defaults and Overrides, relationships that resolve, one main document, and shared-string and style indices in range.
- **XML:** text may only contain characters XML 1.0 can carry. U+0001 or U+FFFE cannot appear in an XML file at all, escaped or not.
- **Excel's published limits,** which a file meant for Excel has to respect even where the standard is silent: 16,384 columns and 1,048,576 rows, at most 32,767 characters in a cell, and 15 significant digits in a number. Sheet names must be unique without regard to case, 1 to 31 UTF-16 units long, contain none of `[ ] : * ? / \`, not start or end with an apostrophe, and not be `History`.

## The adversarial test

`lake exe xlsxgen lab out/lab` writes 342 files with the same writer as the example, and records our verdict and the model's value for every cell. [`tools/differential.py`](tools/differential.py) then reads every file with four readers from independent code bases: a strict XML parser (expat), openpyxl (Python), calamine (Rust) and SheetJS (JavaScript). It compares each against the model, cell by cell. The corpus has three kinds of file:

- **21 broken files**, each breaking one rule on purpose. Our checkers must reject every one, and they do.
- **21 probes** aimed where a spec like this is usually too weak.
- **300 random well-formed workbooks.**

### What it found in the readers

| File | What happened |
|---|---|
| a shared string index past the end of the table | **calamine crashes** (a Rust panic: index out of bounds); openpyxl and SheetJS refuse the file |
| a worksheet relationship to a part that is not there | **openpyxl silently drops the sheet** and opens the rest |
| cell A1 written twice, with 1 then 2 | **all three readers silently keep the second value** |
| two sheets named `Limits` and `LIMITS` | **openpyxl renames one to `LIMITS1`** |
| a sheet with an empty name | openpyxl renames it `Sheet` |
| the integer 2^53 + 1 | calamine and SheetJS read 2^53; 10^400 becomes `inf` or nothing |
| an empty shared string | calamine reads it as an empty cell, in 170 of the 300 random workbooks too |

Of the 21 broken files, the readers accepted 11 without any complaint. These include a column past `XFD`, a 32-character sheet name, a workbook with no sheets, two main documents, a part with no content type, and two part names that differ only in case. The full table is in [docs/adversarial/report.txt](docs/adversarial/report.txt).

### What it found in the spec

The point of attacking your own spec is that it finds your own mistakes. The first version had four:

1. **Characters XML cannot carry** (U+0001, U+FFFE) were allowed. expat and openpyxl refuse such a file outright. Now text must be XML characters.
2. **Integers were unbounded.** Readers that use doubles silently round past 2^53. Now numbers keep Excel's 15 digits.
3. **Excel's own limits were missing:** 32,767 characters of text, and sheet names measured in UTF-16 units, so 16 emoji make 32 units, not 16 characters. `History` and names starting with an apostrophe are refused too.
4. **One rule was stricter than the standard.** Version 1 required every part to be reachable. ECMA-376 Part 1 §9.1.4 tells readers to ignore parts they cannot place, so an orphan part does not make a file unreadable. Reachability is now a separate writer rule ([`NoOrphans`](Xlsx/Package.lean)), still proved for every layout.

Reading the standard again for (4) found a fifth: OPC compares part names without regard to ASCII case, so `/xl/workbook.xml` and `/xl/Workbook.xml` are the same name. Version 1 compared them exactly; now the spec compares case-folded names, and the layout theorem proves sheet names stay distinct under folding.

The corpus also caught a bug in the XML writer, which is outside the proofs: a carriage return in text came back from openpyxl as a line feed, because XML parsers normalize line endings. The writer now writes CR as `&#13;`, and tab and LF in attribute values as character references.

With spec v2, all 342 verdicts are as expected: the 21 broken files and 9 more the first spec let through are rejected, and all 312 valid files are accepted. Across the 300 random workbooks, expat, openpyxl and SheetJS agree with the model on every cell. calamine's only disagreements are the empty strings above.

## Pictures, in Lean Studio

`Xlsx/Visuals.lean` has three infoview widgets. Put the cursor on a `#widget` line and Lean Studio's **Infoview** tab draws it (VS Code's infoview works too). The JavaScript only draws: the data comes from the functions the theorems are about, and the controls call back into Lean over RPC.

**The package.** Every entry of the archive, how it gets its content type, and every relationship, laid out by distance from the package. Drag the slider and Lean lays out a workbook with more sheets.

![The package map for a workbook with five sheets](docs/images/package-map-5-sheets.png)

**The sheets as a reader sees them.** Point at a cell to see how it is stored, the XML Lean writes for it, and the shared string it points into.

![The sheet view](docs/images/sheet-view.png)

**Column names.** Type any number and Lean's own `colName` answers, with each step of the bijective base-26 encoding and the fold that reads it back.

![The column explorer on 16384 = XFD](docs/images/columns-xfd.png)

**Tenet's verdicts** on each declaration, in the gutter and the Tenet panel, after **Build**:

![Tenet checked 593 declarations: 593 verified, 0 resting on sorry or an axiom, 0 rejected](docs/images/tenet-verdicts.png)

**The Project Map:** 533 declarations and 2,202 uses between them, every one fully proved.

![The project map](docs/images/project-map.png)

## Running it

You need [elan](https://github.com/leanprover/elan); the toolchain is pinned in `lean-toolchain`.

```bash
lake build
```

Write the example workbook, and open it in any spreadsheet app:

```bash
lake exe xlsxgen out/example.xlsx
```

Write the adversarial corpus. This fails if any verdict is not the expected one:

```bash
lake exe xlsxgen lab out/lab 300
```

Read the corpus with the four readers:

```bash
pip install openpyxl==3.1.5 python-calamine==0.4.0 && npm install --prefix /tmp/sheetjs xlsx@0.18.5
```

```bash
python tools/differential.py out/lab --sheetjs /tmp/sheetjs/node_modules
```

To see the pictures, open the folder in [Lean Studio](https://github.com/keithadler/leanstudio) (or VS Code with the Lean extension) and put the cursor on the `#widget` lines at the end of `Xlsx/Visuals.lean`.

## What is not proved

- **The XML and the ZIP bytes.** The theorems are about the model. `Xml.lean` renders it and `Zip.lean` writes a stored (uncompressed) archive with CRC-32, and neither is verified. The corpus tests them against four readers, which is evidence, not proof. The next step is a proof that reading back the ZIP gives the parts that were written. For compressed output, that is where lean-zip's verified DEFLATE fits.
- **The model is a subset of SpreadsheetML:** numbers, text, booleans, shared strings, and a style index. There are no formulas, dates, rich text, merged cells, tables or charts. Relationship targets are relative paths without `..`. Content type Overrides are matched exactly, not by case-folded name.
- **Lean strings are Unicode scalar values,** so the unpaired surrogates a real file can contain cannot be represented at all.
- **Excel itself was not in the loop.** Its limits come from Microsoft's published specifications, not from running Excel.

## Layout

| Path | What it is |
|---|---|
| `Xlsx/CellRef.lean` | Column names, A1 references, the limits |
| `Xlsx/Package.lean` | Open Packaging Conventions: parts, content types, relationships, the checker |
| `Xlsx/Workbook.lean` | SpreadsheetML: sheets, rows, cells, shared strings, the checker |
| `Xlsx/Build.lean` | The layout of any workbook as a package, and the theorems about it |
| `Xlsx/Example.lean` | The example workbook, checked by the kernel |
| `Xlsx/Xml.lean`, `Xlsx/Zip.lean` | The writer (not verified) |
| `Xlsx/Visuals.lean`, `widgets/` | The infoview widgets |
| `Lab/Adversarial.lean` | The adversarial corpus |
| `tools/differential.py` | Reads the corpus with four readers and compares with the model |
| `docs/adversarial/` | The last run's report and results |
| `docs/x/` | Images for posts |

## License

MIT. Created by Keith Adler, [@keithadler](https://x.com/keithadler) on X.
