import Xlsx.Visuals

/-!
# Try it on your own files

Build once with `lake build`, open this file in Lean Studio (or VS Code), and put the
cursor on a line below. The compiled `xlsxlean` reads the workbook, the proved
checkers judge it, and the infoview draws the verdict, the package and the sheets.
Paths are relative to the project folder; put your own file in and add a line.
-/

#xlsx_check "samples/openpyxl.xlsx"
#xlsx_check "samples/value-under-merge.xlsx"
#xlsx_check "samples/dates-1900.xlsx"
