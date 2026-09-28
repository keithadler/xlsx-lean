/-!
# Dates

A date in XLSX is a number whose cell format is a date format. Nothing else marks it.

* **Which formats are dates.** Built-in formats 14 to 22 and 45 to 47 are dates and
  times (ECMA-376), and so are the East Asian built-ins 27 to 36 and 50 to 58. A custom
  format is a date when, after quoted text, escaped characters and `[...]` sections are
  removed, it still has a `y`, `m`, `d`, `h` or `s`.
* **Which day a number is.** In the 1900 system, serial 1 is 1900-01-01. Excel keeps
  Lotus 1-2-3's mistake of treating 1900 as a leap year, so serial 60 is 1900-02-29, a
  day that never existed, and every serial after it is one day ahead of a plain count.
  Serial 0 is shown as 1900-01-00. In the 1904 system (a `date1904` workbook), serial
  0 is 1904-01-01 and there is no leap-year mistake.
* **How far.** Excel shows dates up to 9999-12-31: serial 2958465 in the 1900 system,
  2957003 in the 1904 system. Negative dates are not dates at all.

The civil calendar arithmetic is Howard Hinnant's `days_from_civil` and
`civil_from_days`, on proleptic Gregorian dates.
-/

namespace Xlsx.Dates

/-- Built-in number formats that show a date or a time. -/
def builtinDate (id : Nat) : Bool :=
  (14 ≤ id && id ≤ 22) || (27 ≤ id && id ≤ 36) || (45 ≤ id && id ≤ 47) || (50 ≤ id && id ≤ 58)

/-- Does a custom format code show a date or a time? -/
def customDate (code : String) : Bool := Id.run do
  let cs := code.toList
  let mut out : List Char := []
  let mut i := 0
  let arr := cs.toArray
  while i < arr.size do
    let c := arr[i]!
    if c == '"' then
      i := i + 1
      while i < arr.size && arr[i]! != '"' do i := i + 1
      i := i + 1
    else if c == '\\' || c == '_' || c == '*' then i := i + 2
    else if c == '[' then
      -- [h], [m], [s] are elapsed times; [Red] and [$-409] are not
      let start := i
      while i < arr.size && arr[i]! != ']' do i := i + 1
      let inner := String.ofList (arr.toList.drop (start + 1) |>.take (i - start - 1))
      if inner.toLower.all (fun ch => ch == 'h' || ch == 'm' || ch == 's') && !inner.isEmpty then
        out := out ++ inner.toList
      i := i + 1
    else
      out := out ++ [c.toLower]
      i := i + 1
  let s := String.ofList out
  return !(s == "general") && out.any (fun c => c == 'y' || c == 'm' || c == 'd' || c == 'h' || c == 's')

/-- Days from 1970-01-01 to a proleptic Gregorian date (Hinnant). -/
def daysFromCivil (y : Int) (m d : Nat) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := (if y ≥ 0 then y else y - 399) / 400
  let yoe := y - era * 400
  let mp : Int := if m > 2 then m - 3 else m + 9
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- The date `z` days after 1970-01-01 (Hinnant). -/
def civilFromDays (z : Int) : Int × Nat × Nat :=
  let z := z + 719468
  let era := (if z ≥ 0 then z else z - 146096) / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (if m ≤ 2 then y + 1 else y, m.toNat, d.toNat)

structure DateTime where
  year : Int
  month : Nat
  day : Nat
  seconds : Nat
  deriving DecidableEq, Repr

def pad (n w : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (w - s.length) '0') ++ s

def DateTime.iso (t : DateTime) : String :=
  let base := s!"{t.year}-{pad t.month 2}-{pad t.day 2}"
  if t.seconds == 0 then base
  else s!"{base}T{pad (t.seconds / 3600) 2}:{pad (t.seconds / 60 % 60) 2}:{pad (t.seconds % 60) 2}"

/-- The last serial Excel shows as a date. -/
def maxSerial (date1904 : Bool) : Nat := if date1904 then 2957003 else 2958465

/-- A serial given as `m × 10^e`, split into whole days and seconds (rounded to the
nearest second, as Excel shows it). `none` when it is negative. -/
def split (m e : Int) : Option (Nat × Nat) :=
  if m < 0 then none
  else if e ≥ 0 then some ((m * 10 ^ e.toNat).toNat, 0)
  else
    let den : Nat := 10 ^ (-e).toNat
    let days := m.toNat / den
    let rem := m.toNat % den
    let secs := (rem * 86400 * 2 + den) / (2 * den)
    if secs ≥ 86400 then some (days + 1, 0) else some (days, secs)

/-- The day a serial shows. The 1900 system's two odd days come back as themselves:
serial 0 is 1900-01-00 and serial 60 is 1900-02-29. -/
def toDateTime (date1904 : Bool) (days secs : Nat) : DateTime :=
  if date1904 then
    let (y, m, d) := civilFromDays (daysFromCivil 1904 1 1 + days)
    ⟨y, m, d, secs⟩
  else if days == 0 then ⟨1900, 1, 0, secs⟩
  else if days == 60 then ⟨1900, 2, 29, secs⟩
  else
    let plain := if days > 60 then days - 1 else days
    let (y, m, d) := civilFromDays (daysFromCivil 1899 12 31 + plain)
    ⟨y, m, d, secs⟩

end Xlsx.Dates
