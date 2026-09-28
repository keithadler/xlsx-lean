/-!
# A small XML parser

Enough XML for OOXML parts: elements, attributes, text, the five predefined entities,
character references, CDATA, comments and processing instructions. It refuses a DTD,
which OOXML forbids, and UTF-16, which no writer we know of uses for XLSX.

Two rules of XML matter for getting values right, and both are followed here:
line endings (a literal CR or CR LF in text becomes LF, while `&#13;` stays a CR) and
attribute-value normalization (a literal tab, LF or CR in an attribute becomes a space).
The adversarial corpus found the first one the hard way.

Characters XML does not allow are *not* rejected here: they are passed through, so
the spec can say which rule they break and where, instead of the parse failing.

This is runtime code. Nothing about it is proved.
-/

namespace Xlsx.Read

inductive Node where
  | elem (name : String) (attrs : Array (String × String)) (kids : Array Node)
  | text (s : String)
  deriving Inhabited, Repr

namespace Node

/-- The name without its namespace prefix: `x:row` is `row`. -/
def localName (n : String) : String :=
  match n.splitOn ":" with
  | [_, l] => l
  | _ => n

def name : Node → String
  | .elem n _ _ => localName n
  | .text _ => ""

def kids : Node → Array Node
  | .elem _ _ k => k
  | .text _ => #[]

def children (n : Node) : Array Node := n.kids.filter fun k => match k with | .elem .. => true | _ => false

/-- An attribute by local name (`r:id` is found as `id`, but a plain `id` wins). -/
def attr? (n : Node) (a : String) : Option String :=
  match n with
  | .elem _ attrs _ =>
    match attrs.find? (·.1 == a) with
    | some (_, v) => some v
    | none => (attrs.find? (fun (k, _) => localName k == a)).map (·.2)
  | .text _ => none

def child? (n : Node) (name : String) : Option Node := n.children.find? (·.name == name)

def childrenNamed (n : Node) (name : String) : Array Node := n.children.filter (·.name == name)

/-- All text below this node, in order. -/
partial def textContent : Node → String
  | .text s => s
  | .elem _ _ k => k.foldl (fun acc c => acc ++ c.textContent) ""

end Node

structure St where
  pos : Nat

abbrev P := StateT Nat (Except String)

section
variable (b : ByteArray)

@[inline] def at? (i : Nat) : Option UInt8 := if h : i < b.size then some b[i] else none

def peek : P (Option UInt8) := do return at? b (← get)

def fail {α} (msg : String) : P α := do throw s!"XML, byte {← get}: {msg}"

def isWs (c : UInt8) : Bool := c == 32 || c == 9 || c == 10 || c == 13

partial def skipWs : P Unit := do
  match ← peek b with
  | some c => if isWs c then (do modify (· + 1); skipWs) else pure ()
  | none => pure ()

/-- Does the input continue with these bytes? -/
def startsWith (i : Nat) (lit : String) : Bool :=
  let l := lit.toUTF8
  i + l.size ≤ b.size && (List.range l.size).all fun k => b[i + k]! == l[k]!

/-- Skip past the next occurrence of `lit`. -/
partial def skipPast (lit : String) : P Unit := do
  let i ← get
  if i ≥ b.size then fail s!"expected {lit}"
  else if startsWith b i lit then set (i + lit.toUTF8.size)
  else (do set (i + 1); skipPast lit)

def utf8 (c : Char) : ByteArray := String.singleton c |>.toUTF8

/-- Decode `&...;` starting at the `&`. -/
def entity : P ByteArray := do
  let start ← get
  let mut i := start + 1
  while i < b.size && b[i]! != 59 && i - start < 12 do i := i + 1
  if i ≥ b.size || b[i]! != 59 then fail "unterminated entity"
  let name := String.fromUTF8! (b.extract (start + 1) i)
  set (i + 1)
  match name with
  | "lt" => return utf8 '<'
  | "gt" => return utf8 '>'
  | "amp" => return utf8 '&'
  | "quot" => return utf8 '"'
  | "apos" => return utf8 '\''
  | _ =>
    if name.startsWith "#x" || name.startsWith "#X" then
      let hex := (name.drop 2).toString
      let v := hex.foldl (fun acc c =>
        acc * 16 + (if c.isDigit then c.toNat - 48 else if 'a' ≤ c && c ≤ 'f' then c.toNat - 87
          else if 'A' ≤ c && c ≤ 'F' then c.toNat - 55 else 0x110000)) 0
      if hex.isEmpty || v ≥ 0x110000 then fail s!"bad character reference &{name};"
      return utf8 (Char.ofNat v)
    else if name.startsWith "#" then
      match (name.drop 1).toString.toNat? with
      | some v => if v < 0x110000 then return utf8 (Char.ofNat v) else fail s!"bad character reference &{name};"
      | none => fail s!"bad character reference &{name};"
    else fail s!"unknown entity &{name};"

def toStr (bytes : ByteArray) : P String :=
  match String.fromUTF8? bytes with
  | some s => pure s
  | none => fail "text is not valid UTF-8"

partial def name : P String := do
  let start ← get
  let rec go (i : Nat) : Nat :=
    if h : i < b.size then
      let c := b[i]
      if isWs c || c == 47 || c == 62 || c == 61 || c == 60 then i else go (i + 1)
    else i
  let stop := go start
  if stop == start then fail "expected a name"
  set stop
  toStr (b.extract start stop)

/-- An attribute value, with entities decoded and literal whitespace made spaces. -/
partial def attrValue : P String := do
  let q ← peek b
  unless q == some 34 || q == some 39 do fail "expected a quoted attribute value"
  modify (· + 1)
  let rec loop (acc : ByteArray) : P ByteArray := do
    match ← peek b with
    | none => fail "unterminated attribute value"
    | some c =>
      if some c == q then (do modify (· + 1); pure acc)
      else if c == 38 then (do let e ← entity b; loop (acc ++ e))
      else if c == 9 || c == 10 || c == 13 then
        -- CR LF counts once (line-ending handling happens before normalization)
        (do modify (· + 1)
            if c == 13 && (← peek b) == some 10 then modify (· + 1)
            loop (acc.push 32))
      else (do modify (· + 1); loop (acc.push c))
  toStr (← loop ByteArray.empty)

mutual
partial def element : P Node := do
  -- at '<'
  modify (· + 1)
  let n ← name b
  let mut attrs : Array (String × String) := #[]
  repeat
    skipWs b
    match ← peek b with
    | some 47 =>
      modify (· + 1)
      unless (← peek b) == some 62 do fail "expected >"
      modify (· + 1)
      return .elem n attrs #[]
    | some 62 =>
      modify (· + 1)
      let kids ← content n
      return .elem n attrs kids
    | some _ =>
      let a ← name b
      skipWs b
      unless (← peek b) == some 61 do fail s!"expected = after {a}"
      modify (· + 1)
      skipWs b
      let v ← attrValue b
      attrs := attrs.push (a, v)
    | none => fail s!"unterminated tag <{n}"
  fail "unreachable"

partial def content (parent : String) : P (Array Node) := do
  let mut kids : Array Node := #[]
  let mut txt : ByteArray := ByteArray.empty
  repeat
    let i ← get
    match at? b i with
    | none => fail s!"<{parent}> is not closed"
    | some 60 =>
      if startsWith b i "</" then
        set (i + 2)
        let n ← name b
        skipWs b
        unless (← peek b) == some 62 do fail "expected >"
        modify (· + 1)
        unless n == parent do fail s!"</{n}> closes <{parent}>"
        if txt.size > 0 then kids := kids.push (.text (← toStr txt))
        return kids
      else if startsWith b i "<!--" then skipPast b "-->"
      else if startsWith b i "<![CDATA[" then
        set (i + 9)
        let start ← get
        skipPast b "]]>"
        let stop := (← get) - 3
        txt := txt ++ b.extract start stop
      else if startsWith b i "<?" then skipPast b "?>"
      else
        if txt.size > 0 then
          kids := kids.push (.text (← toStr txt))
          txt := ByteArray.empty
        kids := kids.push (← element)
    | some 38 => txt := txt ++ (← entity b)
    | some 13 =>
      -- a literal CR or CR LF is a line feed
      set (i + 1)
      if at? b (i + 1) == some 10 then set (i + 2)
      txt := txt.push 10
    | some c => set (i + 1); txt := txt.push c
  fail "unreachable"
end

/-- Parse a whole document: prolog, one root element, trailing misc. -/
partial def document : P Node := do
  if b.size ≥ 3 && b[0]! == 0xEF && b[1]! == 0xBB && b[2]! == 0xBF then set 3
  if b.size ≥ 2 && ((b[0]! == 0xFF && b[1]! == 0xFE) || (b[0]! == 0xFE && b[1]! == 0xFF)) then
    fail "UTF-16 XML is not supported"
  repeat
    skipWs b
    let i ← get
    if startsWith b i "<?" then skipPast b "?>"
    else if startsWith b i "<!--" then skipPast b "-->"
    else if startsWith b i "<!DOCTYPE" then fail "a DTD is not allowed in OOXML"
    else break
  unless (← peek b) == some 60 do fail "expected the root element"
  let root ← element b
  repeat
    skipWs b
    let i ← get
    if startsWith b i "<!--" then skipPast b "-->"
    else if startsWith b i "<?" then skipPast b "?>"
    else break
  unless (← get) == b.size do fail "content after the root element"
  return root

end

def parse (b : ByteArray) : Except String Node := (document b).run' 0

/-- Parse the one element that starts at `pos` (at its `<`), and say where it ends. -/
def elementAt (b : ByteArray) (pos : Nat) : Except String (Node × Nat) := (element b).run pos

/-- Where `pat` next occurs at or after `start`. -/
def indexOf (b : ByteArray) (pat : String) (start : Nat) : Option Nat := Id.run do
  let p := pat.toUTF8
  if p.size == 0 then return some start
  let mut i := start
  while i + p.size ≤ b.size do
    if b[i]! == p[0]! && startsWith b i pat then return some i
    i := i + 1
  return none

/-- The bytes between `<sheetData …>` and `</sheetData>`, as `(content start, content end)`,
if the element is there and not empty. A namespace prefix is allowed. -/
def sheetDataSpan (b : ByteArray) : Option (Nat × Nat) := Id.run do
  let mut from_ := 0
  repeat
    let some k := indexOf b "sheetData" from_ | return none
    -- a start tag: `<sheetData` or `<x:sheetData`
    let mut j := k
    while j > 0 && b[j - 1]! != 60 && b[j - 1]! != 62 && b[j - 1]! != 32 do j := j - 1
    if j > 0 && b[j - 1]! == 60 && (j == k || b[k - 1]! == 58) then
      let some gt := indexOf b ">" k | return none
      if gt > 0 && b[gt - 1]! == 47 then return none   -- `<sheetData/>`
      -- the end tag: `</sheetData>` or `</x:sheetData>`
      let mut e := gt + 1
      repeat
        let some close := indexOf b "sheetData>" e | return none
        let mut c := close
        while c > 0 && b[c - 1]! != 60 && b[c - 1]! != 62 do c := c - 1
        if c ≥ 2 && b[c - 1]! == 60 && b[c]! == 47 then return some (gt + 1, c - 1)
        e := close + 1
      return none
    from_ := k + 1
  return none

end Xlsx.Read
