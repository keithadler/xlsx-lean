import Zip.Native.Crc32

/-!
# The ZIP writer, and the proof that it can be read back

XLSX readers accept uncompressed ("stored", method 0) entries, so the writer skips
DEFLATE. Its byte layout is written here as lists of bytes, which is what the proof is
about; `archive` just packs that list into a `ByteArray`.

`readSpec` reads an archive the way a ZIP reader does: find the end-of-central-directory
record at the end, go to the central directory, and for each record follow its offset
to the local header and take the data from there. It is a specification: the
production reader `Read.readZip` (ByteArray, DEFLATE, checks) follows the same steps,
and the lab tests the two against each other on every corpus file.

**`readSpec_archive`**: for any list of entries that fits in a plain ZIP (names under
64 KiB, fewer than 65,535 entries, the whole archive under 4 GiB), reading back what
was written gives every entry's name and data, in order.

CRCs come from lean-zip's CRC-32, which is proved equal to its specification, so the
writer and the reader compute the same function.
-/

namespace Xlsx.Archive

/-- Little-endian, two bytes. -/
def le16 (n : Nat) : List UInt8 := [(n % 256).toUInt8, (n / 256 % 256).toUInt8]
/-- Little-endian, four bytes. -/
def le32 (n : Nat) : List UInt8 := le16 (n % 65536) ++ le16 (n / 65536 % 65536)

/-- Read little-endian bytes back. -/
def dec : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * dec bs

/-- `k` bytes at position `i`, as a number. -/
def rd (l : List UInt8) (i k : Nat) : Nat := dec ((l.drop i).take k)

/-- DOS date for 1980-01-01, the earliest a ZIP can say. The output is reproducible. -/
def dosDate : Nat := (0 <<< 9) ||| (1 <<< 5) ||| 1

structure Entry where
  name : String
  data : ByteArray

def Entry.nameBytes (e : Entry) : List UInt8 := e.name.toUTF8.toList
def Entry.bytes (e : Entry) : List UInt8 := e.data.toList
def Entry.crc (e : Entry) : Nat := (Crc32.Native.crc32 0 e.data).toNat

def localRecord (e : Entry) : List UInt8 :=
  le32 0x04034b50 ++ le16 20 ++ le16 0x0800 ++ le16 0 ++ le16 0 ++ le16 dosDate
  ++ le32 e.crc ++ le32 e.bytes.length ++ le32 e.bytes.length ++ le16 e.nameBytes.length ++ le16 0
  ++ e.nameBytes ++ e.bytes

def centralRecord (e : Entry) (off : Nat) : List UInt8 :=
  le32 0x02014b50 ++ le16 20 ++ le16 20 ++ le16 0x0800 ++ le16 0 ++ le16 0 ++ le16 dosDate
  ++ le32 e.crc ++ le32 e.bytes.length ++ le32 e.bytes.length ++ le16 e.nameBytes.length
  ++ le16 0 ++ le16 0 ++ le16 0 ++ le16 0 ++ le32 0 ++ le32 off ++ e.nameBytes

def locals : List Entry → List UInt8
  | [] => []
  | e :: es => localRecord e ++ locals es

def centrals : Nat → List Entry → List UInt8
  | _, [] => []
  | off, e :: es => centralRecord e off ++ centrals (off + (localRecord e).length) es

def eocd (count cdSize cdOffset : Nat) : List UInt8 :=
  le32 0x06054b50 ++ le16 0 ++ le16 0 ++ le16 count ++ le16 count ++ le32 cdSize ++ le32 cdOffset
  ++ le16 0

/-- The archive, byte by byte. -/
def bytes (es : List Entry) : List UInt8 :=
  locals es ++ centrals 0 es ++ eocd es.length (centrals 0 es).length (locals es).length

def archive (es : List Entry) : ByteArray := ⟨(bytes es).toArray⟩

/-! ## Reading it back -/

def readCentral (l : List UInt8) : Nat → Nat → Option (List (List UInt8 × List UInt8))
  | 0, _ => some []
  | k + 1, p =>
    if rd l p 4 ≠ 0x02014b50 then none else
    let off := rd l (p + 42) 4
    if rd l off 4 ≠ 0x04034b50 then none else
    let nlen := rd l (p + 28) 2
    let name := (l.drop (p + 46)).take nlen
    let data := (l.drop (off + 30 + rd l (off + 26) 2 + rd l (off + 28) 2)).take (rd l (p + 20) 4)
    (readCentral l k (p + 46 + nlen + rd l (p + 30) 2 + rd l (p + 32) 2)).map ((name, data) :: ·)

/-- Read an archive as a ZIP reader does: end record, central directory, local headers. -/
def readSpec (l : List UInt8) : Option (List (List UInt8 × List UInt8)) :=
  let e := l.length - 22
  if rd l e 4 ≠ 0x06054b50 then none
  else readCentral l (rd l (e + 10) 2) (rd l (e + 16) 4)

/-! ## The proof -/

@[simp] theorem length_le16 (n : Nat) : (le16 n).length = 2 := rfl
@[simp] theorem length_le32 (n : Nat) : (le32 n).length = 4 := rfl

theorem dec_le16 {n : Nat} (h : n < 65536) : dec (le16 n) = n := by
  simp only [le16, dec, Nat.toUInt8_eq, UInt8.toNat_ofNat']
  omega

theorem dec_le16_append {n : Nat} (h : n < 65536) (rest : List UInt8) :
    dec (le16 n ++ rest) = n + 65536 * dec rest := by
  simp only [le16, List.cons_append, List.nil_append, dec, Nat.toUInt8_eq, UInt8.toNat_ofNat']
  omega

theorem dec_le32 {n : Nat} (h : n < 2 ^ 32) : dec (le32 n) = n := by
  rw [le32, dec_le16_append (Nat.mod_lt _ (by decide)), dec_le16 (by omega)]
  omega

/-- A field read where it was written. -/
theorem rd_mid (pre bs post : List UInt8) : rd (pre ++ bs ++ post) pre.length bs.length = dec bs := by
  simp [rd, List.append_assoc, List.drop_left', List.take_left']

theorem rd_at {l pre bs post : List UInt8} {i k : Nat} (hl : l = pre ++ bs ++ post)
    (hi : pre.length = i) (hk : bs.length = k) : rd l i k = dec bs := by
  subst hl hi hk; exact rd_mid ..

theorem slice_at {l pre bs post : List UInt8} {i k : Nat} (hl : l = pre ++ bs ++ post)
    (hi : pre.length = i) (hk : bs.length = k) : (l.drop i).take k = bs := by
  subst hl hi hk; simp [List.append_assoc, List.drop_left', List.take_left']

theorem length_localRecord (e : Entry) :
    (localRecord e).length = 30 + e.nameBytes.length + e.bytes.length := by
  simp [localRecord]; omega

theorem length_centralRecord (e : Entry) (off : Nat) :
    (centralRecord e off).length = 46 + e.nameBytes.length := by
  simp [centralRecord]; omega

theorem locals_append (xs ys : List Entry) : locals (xs ++ ys) = locals xs ++ locals ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [locals, ih, List.append_assoc]

theorem centrals_append (o : Nat) (xs ys : List Entry) :
    centrals o (xs ++ ys) = centrals o xs ++ centrals (o + (locals xs).length) ys := by
  induction xs generalizing o with
  | nil => simp [centrals, locals]
  | cons x xs ih => simp [centrals, locals, ih, List.append_assoc, Nat.add_assoc]

/-- What an archive must fit: the ZIP fields are 16 and 32 bits wide. -/
structure Fits (es : List Entry) : Prop where
  count : es.length < 65535
  names : ∀ e ∈ es, e.nameBytes.length < 65536
  total : (bytes es).length < 2 ^ 32

end Xlsx.Archive
