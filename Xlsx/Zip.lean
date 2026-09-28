/-!
# A ZIP writer, stored entries only

XLSX readers accept uncompressed ("stored", method 0) entries, so this writer skips
DEFLATE entirely. Nothing about it is proved yet: that is the next step, reading back
what it writes. For compressed output, `kim-em/lean-zip` has a verified DEFLATE.
-/

namespace Xlsx.Archive

/-- The CRC-32 table (polynomial `0xEDB88320`, reflected). -/
def crcTable : Array UInt32 := Id.run do
  let mut t := Array.mkEmpty 256
  for i in [0:256] do
    let mut c : UInt32 := i.toUInt32
    for _ in [0:8] do
      c := if c &&& 1 == 1 then (0xEDB88320 : UInt32) ^^^ (c >>> 1) else c >>> 1
    t := t.push c
  return t

def crc32 (data : ByteArray) : UInt32 := Id.run do
  let mut c : UInt32 := 0xFFFFFFFF
  for b in data do
    c := crcTable[((c ^^^ b.toUInt32) &&& 0xFF).toNat]! ^^^ (c >>> 8)
  return c ^^^ 0xFFFFFFFF

def u16 (n : Nat) : ByteArray := ⟨#[(n % 256).toUInt8, (n / 256 % 256).toUInt8]⟩
def u32 (n : Nat) : ByteArray :=
  ⟨#[(n % 256).toUInt8, (n / 256 % 256).toUInt8, (n / 65536 % 256).toUInt8,
     (n / 16777216 % 256).toUInt8]⟩

/-- DOS date for 1980-01-01, the earliest a ZIP can say. The output is reproducible. -/
def dosDate : Nat := (0 <<< 9) ||| (1 <<< 5) ||| 1

structure Entry where
  name : String
  data : ByteArray

/-- The archive bytes. -/
def archive (entries : List Entry) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut central := ByteArray.empty
  for e in entries do
    let name := e.name.toUTF8
    let crc := (crc32 e.data).toNat
    let offset := out.size
    -- local file header
    out := out ++ u32 0x04034b50 ++ u16 20 ++ u16 0x0800 ++ u16 0 ++ u16 0 ++ u16 dosDate
      ++ u32 crc ++ u32 e.data.size ++ u32 e.data.size ++ u16 name.size ++ u16 0
      ++ name ++ e.data
    -- central directory header
    central := central ++ u32 0x02014b50 ++ u16 20 ++ u16 20 ++ u16 0x0800 ++ u16 0 ++ u16 0
      ++ u16 dosDate ++ u32 crc ++ u32 e.data.size ++ u32 e.data.size ++ u16 name.size
      ++ u16 0 ++ u16 0 ++ u16 0 ++ u16 0 ++ u32 0 ++ u32 offset ++ name
  let cdOffset := out.size
  out := out ++ central
    ++ u32 0x06054b50 ++ u16 0 ++ u16 0 ++ u16 entries.length ++ u16 entries.length
    ++ u32 central.size ++ u32 cdOffset ++ u16 0
  return out

end Xlsx.Archive
