import Zip.Native.InflateTreeFree
import Zip.Native.Crc32

/-!
# Reading a ZIP archive

The central directory is the index: find the end-of-central-directory record, walk
the directory, and for each entry read its data from the local header it points to.
Stored entries are copied; DEFLATE entries go through `Zip.Native.Inflate.inflate`, the
decoder lean-zip ships, for which `inflate (deflateRaw x) = x` is proved
(`Zip.Native.Deflate.inflate_deflateRaw`). Every entry's CRC-32 is
checked with lean-zip's CRC, which is proved equal to its specification.

Refused, with a message: encryption, ZIP64, methods other than stored and DEFLATE,
and archives that decompress past a size limit (a zip-bomb guard).

Entries are returned in directory order, duplicates included, so the spec can see
them.
-/

namespace Xlsx.Read

structure ZipEntry where
  name : String
  data : ByteArray
  method : Nat

def u16At (b : ByteArray) (i : Nat) : Nat := b[i]!.toNat + b[i + 1]!.toNat * 256
def u32At (b : ByteArray) (i : Nat) : Nat := u16At b i + u16At b (i + 2) * 65536

/-- The end-of-central-directory record: the last `PK\x05\x06` within 64 KiB of the end. -/
def findEocd (b : ByteArray) : Option Nat := Id.run do
  if b.size < 22 then return none
  let lowest := if b.size ≥ 22 + 65535 then b.size - 22 - 65535 else 0
  let mut i := b.size - 22
  repeat
    if u32At b i == 0x06054b50 then return some i
    if i ≤ lowest then return none
    i := i - 1
  return none

def readZip (b : ByteArray) (limit : Nat := 512 * 1024 * 1024) : Except String (Array ZipEntry) := do
  if b.size ≥ 8 && b[0]! == 0xD0 && b[1]! == 0xCF && b[2]! == 0x11 && b[3]! == 0xE0 then
    throw "an OLE compound file, not a ZIP: a password-protected workbook, or an old .xls renamed"
  let some e := findEocd b | throw "not a ZIP archive: no end-of-central-directory record"
  let count := u16At b (e + 10)
  let cdSize := u32At b (e + 12)
  let cdOffset := u32At b (e + 16)
  if count == 0xFFFF || cdOffset == 0xFFFFFFFF || cdSize == 0xFFFFFFFF then
    throw "ZIP64 archives are not supported"
  if cdOffset + cdSize > e then throw "the central directory runs past its end record"
  let mut out : Array ZipEntry := #[]
  let mut p := cdOffset
  let mut total := 0
  for _ in [0:count] do
    if p + 46 > b.size || u32At b p != 0x02014b50 then throw s!"bad central directory header at byte {p}"
    let flags := u16At b (p + 8)
    let method := u16At b (p + 10)
    let crc := u32At b (p + 16)
    let csize := u32At b (p + 20)
    let usize := u32At b (p + 24)
    let nlen := u16At b (p + 28)
    let xlen := u16At b (p + 30)
    let clen := u16At b (p + 32)
    let local_ := u32At b (p + 42)
    let nameBytes := b.extract (p + 46) (p + 46 + nlen)
    let name := (String.fromUTF8? nameBytes).getD (String.ofList (nameBytes.toList.map fun c => Char.ofNat c.toNat))
    p := p + 46 + nlen + xlen + clen
    if flags &&& 1 == 1 then throw s!"{name}: encrypted entries are not supported"
    if csize == 0xFFFFFFFF || usize == 0xFFFFFFFF || local_ == 0xFFFFFFFF then throw s!"{name}: ZIP64 entries are not supported"
    if local_ + 30 > b.size || u32At b local_ != 0x04034b50 then throw s!"{name}: bad local header"
    let start := local_ + 30 + u16At b (local_ + 26) + u16At b (local_ + 28)
    if start + csize > b.size then throw s!"{name}: data runs past the end of the archive"
    let raw := b.extract start (start + csize)
    total := total + usize
    if total > limit then throw s!"the archive expands past {limit} bytes"
    let data ← match method with
      | 0 => pure raw
      | 8 =>
        -- some room past the declared size, so a wrong size is reported as one
        match Zip.Native.Inflate.inflate raw (usize + 65536) with
        | .ok d => pure d
        | .error msg => throw s!"{name}: DEFLATE data is corrupt: {msg}"
      | m => throw s!"{name}: compression method {m} is not supported"
    if data.size != usize then throw s!"{name}: {data.size} bytes, the directory says {usize}"
    if (Crc32.Native.crc32 0 data).toNat != crc then throw s!"{name}: CRC-32 does not match"
    out := out.push { name, data, method }
  return out

end Xlsx.Read
