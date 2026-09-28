import Xlsx.Zip

/-!
# Reading back what was written

`readSpec_archive`: for any list of entries that fits in a plain ZIP, `readSpec`
recovers every entry's name and data, in order, by following the end record, the
central directory and each local header, as a ZIP reader does.
-/

namespace Xlsx.Archive

/-- One central record, and the local record it points to, read in place. -/
theorem readOne {l : List UInt8} {e : Entry} {off p : Nat}
    (hcen : ∃ pre post, l = pre ++ centralRecord e off ++ post ∧ pre.length = p)
    (hloc : ∃ pre post, l = pre ++ localRecord e ++ post ∧ pre.length = off)
    (hn : e.nameBytes.length < 65536) (hs : e.bytes.length < 2 ^ 32) (ho : off < 2 ^ 32) :
    rd l p 4 = 0x02014b50 ∧ rd l (p + 42) 4 = off ∧ rd l off 4 = 0x04034b50 ∧
    rd l (p + 28) 2 = e.nameBytes.length ∧ (l.drop (p + 46)).take e.nameBytes.length = e.nameBytes ∧
    rd l (p + 30) 2 = 0 ∧ rd l (p + 32) 2 = 0 ∧ rd l (p + 20) 4 = e.bytes.length ∧
    rd l (off + 26) 2 = e.nameBytes.length ∧ rd l (off + 28) 2 = 0 ∧
    (l.drop (off + 30 + e.nameBytes.length)).take e.bytes.length = e.bytes := by
  obtain ⟨pre, post, hl, rfl⟩ := hcen
  obtain ⟨lpre, lpost, hl', rfl⟩ := hloc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rd_at (pre := pre) (bs := le32 0x02014b50) (post := (le16 20 ++ le16 20 ++ le16 0x0800 ++ le16 0 ++ le16 0 ++ le16 dosDate ++ le32 e.crc ++ le32 e.bytes.length ++ le32 e.bytes.length ++ le16 e.nameBytes.length ++ le16 0 ++ le16 0 ++ le16 0 ++ le16 0 ++ le32 0 ++ le32 lpre.length ++ e.nameBytes) ++ post) (i := pre.length) (k := 4)
      (by rw [hl, centralRecord]; simp only [List.append_assoc])
      (by simp) rfl]
    rfl
  · rw [rd_at (pre := pre ++ (le32 0x02014b50 ++ le16 20 ++ le16 20 ++ le16 0x0800 ++ le16 0 ++ le16 0 ++ le16 dosDate ++ le32 e.crc ++ le32 e.bytes.length ++ le32 e.bytes.length ++ le16 e.nameBytes.length ++ le16 0 ++ le16 0 ++ le16 0 ++ le16 0 ++ le32 0)) (bs := le32 lpre.length) (post := (e.nameBytes) ++ post) (i := pre.length + 42) (k := 4)
      (by rw [hl, centralRecord]; simp only [List.append_assoc])
      (by simp) rfl]
    exact dec_le32 ho
  · rw [rd_at (pre := lpre) (bs := le32 0x04034b50) (post := (le16 20 ++ le16 0x0800 ++ le16 0 ++ le16 0 ++ le16 dosDate ++ le32 e.crc ++ le32 e.bytes.length ++ le32 e.bytes.length ++ le16 e.nameBytes.length ++ le16 0 ++ e.nameBytes ++ e.bytes) ++ lpost) (i := lpre.length) (k := 4)
      (by rw [hl', localRecord]; simp only [List.append_assoc])
      (by simp) rfl]
    rfl
  · rw [rd_at (pre := pre ++ (le32 0x02014b50 ++ le16 20 ++ le16 20 ++ le16 0x0800 ++ le16 0 ++ le16 0 ++ le16 dosDate ++ le32 e.crc ++ le32 e.bytes.length ++ le32 e.bytes.length)) (bs := le16 e.nameBytes.length) (post := (le16 0 ++ le16 0 ++ le16 0 ++ le16 0 ++ le32 0 ++ le32 lpre.length ++ e.nameBytes) ++ post) (i := pre.length + 28) (k := 2)
      (by rw [hl, centralRecord]; simp only [List.append_assoc])
      (by simp) rfl]
    exact dec_le16 hn
  · exact slice_at (pre := pre ++ (le32 0x02014b50 ++ le16 20 ++ le16 20 ++ le16 0x0800 ++ le16 0 ++ le16 0 ++ le16 dosDate ++ le32 e.crc ++ le32 e.bytes.length ++ le32 e.bytes.length ++ le16 e.nameBytes.length ++ le16 0 ++ le16 0 ++ le16 0 ++ le16 0 ++ le32 0 ++ le32 lpre.length)) (bs := e.nameBytes) (post := post) (i := pre.length + 46) (k := e.nameBytes.length)
      (by rw [hl, centralRecord]; simp only [List.append_assoc])
      (by simp) rfl
  · rw [rd_at (pre := pre ++ (le32 0x02014b50 ++ le16 20 ++ le16 20 ++ le16 0x0800 ++ le16 0 ++ le16 0 ++ le16 dosDate ++ le32 e.crc ++ le32 e.bytes.length ++ le32 e.bytes.length ++ le16 e.nameBytes.length)) (bs := le16 0) (post := (le16 0 ++ le16 0 ++ le16 0 ++ le32 0 ++ le32 lpre.length ++ e.nameBytes) ++ post) (i := pre.length + 30) (k := 2)
      (by rw [hl, centralRecord]; simp only [List.append_assoc])
      (by simp) rfl]
    rfl
  · rw [rd_at (pre := pre ++ (le32 0x02014b50 ++ le16 20 ++ le16 20 ++ le16 0x0800 ++ le16 0 ++ le16 0 ++ le16 dosDate ++ le32 e.crc ++ le32 e.bytes.length ++ le32 e.bytes.length ++ le16 e.nameBytes.length ++ le16 0)) (bs := le16 0) (post := (le16 0 ++ le16 0 ++ le32 0 ++ le32 lpre.length ++ e.nameBytes) ++ post) (i := pre.length + 32) (k := 2)
      (by rw [hl, centralRecord]; simp only [List.append_assoc])
      (by simp) rfl]
    rfl
  · rw [rd_at (pre := pre ++ (le32 0x02014b50 ++ le16 20 ++ le16 20 ++ le16 0x0800 ++ le16 0 ++ le16 0 ++ le16 dosDate ++ le32 e.crc)) (bs := le32 e.bytes.length) (post := (le32 e.bytes.length ++ le16 e.nameBytes.length ++ le16 0 ++ le16 0 ++ le16 0 ++ le16 0 ++ le32 0 ++ le32 lpre.length ++ e.nameBytes) ++ post) (i := pre.length + 20) (k := 4)
      (by rw [hl, centralRecord]; simp only [List.append_assoc])
      (by simp) rfl]
    exact dec_le32 hs
  · rw [rd_at (pre := lpre ++ (le32 0x04034b50 ++ le16 20 ++ le16 0x0800 ++ le16 0 ++ le16 0 ++ le16 dosDate ++ le32 e.crc ++ le32 e.bytes.length ++ le32 e.bytes.length)) (bs := le16 e.nameBytes.length) (post := (le16 0 ++ e.nameBytes ++ e.bytes) ++ lpost) (i := lpre.length + 26) (k := 2)
      (by rw [hl', localRecord]; simp only [List.append_assoc])
      (by simp) rfl]
    exact dec_le16 hn
  · rw [rd_at (pre := lpre ++ (le32 0x04034b50 ++ le16 20 ++ le16 0x0800 ++ le16 0 ++ le16 0 ++ le16 dosDate ++ le32 e.crc ++ le32 e.bytes.length ++ le32 e.bytes.length ++ le16 e.nameBytes.length)) (bs := le16 0) (post := (e.nameBytes ++ e.bytes) ++ lpost) (i := lpre.length + 28) (k := 2)
      (by rw [hl', localRecord]; simp only [List.append_assoc])
      (by simp) rfl]
    rfl
  · exact slice_at (pre := lpre ++ (le32 0x04034b50 ++ le16 20 ++ le16 0x0800 ++ le16 0 ++ le16 0 ++ le16 dosDate ++ le32 e.crc ++ le32 e.bytes.length ++ le32 e.bytes.length ++ le16 e.nameBytes.length ++ le16 0 ++ e.nameBytes)) (bs := e.bytes) (post := lpost) (i := lpre.length + 30 + e.nameBytes.length) (k := e.bytes.length)
      (by rw [hl', localRecord]; simp only [List.append_assoc])
      (by simp; omega) rfl

theorem length_bytes (es : List Entry) :
    (bytes es).length = (locals es).length + (centrals 0 es).length + 22 := by
  simp [bytes, eocd]; omega

/-- The central directory, walked from any record onward. -/
theorem readCentral_suffix (es : List Entry) (hf : Fits es) :
    ∀ (todo done : List Entry), done ++ todo = es →
      readCentral (bytes es) todo.length ((locals es).length + (centrals 0 done).length)
        = some (todo.map fun e => (e.nameBytes, e.bytes)) := by
  intro todo
  induction todo with
  | nil => intro _ _; rfl
  | cons e rest ih =>
    intro done hes
    have hmem : e ∈ es := by rw [← hes]; simp
    have htot : (bytes es).length < 2 ^ 32 := hf.total
    have hsplit : bytes es = locals done ++ localRecord e ++ locals rest
        ++ (centrals 0 done ++ centralRecord e (locals done).length
          ++ centrals ((locals done).length + (localRecord e).length) rest)
        ++ eocd es.length (centrals 0 es).length (locals es).length := by
      conv => lhs; rw [bytes]
      conv => lhs; enter [1, 1]; rw [← hes, locals_append]
      conv => lhs; enter [1, 2]; rw [← hes, centrals_append]
      simp [locals, centrals, List.append_assoc]
    have hcen : ∃ pre post, bytes es = pre ++ centralRecord e (locals done).length ++ post ∧
        pre.length = (locals es).length + (centrals 0 done).length := by
      refine ⟨locals done ++ localRecord e ++ locals rest ++ centrals 0 done,
        centrals ((locals done).length + (localRecord e).length) rest
          ++ eocd es.length (centrals 0 es).length (locals es).length, ?_, ?_⟩
      · rw [hsplit]; simp only [List.append_assoc]
      · rw [← hes, locals_append]; simp [locals]; omega
    have hloc : ∃ pre post, bytes es = pre ++ localRecord e ++ post ∧
        pre.length = (locals done).length :=
      ⟨locals done, locals rest ++ (centrals 0 done ++ centralRecord e (locals done).length
          ++ centrals ((locals done).length + (localRecord e).length) rest)
          ++ eocd es.length (centrals 0 es).length (locals es).length,
        by rw [hsplit]; simp only [List.append_assoc], rfl⟩
    have hoff : (locals done).length < 2 ^ 32 := by
      have : (bytes es).length = (locals done).length + (localRecord e).length + (locals rest).length
          + ((centrals 0 done).length + (centralRecord e (locals done).length).length
            + (centrals ((locals done).length + (localRecord e).length) rest).length) + 22 := by
        rw [hsplit]; simp [eocd]; omega
      omega
    have hsize : e.bytes.length < 2 ^ 32 := by
      have : (bytes es).length = (locals done).length + (localRecord e).length + (locals rest).length
          + ((centrals 0 done).length + (centralRecord e (locals done).length).length
            + (centrals ((locals done).length + (localRecord e).length) rest).length) + 22 := by
        rw [hsplit]; simp [eocd]; omega
      rw [length_localRecord] at this
      omega
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
      readOne hcen hloc (hf.names e hmem) hsize hoff
    simp only [List.length_cons, readCentral]
    rw [if_neg (by rw [h1]; decide)]
    simp only [h2]
    rw [if_neg (by rw [h3]; decide)]
    simp only [h4, h5, h6, h7, h8, h9, h10, Nat.add_zero, h11]
    have := ih (done ++ [e]) (by simp [hes])
    rw [centrals_append] at this
    simp only [centrals, List.append_nil, List.length_append, length_centralRecord, Nat.zero_add] at this
    rw [show (locals es).length + (centrals 0 done).length + 46 + e.nameBytes.length =
      (locals es).length + ((centrals 0 done).length + (46 + e.nameBytes.length)) by omega, this]
    rfl

/-- **Reading back what was written gives every entry, in order.** -/
theorem readSpec_archive (es : List Entry) (hf : Fits es) :
    readSpec (bytes es) = some (es.map fun e => (e.nameBytes, e.bytes)) := by
  have hlen := length_bytes es
  have hl : (bytes es).length - 22 = (locals es).length + (centrals 0 es).length := by omega
  have hcount : es.length < 65536 := by have := hf.count; omega
  have htot := hf.total
  have hcd : (locals es).length < 2 ^ 32 := by omega
  unfold readSpec
  simp only [hl]
  rw [rd_at (pre := locals es ++ centrals 0 es) (bs := le32 0x06054b50)
      (post := le16 0 ++ le16 0 ++ le16 es.length ++ le16 es.length ++ le32 (centrals 0 es).length
        ++ le32 (locals es).length ++ le16 0)
      (i := (locals es).length + (centrals 0 es).length) (k := 4)
      (by simp [bytes, eocd]) (by simp) rfl]
  rw [if_neg (by decide)]
  rw [rd_at (pre := locals es ++ centrals 0 es ++ (le32 0x06054b50 ++ le16 0 ++ le16 0 ++ le16 es.length))
      (bs := le16 es.length)
      (post := le32 (centrals 0 es).length ++ le32 (locals es).length ++ le16 0)
      (i := (locals es).length + (centrals 0 es).length + 10) (k := 2)
      (by simp [bytes, eocd]) (by simp; omega) rfl, dec_le16 hcount]
  rw [rd_at (pre := locals es ++ centrals 0 es ++ (le32 0x06054b50 ++ le16 0 ++ le16 0 ++ le16 es.length
        ++ le16 es.length ++ le32 (centrals 0 es).length))
      (bs := le32 (locals es).length) (post := le16 0)
      (i := (locals es).length + (centrals 0 es).length + 16) (k := 4)
      (by simp [bytes, eocd]) (by simp; omega) rfl, dec_le32 hcd]
  have := readCentral_suffix es hf es [] rfl
  simpa [centrals] using this

end Xlsx.Archive
