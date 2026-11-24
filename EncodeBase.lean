import PartISpec
import NumBits
import CoordsBase
import ClosedBase
open CF61

def cfPIDecode (k l t r : ℤ) : PICell :=
  if r = 1 then
    if t < 3*k then ⟨l.toNat,(t-k).toNat,0⟩
    else ⟨(l+1).toNat,(t-3*k).toNat,4⟩
  else if r = 2 then ⟨l.toNat,t.toNat,1⟩
  else if r = 3 then ⟨(l+1).toNat,(t-3*k).toNat,5⟩
  else if t = 4*k-1 then ⟨0,0,2⟩
  else if t < 2*k-1 then ⟨l.toNat,(t+1).toNat,2⟩
  else ⟨l.toNat,(t-2*k+1).toNat,3⟩

theorem cfPIZOne {h l : ℤ} (hz : z h l = 1) :
    0 ≤ l ∧ 0 ≤ h ∧ l.toNat &&& h.toNat = 0 := by
  have hs : 0 ≤ h ∧ 0 ≤ l := by
    contrapose! hz
    simp [z, show ¬(0 ≤ h ∧ 0 ≤ l) by omega]
  have hh := cfZBit h.toNat l.toNat
  rw [Int.toNat_of_nonneg hs.1, Int.toNat_of_nonneg hs.2, hz] at hh
  exact ⟨hs.2,hs.1,by rw [Nat.and_comm]; split at hh <;> omega⟩

theorem cfPIDisj (m u v : ℕ) (hu : u < 2*K m) (hv : v < 2*K m)
    (h : u &&& v = 0) : u < K m ∨ v < K m := by
  by_contra! hn
  have h2 : 2*K m = 2^(m-2+1) := by simp [K,pow_succ,mul_comm]
  rw [h2] at hu hv
  have a := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (i := m-2) hn.1 hu
  have b := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (i := m-2) hn.2 hv
  have q := congrArg (fun x : ℕ => x.testBit (m-2)) h
  simp [a,b] at q

theorem cfPICellValueCast (m : ℕ) (x : PICell) :
    ((PICellValue (K m) x : ℕ):ℤ) =
    16*(K m : ℤ)*x.u + 4*x.v + 4*(K m:ℤ)*(PITagShift x.kind:ℕ) + (PITagResidue x.kind:ℕ) := by
  simp [PICellValue]

theorem cfPIHit (m : ℕ) (x : PICell) (hx : PIValid (K m) x) :
    ∃ l t r : ℤ, Coords m (PICellValue (K m) x) l (2*(K m:ℤ)+t) r ∧
    -1 ≤ l ∧ l < 2*(K m:ℤ) ∧ 0 ≤ t ∧ t < 4*(K m:ℤ) ∧
    cfClosedRow (K m) l t r ∧ cfPIDecode (K m) l t r = x := by
  rcases x with ⟨u,v,i⟩
  obtain ⟨hu,hv,hd,hi⟩ := hx
  change u < 2*K m at hu
  change v < 2*K m at hv
  change u &&& v = 0 at hd
  change PITagOK u v i at hi
  have hk : 0 < K m := by unfold K; positivity
  have ha := cfPIDisj m u v hu hv hd
  have hz : z (v:ℤ) (u:ℤ) = 1 := by rw [cfZBit,Nat.and_comm,if_pos hd]
  have hvu : u = v → u = 0 := by rintro rfl; simpa using hd
  fin_cases i
  · refine ⟨(u:ℤ), (K m:ℤ)+(v:ℤ), 1, ?_, by omega, by omega, by omega, by omega, ?_, ?_⟩
    · unfold Coords
      rw [cfPICellValueCast]
      refine ⟨?_, by omega, by omega, by omega, by omega⟩
      norm_num [PITagShift, PITagResidue] <;> ring
    · unfold cfClosedRow
      left
      refine ⟨by decide, ?_⟩
      refine ⟨by omega, by omega, ?_⟩
      convert hz using 2 <;> ring
    · unfold cfPIDecode
      try simp only [Int.toNat_natCast, Nat.cast_zero, Int.toNat_zero]
      split_ifs <;> first | congr 1 <;> omega | omega
  · refine ⟨(u:ℤ), (v:ℤ), 2, ?_, by omega, by omega, by omega, by omega, ?_, ?_⟩
    · unfold Coords
      rw [cfPICellValueCast]
      refine ⟨?_, by omega, by omega, by omega, by omega⟩
      norm_num [PITagShift, PITagResidue] <;> ring
    · unfold cfClosedRow
      right; right; left
      refine ⟨by decide, ?_⟩
      refine ⟨by omega, ?_⟩
      convert hz using 2 <;> ring
    · unfold cfPIDecode
      try simp only [Int.toNat_natCast, Nat.cast_zero, Int.toNat_zero]
      split_ifs <;> first | congr 1 <;> omega | omega
  · norm_num [PITagOK] at hi
    by_cases h : u = v
    · have : u = 0 := hvu h
      obtain rfl : u = 0 := this
      obtain rfl : v = 0 := h.symm
      refine ⟨-1, 4*(K m:ℤ)-1, 4, ?_, by omega, by omega, by omega, by omega, ?_, ?_⟩
      · unfold Coords
        rw [cfPICellValueCast]
        refine ⟨?_, by omega, by omega, by omega, by omega⟩
        norm_num [PITagShift, PITagResidue] <;> ring
      · unfold cfClosedRow
        right; right; right; right; right; skip
        omega
      · unfold cfPIDecode
        try simp only [Int.toNat_natCast, Nat.cast_zero, Int.toNat_zero]
        split_ifs <;> first | congr 1 <;> omega | omega
    · refine ⟨(u:ℤ), (v:ℤ)-1, 4, ?_, by omega, by omega, by omega, by omega, ?_, ?_⟩
      · unfold Coords
        rw [cfPICellValueCast]
        refine ⟨?_, by omega, by omega, by omega, by omega⟩
        norm_num [PITagShift, PITagResidue] <;> ring
      · unfold cfClosedRow
        right; right; right; left
        refine ⟨by decide, ?_⟩
        refine ⟨by omega, by omega, ?_⟩
        convert hz using 2 <;> ring
      · unfold cfPIDecode
        try simp only [Int.toNat_natCast, Nat.cast_zero, Int.toNat_zero]
        split_ifs <;> first | congr 1 <;> omega | omega
  · norm_num [PITagOK] at hi
    refine ⟨(u:ℤ), 2*(K m:ℤ)+(v:ℤ)-1, 4, ?_, by omega, by omega, by omega, by omega, ?_, ?_⟩
    · unfold Coords
      rw [cfPICellValueCast]
      refine ⟨?_, by omega, by omega, by omega, by omega⟩
      norm_num [PITagShift, PITagResidue] <;> ring
    · unfold cfClosedRow
      right; right; right; right; left
      refine ⟨by decide, ?_⟩
      refine ⟨by omega, by omega, ?_⟩
      convert hz using 2 <;> ring
    · unfold cfPIDecode
      try simp only [Int.toNat_natCast, Nat.cast_zero, Int.toNat_zero]
      split_ifs <;> first | congr 1 <;> omega | omega
  · norm_num [PITagOK] at hi
    refine ⟨(u:ℤ)-1, 3*(K m:ℤ)+(v:ℤ), 1, ?_, by omega, by omega, by omega, by omega, ?_, ?_⟩
    · unfold Coords
      rw [cfPICellValueCast]
      refine ⟨?_, by omega, by omega, by omega, by omega⟩
      norm_num [PITagShift, PITagResidue] <;> ring
    · unfold cfClosedRow
      right; left
      refine ⟨by left; decide, ?_⟩
      refine ⟨by omega, by omega, ?_⟩
      convert hz using 2 <;> ring
    · unfold cfPIDecode
      try simp only [Int.toNat_natCast, Nat.cast_zero, Int.toNat_zero]
      split_ifs <;> first | congr 1 <;> omega | omega
  · norm_num [PITagOK] at hi
    refine ⟨(u:ℤ)-1, 3*(K m:ℤ)+(v:ℤ), 3, ?_, by omega, by omega, by omega, by omega, ?_, ?_⟩
    · unfold Coords
      rw [cfPICellValueCast]
      refine ⟨?_, by omega, by omega, by omega, by omega⟩
      norm_num [PITagShift, PITagResidue] <;> ring
    · unfold cfClosedRow
      right; left
      refine ⟨by right; decide, ?_⟩
      refine ⟨by omega, by omega, ?_⟩
      convert hz using 2 <;> ring
    · unfold cfPIDecode
      try simp only [Int.toNat_natCast, Nat.cast_zero, Int.toNat_zero]
      split_ifs <;> first | congr 1 <;> omega | omega
