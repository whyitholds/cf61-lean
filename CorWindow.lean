import CorCells
import MainBits

open CF61

def corExcluded (k : ℕ) : PICell := ⟨2*k-1,0,0⟩

theorem corExcludedMem {m : ℕ} (hm : 3 ≤ m) :
    corExcluded (K m) ∈ corCells (m-1) := by
  have hk := cfKTwo m hm
  apply (corMemCells hm).mpr
  change 2*K m-1 < 2*K m ∧ 0 < 2*K m ∧ (2*K m-1) &&& 0 = 0 ∧ _
  exact ⟨by omega, by omega, by simp, Or.inl (by change (0 : ℕ) ≤ 1; decide)⟩

theorem corCellStart {k : ℕ} {a : PICell} (ha : PIValid k a) :
    8*k ≤ PICellValue k a := by
  rcases a with ⟨u,v,i⟩
  obtain ⟨_,_,_,htag⟩ := ha
  change PITagOK u v i at htag
  rcases Nat.eq_zero_or_pos u with rfl | hu
  · fin_cases i <;> norm_num [PITagOK] at htag <;>
      norm_num [PICellValue, PITagShift, PITagResidue] <;> omega
  · have hmul : 16*k ≤ 16*k*u := by simpa using Nat.mul_le_mul_left (16*k) hu
    fin_cases i <;> norm_num [PICellValue, PITagShift, PITagResidue] <;> omega

theorem corCellCut {m : ℕ} (hm : 3 ≤ m) {a : PICell} (ha : PIValid (K m) a) :
    PICellValue (K m) a + 6*K m < n₀ m ↔ a ≠ corExcluded (K m) := by
  rcases a with ⟨u,v,i⟩
  let k := K m
  have hk : 2 ≤ k := cfKTwo m hm
  change u < 2*k ∧ v < 2*k ∧ u &&& v = 0 ∧ PITagOK u v i at ha
  obtain ⟨hu,hv,hd,htag⟩ := ha
  change PICellValue k ⟨u,v,i⟩ + 6*k < 32*k^2 ↔ (⟨u,v,i⟩ : PICell) ≠ corExcluded k
  by_cases high : u = 2*k-1
  · have hvz : v = 0 := by
      have top : u = 2^(m-1)-1 := by rw [corWidth hm]; exact high
      have hv' : v < 2^(m-1) := by rw [corWidth hm]; exact hv
      rwa [Nat.and_comm, top, Nat.and_two_pow_sub_one_of_lt_two_pow hv'] at hd
    subst v
    subst u
    have hmprod : 16*k*(2*k-1) + 16*k = 32*k^2 := by
      calc
        _ = 16*k*(2*k-1+1) := by ring
        _ = 32*k^2 := by rw [show 2*k-1+1 = 2*k by omega]; ring
    fin_cases i <;> norm_num [PITagOK] at htag <;>
      norm_num [corExcluded, PICellValue, PITagShift, PITagResidue] <;> omega
  · have hmprod : 16*k*u + 32*k ≤ 32*k^2 := by
      calc
        _ = 16*k*(u+2) := by ring
        _ ≤ 16*k*(2*k) := Nat.mul_le_mul_left _ (by omega)
        _ = 32*k^2 := by ring
    have hn : (⟨u,v,i⟩ : PICell) ≠ corExcluded k := fun h => high (congrArg PICell.u h)
    apply iff_of_true _ hn
    fin_cases i <;> norm_num [PICellValue, PITagShift, PITagResidue] <;> omega

def corOddCells (m : ℕ) : Finset PICell :=
  (corCells (m-1)).erase (corExcluded (K m))

theorem corOddCellsMem {m : ℕ} (hm : 3 ≤ m) {a : PICell} :
    a ∈ corOddCells m ↔ PIValid (K m) a ∧ PICellValue (K m) a + 6*K m < n₀ m := by
  rw [corOddCells, Finset.mem_erase, corMemCells hm]
  constructor
  · exact fun ⟨hn,ha⟩ => ⟨ha, (corCellCut hm ha).mpr hn⟩
  · exact fun ⟨ha,hp⟩ => ⟨(corCellCut hm ha).mp hp, ha⟩

theorem corOddCellsCard {m : ℕ} (hm : 3 ≤ m) :
    (corOddCells m).card + 2 = 4*3^(m-1) := by
  have h := Finset.card_erase_add_one (corExcludedMem hm)
  have h' := corCellsCard (m-1)
  unfold corOddCells
  omega
