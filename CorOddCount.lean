import CorWindow
import CorTransfer
import EncodeRows

open OneAdd CF61

noncomputable def corOddValues (m : ℕ) (x : ℕ → ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (Nb m)).filter fun N => N % 2 = 1 ∧ cfTerm x N

theorem corOddValuesMem {m N : ℕ} {x : ℕ → ℕ} :
    N ∈ corOddValues m x ↔ N < Nb m ∧ N % 2 = 1 ∧ cfTerm x N := by
  classical
  simp [corOddValues]

def corOddValue (m : ℕ) (a : PICell) : ℕ := 2*PICellValue (K m) a - (3*b m+4)

theorem corOddValueIndex {m : ℕ} (hm : 3 ≤ m) {a : PICell} (ha : PIValid (K m) a) :
    (corOddValue m a + 3*b m+4)/2 = PICellValue (K m) a ∧ corOddValue m a % 2 = 1 := by
  have hstart := corCellStart ha
  have hb := cfBFromK m hm
  have hk := cfKTwo m hm
  unfold corOddValue
  omega

theorem corOddValuesCard {m : ℕ} (hm : 3 ≤ m) {x : ℕ → ℕ} (hx : IsUlam 4 (b m) x) :
    (corOddValues m x).card = (corOddCells m).card := by
  have hb := cfBFromK m hm
  have hk := cfKTwo m hm
  have scale := (cfEndpointScale hm).1
  symm
  apply Finset.card_bij (fun a _ => corOddValue m a)
  · intro a ha
    obtain ⟨hv, hcut⟩ := (corOddCellsMem hm).mp ha
    have hstart := corCellStart hv
    obtain ⟨hindex, ho⟩ := corOddValueIndex hm hv
    have hN : corOddValue m a < Nb m := by unfold corOddValue; omega
    apply corOddValuesMem.mpr
    refine ⟨hN, ho, (corOddBit hm hx ho hN).mpr ?_⟩
    rw [hindex]
    exact (cfPISupport cfCheckedClosed m hm _ (by omega) (by omega)).mpr ⟨a,hv,rfl⟩
  · intro a ha a' ha' he
    have hv := ((corOddCellsMem hm).mp ha).1
    have hv' := ((corOddCellsMem hm).mp ha').1
    have hstart := corCellStart hv
    apply cfPIInject m hm hv hv' _ (by omega)
    rw [← (corOddValueIndex hm hv).1, ← (corOddValueIndex hm hv').1, he]
  · intro N h
    obtain ⟨hN,ho,ht⟩ := corOddValuesMem.mp h
    let p := (N + 3*b m + 4)/2
    have hp : 1 ≤ p := by dsimp [p]; omega
    have hcut : p + 6*K m < n₀ m := by dsimp [p]; omega
    have hy : y m p = 1 := (corOddBit hm hx ho hN).mp ht
    obtain ⟨a,hv,hea⟩ := (cfPISupport cfCheckedClosed m hm p hp (by omega)).mp hy
    refine ⟨a,(corOddCellsMem hm).mpr ⟨hv, by rwa [hea]⟩, ?_⟩
    rw [corOddValue, hea]
    dsimp [p]
    omega
