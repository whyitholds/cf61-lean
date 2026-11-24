import ClosedResult
import PartIFull
import PartIIResult
import MainEven
import MainOdd

open OneAdd CF61

theorem corTermModel {m : ℕ} (hm : 3 ≤ m) {x : ℕ → ℕ} (hx : IsUlam 4 (b m) x)
    (t : ℕ) (ht : t ≤ Nb m) : cfTerm x t ↔ cfModel m t ∨ t = Nb m := by
  have eqs := cfCheckedClosed.1
  have hb := cfBFromK m hm
  have hk := cfKTwo m hm
  obtain ⟨scale, lower⟩ := cfEndpointScale hm
  let P := fun v => cfModel m v ∨ v = Nb m
  apply cfTermDetermined hx (by decide) P _ _ t ht
  · intro v hv
    change (cfEvenSeed m v ∨ (∃ d, v = b m + 2*d ∧ cfOffset m d = 1)) ∨ v = Nb m ↔ _
    unfold cfEvenSeed
    constructor
    · rintro ((h | ⟨d,e,_⟩) | h) <;> omega
    · rintro (h | h)
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inr ⟨0, by omega, by simpa [cfOffset] using (eqs m hm).2.1⟩)
  · intro v hv hN
    have pairs : ∀ w, cfValuePair P v w ↔ cfValuePair (cfModel m) v w := by
      intro w
      unfold cfValuePair
      by_cases h : 0 < w ∧ w < v-w
      · have h1 : w ≠ Nb m := by omega
        have h2 : v-w ≠ Nb m := by omega
        simp [P, h1, h2]
      · tauto
    rw [existsUnique_congr pairs]
    change (cfModel m v ∨ v = Nb m) ↔ _
    by_cases he : v % 2 = 0
    · rw [cfEvenModelIff hm he]
      exact (cfEvenRuleLocal eqs hm hv hN he
        (cfLateOfParts (cfPartIFromClosed cfCheckedClosed) (cfPartIIFromClosed cfCheckedClosed) hm)).symm
    · have hne : v ≠ Nb m := by omega
      simpa [hne] using cfOddRule eqs hm hv (show v % 2 = 1 by omega)

theorem corOddBit {m : ℕ} (hm : 3 ≤ m) {x : ℕ → ℕ} (hx : IsUlam 4 (b m) x)
    {N : ℕ} (ho : N % 2 = 1) (hN : N < Nb m) :
    cfTerm x N ↔ y m ((N + 3*b m + 4)/2) = 1 := by
  have hb := cfBFromK m hm
  have hk := cfKTwo m hm
  rw [corTermModel hm hx N hN.le, or_iff_left (ne_of_lt hN), cfOddModelIff ho]
  constructor
  · rintro ⟨d, hd, hy⟩
    rwa [show (N + 3*b m + 4)/2 = 8*K m + d by omega]
  · intro hy
    let n := (N + 3*b m + 4)/2
    change y m n = 1 at hy
    have hn : 1 ≤ n := by dsimp [n]; omega
    have hstart : 8*K m ≤ n := by
      by_contra! h
      have := (cfCheckedClosed.1 m hm).1 n hn h
      omega
    refine ⟨n - 8*K m, ?_, ?_⟩
    · dsimp [n] at *
      omega
    · simpa only [cfOffset, Nat.add_sub_of_le hstart] using hy

theorem corOddTable {m : ℕ} (hm : 3 ≤ m) {x : ℕ → ℕ} (hx : IsUlam 4 (b m) x)
    {N : ℕ} (ho : N % 2 = 1) (hN : N < Nb m) {l c r : ℤ}
    (hc : Coords m ((N + 3*b m + 4)/2) l c r) :
    cfTerm x N ↔ Y m l c r = 1 := by
  have hb := cfBFromK m hm
  have hk := cfKTwo m hm
  have scale := (cfEndpointScale hm).1
  rw [corOddBit hm hx ho hN,
    cfCheckedClosed.2 m hm _ (by omega) (by omega) l c r hc]
