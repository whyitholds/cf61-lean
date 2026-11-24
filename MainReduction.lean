import MainEven
import MainOdd
open OneAdd CF61

theorem cfModelOddSeed {m t : ℕ} (hm : 3 ≤ m) (he : t%2=0) :
    cfModel m t ↔ cfEvenSeed m t := by
  have hb := cfBFromK m hm
  constructor
  · rintro (h|⟨d,e,_⟩)
    · exact h
    · omega
  · exact Or.inl

theorem cfMainLocal (eqs : BitsEquations) {m T : ℕ} (hm : 3 ≤ m) (hT : T ≤ Nb m)
    (hlate : ∀ s, 4*K m+3<s → 2*b m+2*s ≤ T →
      (S m (16*K m+s)=1 ↔ 2*b m+2*s=Nb m)) {x : ℕ→ℕ} (hx : IsUlam 4 (b m) x)
    (t : ℕ) (hle : t ≤ T) : (cfTerm x t ∧ t%2=0) ↔
    t=4 ∨ t=2*b m+4 ∨ t=4*b m+4 ∨ t=Nb m := by
  have hb := cfBFromK m hm
  have hk := cfKTwo m hm
  obtain ⟨scale,lower⟩ := cfEndpointScale hm
  have heNb : Nb m%2=0 := by omega
  let P := fun v => cfModel m v ∨ v=Nb m
  have init : ∀ v ≤ b m, P v ↔ v=4 ∨ v=b m := by
    intro v hv
    change (cfEvenSeed m v ∨ (∃ d, v=b m+2*d ∧ cfOffset m d=1)) ∨ v=Nb m ↔ _
    unfold cfEvenSeed
    constructor
    · rintro ((h|⟨d,e,_⟩)|h) <;> omega
    · rintro (h|h)
      · exact Or.inl (Or.inl (Or.inl h))
      · have zero := (eqs m hm).2.1
        exact Or.inl (Or.inr ⟨0,by omega,by simpa [cfOffset] using zero⟩)
  have law : ∀ v, b m<v → v ≤ T → (P v ↔ ∃! w, cfValuePair P v w) := by
    intro v hv hN
    have pairs : ∀ w, cfValuePair P v w ↔ cfValuePair (cfModel m) v w := by
      intro w
      unfold cfValuePair
      by_cases h : 0<w ∧ w<v-w
      · have h1 : w≠Nb m := by omega
        have h2 : v-w≠Nb m := by omega
        simp [P,h1,h2]
      · tauto
    rw [existsUnique_congr pairs]
    change (cfModel m v ∨ v=Nb m) ↔ _
    by_cases hEv : v%2=0
    · rw [cfModelOddSeed hm hEv]
      exact (cfEvenRuleLocal eqs hm hv hN hEv hlate).symm
    · have hne : v≠Nb m := by omega
      simpa [hne] using cfOddRule eqs hm hv (show v%2=1 by omega)
  have member := cfTermDetermined hx (by decide) P init law t hle
  rw [member]
  by_cases hEv : t%2=0
  · change ((cfModel m t ∨ t=Nb m) ∧ _) ↔ _
    rw [cfModelOddSeed hm hEv]
    unfold cfEvenSeed
    omega
  · omega

theorem cfMainOfParts (exi : UlamExists) (pi : CF61_PartI) (pii : CF61_PartII) : CF61_Main := by
  refine ⟨exi,?_⟩
  intro m hm
  dsimp only
  intro x hx t hle
  exact cfMainLocal pi.1 hm le_rfl (cfLateOfParts pi pii hm) hx t hle
