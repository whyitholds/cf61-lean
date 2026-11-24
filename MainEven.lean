import MainModel
import MainCount
import Statement
open OneAdd CF61

theorem cfEvenShape {m : ℕ} (hm : 3 ≤ m) (s v : ℕ) :
    cfValuePair (cfModel m) (2*b m+2*s) v ↔
      (s=4 ∧ v=4) ∨ (s=4*K m+3 ∧ v=4) ∨ (s=8*K m+2 ∧ v=8*K m+2) ∨
      ∃ d, cfOffsetPair m s d ∧ v=b m+2*d := by
  have hb := cfBFromK m hm
  have hk := cfKTwo m hm
  constructor
  · rintro ⟨hv,lt,a,b'⟩
    rcases a with seed|⟨d,he,hd⟩ <;> rcases b' with seed'|⟨e,he',hd'⟩
    · unfold cfEvenSeed at seed seed'
      omega
    · unfold cfEvenSeed at seed; omega
    · unfold cfEvenSeed at seed'; omega
    · right; right; right
      refine ⟨d,⟨by omega,hd,?_⟩,he⟩
      simpa [show s-d=e by omega] using hd'
  · rintro (⟨hs,hv⟩|⟨hs,hv⟩|⟨hs,hv⟩|⟨d,⟨lt,b1,b2⟩,hv⟩)
    · refine ⟨by omega,by omega,Or.inl (Or.inl hv),Or.inl (Or.inr (Or.inl ?_))⟩; omega
    · refine ⟨by omega,by omega,Or.inl (Or.inl hv),Or.inl (Or.inr (Or.inr ?_))⟩; omega
    · refine ⟨by omega,by omega,Or.inl (Or.inr (Or.inl hv)),Or.inl (Or.inr (Or.inr ?_))⟩; omega
    · exact ⟨by omega,by omega,Or.inr ⟨d,hv,b1⟩,Or.inr ⟨s-d,by omega,b2⟩⟩

theorem cfEvenOrdinary (eqs : BitsEquations) {m : ℕ} (hm : 3 ≤ m) (s : ℕ)
    (h4 : s≠4) (h5 : s≠4*K m+3) (h6 : s≠8*K m+2) :
    (∃! v, cfValuePair (cfModel m) (2*b m+2*s) v) ↔ S m (16*K m+s)=1 := by
  rw [cfCountOffsets eqs hm]
  have shape : ∀ v, cfValuePair (cfModel m) (2*b m+2*s) v ↔
      ∃ d, cfOffsetPair m s d ∧ v=b m+2*d := by
    intro v; simp [cfEvenShape hm,h4,h5,h6]
  constructor
  · rintro ⟨v,hv,hu⟩
    obtain ⟨d,hd,he⟩ := (shape _).1 hv
    refine ⟨d,hd,?_⟩
    intro e h'
    have hh := hu _ ((shape _).2 ⟨e,h',rfl⟩)
    omega
  · rintro ⟨d,hd,hu⟩
    refine ⟨_,(shape _).2 ⟨d,hd,rfl⟩,?_⟩
    intro v hv
    obtain ⟨e,he,eq⟩ := (shape _).1 hv
    rw [hu _ he] at eq
    exact eq

theorem cfEvenExceptional (eqs : BitsEquations) {m s : ℕ} (hm : 3 ≤ m)
    (hs : s=4 ∨ s=4*K m+3 ∨ s=8*K m+2) :
    ¬ ∃! v, cfValuePair (cfModel m) (2*b m+2*s) v := by
  have hb := cfBFromK m hm
  have hk := cfKTwo m hm
  have w : ∃ d, cfOffsetPair m s d := by
    rcases hs with h|h|h
    · exact ⟨0,(cfShortPairShape eqs hm (s := s) (by omega)).2 (by omega)⟩
    · exact ⟨2,(cfShortPairShape eqs hm (s := s) (by omega)).2 (by omega)⟩
    · simpa [h] using (show ∃ d, cfOffsetPair m (8*K m+2) d from ⟨4,cfLateException eqs hm⟩)
  rintro ⟨v,hv,hu⟩
  obtain ⟨d,hd⟩ := w
  have hu' := hu _ ((cfEvenShape hm _ _).2 (Or.inr (Or.inr (Or.inr ⟨d,hd,rfl⟩))))
  rcases hs with h|h|h
  · have h' := hu _ ((cfEvenShape hm _ _).2 (Or.inl ⟨h,rfl⟩)); omega
  · have h' := hu _ ((cfEvenShape hm _ _).2 (Or.inr (Or.inl ⟨h,rfl⟩))); omega
  · have h' := hu _ ((cfEvenShape hm _ _).2 (Or.inr (Or.inr (Or.inl ⟨h,rfl⟩)))); omega

theorem cfEvenSmall {m t : ℕ} (hm : 3 ≤ m) (ht : t<2*b m) (he : t%2=0) :
    ¬ ∃ v, cfValuePair (cfModel m) t v := by
  have hb := cfBFromK m hm
  have hk := cfKTwo m hm
  rintro ⟨v,_,lt,a,b'⟩
  rcases a with seed|⟨d,hd,_⟩ <;> rcases b' with seed'|⟨e,he',_⟩ <;>
    unfold cfEvenSeed at * <;> omega

theorem cfEndpointScale {m : ℕ} (hm : 3 ≤ m) :
    Nb m+6*b m+8=2*n₀ m ∧ 24*K m+2<n₀ m := by
  have h := cfBFromK m hm
  have hk := cfKTwo m hm
  have hb : 7 ≤ b m := by omega
  unfold Nb n₀
  have hlarge : 4 ≤ 4*b m^2+2*b m := by nlinarith
  have heq : 4*b m^2+2*b m+6*b m+4=2*(32*K m^2) := by
    nlinarith [congrArg (fun x : ℕ => 4*x^2) h]
  constructor
  · omega
  · nlinarith [Nat.mul_le_mul_left (K m) hk]

theorem cfEvenRuleLocal (eqs : BitsEquations) {m T t : ℕ}
    (hm : 3 ≤ m) (ht : b m<t) (hle : t ≤ T) (he : t%2=0)
    (hlate : ∀ s, 4*K m+3<s → 2*b m+2*s ≤ T →
      (S m (16*K m+s)=1 ↔ 2*b m+2*s=Nb m)) :
    (∃! v, cfValuePair (cfModel m) t v) ↔ cfEvenSeed m t ∨ t=Nb m := by
  have hb := cfBFromK m hm
  have hk := cfKTwo m hm
  obtain ⟨scale,lower⟩ := cfEndpointScale hm
  by_cases small : t<2*b m
  · have h := cfEvenSmall hm small he
    constructor
    · rintro ⟨v,hv,_⟩; exact False.elim (h ⟨v,hv⟩)
    · rintro (seed|eq)
      · unfold cfEvenSeed at seed; omega
      · omega
  obtain ⟨s,hs⟩ : ∃ s, t=2*b m+2*s := ⟨(t-2*b m)/2,by omega⟩
  subst t
  by_cases exc : s=4 ∨ s=4*K m+3 ∨ s=8*K m+2
  · have h := cfEvenExceptional eqs hm exc
    apply iff_of_false h
    unfold cfEvenSeed
    omega
  rw [cfEvenOrdinary eqs hm s (by tauto) (by tauto) (by tauto)]
  unfold cfEvenSeed
  by_cases early : s ≤ 4*K m+3
  · rw [cfShortCount eqs hm early]; omega
  rw [hlate s (by omega) hle]
  omega

theorem cfLateOfParts (pi : CF61_PartI) (pii : CF61_PartII) {m : ℕ} (hm : 3 ≤ m)
    (s : ℕ) (hgt : 4*K m+3<s) (hle : 2*b m+2*s ≤ Nb m) :
    S m (16*K m+s)=1 ↔ 2*b m+2*s=Nb m := by
  obtain ⟨scale,lower⟩ := cfEndpointScale hm
  have hb := cfBFromK m hm
  by_cases last : 16*K m+s=n₀ m
  · rw [last]
    exact iff_of_true (pii.2 _ hm).1 (by omega)
  · have h := pi.2 _ hm (16*K m+s) (by omega) (by omega)
    omega
