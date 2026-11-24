import PartILowSpec
import PartIPacked
import WeightPure

set_option maxRecDepth 30000 in
theorem pwNodup : pwAll.Nodup := by
  let heads := (List.finRange 3).product (List.finRange 3)
  let tags := (List.finRange 6).product (List.finRange 6)
  have he : pwAll = heads.product tags := by decide +kernel
  rw [he]
  exact ((List.nodup_finRange 3).product (List.nodup_finRange 3)).product
    ((List.nodup_finRange 6).product (List.nodup_finRange 6))

theorem pwMem (t : PWChoice) : t ∈ pwAll := by
  rcases t with ⟨⟨a,b⟩,x,y⟩
  simp [pwAll]

theorem pwTagS (t : Fin 6) : PITagShift t = pwShift t := by
  fin_cases t <;> rfl

theorem pwTagR (t : Fin 6) : PITagResidue t = pwResidue t := by
  fin_cases t <;> rfl

theorem pwRuleIff (ah d r j e c b f g : ℕ) (T : PWChoice) :
    pwRule ah d r j e c b f g T = true ↔ piTailPred ah d r j e c b f g T := by
  simp only [pwRule, Bool.and_eq_true, decide_eq_true_eq, piTailPred, piCmpUp,piCmp,
    piHU,piHV,piFits,pwFit,pwTagS,pwTagR]
  tauto

theorem pwCard (ah d r j e c b f g : ℕ) :
    (piTailChoices ah d r j e c b f g).card = pwAll.countP (pwRule ah d r j e c b f g) := by
  have he : piTailChoices ah d r j e c b f g =
      pwAll.toFinset.filter (fun T => pwRule ah d r j e c b f g T = true) := by
    ext T
    simp only [piTailChoices, Finset.mem_filter, Finset.mem_univ, true_and,
      List.mem_toFinset, pwMem, pwRuleIff]
  rw [he]
  simpa only [decide_eq_true_eq, Bool.decide_eq_true] using
    (List.Nodup.card_eq_countP (P := fun T => pwRule ah d r j e c b f g T = true) pwNodup)

theorem pwTableEq : piWeights = pwTable := rfl
