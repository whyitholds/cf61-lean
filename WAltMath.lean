import WAltPure
import Mathlib

theorem waResidueBound (x : Fin 6) : pwResidue x ≤ 3 := by
  fin_cases x <;> decide

theorem waArith (q t h v e : ℕ) (f g : Bool) (hq : q < 32) (he : e < 8) :
    ((if h < 2 ∧ f = true ∧ g = true then
      some (16*h+4*(v%4)+e%4,2*(v/4)+e/4) else none) = some (q,t)) ↔
    (f && g && decide (h = q/16) && decide (v = q/4%4 + 4*(t/2)) &&
      decide (e = q%4 + 4*(t%2))) = true := by
  by_cases hh : h < 2 <;> cases f <;> cases g <;> simp [hh] <;> omega

theorem waKeySpec {q s t : ℕ} (hq : q < 32) (T : PWChoice) :
    waRuleKey s T = some (q,t) ↔
      pwRule (q/16) (q/4%4) (q%4) (t/2) (t%2)
        (s/18) (s/9%2) (s/3%3) (s%3) T = true := by
  rcases T with ⟨⟨a,b⟩,x,y⟩
  let h := s/18 + waU a + waU b
  let v := s/9%2 + waV a + waV b + pwShift x + pwShift y
  let e := pwResidue x + pwResidue y
  let f := pwFit (waCmp (waU a) (waV a) (s/3%3)) x
  let g := pwFit (waCmp (waU b) (waV b) (s%3)) y
  have he : e < 8 := by dsimp only [e]; have := waResidueBound x; have := waResidueBound y; omega
  change (if h<2 ∧ f = true ∧ g = true then some (16*h+4*(v%4)+e%4,2*(v/4)+e/4) else none) =
    some (q,t) ↔ (f && g && decide (h = q/16) && decide (v = q/4%4 + 4*(t/2)) &&
      decide (e = q%4 + 4*(t%2))) = true
  exact waArith q t h v e f g hq he

theorem waFromRule {q s t : ℕ} (hq : q < 32) :
    (pwAll.filterMap (waRuleKey s)).count (q,t) =
      pwAll.countP (pwRule (q/16) (q/4%4) (q%4) (t/2) (t%2)
        (s/18) (s/9%2) (s/3%3) (s%3)) := by
  rw [List.count_filterMap]
  apply List.countP_congr
  intro x _
  simpa only [beq_iff_eq] using waKeySpec (s := s) hq x

theorem waRowCount (ps : List (ℕ×ℕ×ℕ)) (q i s t : ℕ) :
    (ps.flatMap (waEntry i s)).count (q,t) =
    if i=q then (ps.map (fun p => if p.1=s ∧ p.2.1=t then p.2.2 else 0)).sum else 0 := by
  rw [List.count_flatMap]
  by_cases hi : i=q
  · subst i
    simp only [ite_true]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p _
    rcases p with ⟨s',t',w⟩
    by_cases hs : s'=s <;> by_cases ht : t'=t <;>
      simp [Function.comp_def, waEntry, hs, ht, List.count_replicate]
  · rw [if_neg hi]
    suffices h : ps.map (List.count (q,t) ∘ waEntry i s) = ps.map (fun _ => 0) by simp [h]
    apply List.map_congr_left
    intro p _
    rcases p with ⟨s',t',w⟩
    by_cases hs : s'=s <;> simp [Function.comp_def, waEntry, hs, hi, List.count_replicate]

theorem waOfTable {q s t : ℕ} (hq : q < 32) :
    (waTableKeys s).count (q,t) = pwWeight q s t := by
  rw [waTableKeys, List.count_flatMap]
  simp only [Function.comp_def, waRowCount]
  rw [← List.sum_toFinset _ List.nodup_range]
  simp [pwWeight, hq]

theorem waWeightOfPass {q s t : ℕ} (hq : q < 32) (hs : waPass s = true) :
    pwCheck q s t = true := by
  unfold waPass at hs
  have h := (List.isPerm_iff.mp hs).count_eq (q,t)
  rw [waOfTable hq,waFromRule hq] at h
  exact beq_iff_eq.mpr h.symm
