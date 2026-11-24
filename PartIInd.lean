import PartIMoves
import PartIAuto

set_option maxRecDepth 10000

def piLowRel (k a v row : ℕ) : Prop :=
  piCol row 72 = min 2 a ∧ piCol row 73 = min 1 v ∧
  ∀ s t : ℕ, s < 72 → t < 8 →
    piDigit (piCol row s) t = min 4 (piNumLow k a v (t/2) (t%2) s)

theorem piStartRel : piLowRel 1 0 0 piStart := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  have h : ∀ (s : Fin 72) (t : Fin 8),
      piDigit (piCol piStart s.val) t.val = min 4 (piNumLow 1 0 0 (t.val/2) (t.val%2) s.val) := by
    decide +kernel
  exact fun s t hs ht => h ⟨s,hs⟩ ⟨t,ht⟩

theorem piClipSum {α : Type*} (s : Finset α) (f : α → ℕ) :
    min 4 (∑ x ∈ s, min 4 (f x)) = min 4 (∑ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert t s h ih =>
    rw [Finset.sum_insert h, Finset.sum_insert h]
    omega

theorem piClipMulSum {α : Type*} (s : Finset α) (f w : α → ℕ) :
    min 4 (∑ x ∈ s, min 4 (f x) * w x) = min 4 (∑ x ∈ s, f x * w x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s h ih =>
    rw [Finset.sum_insert h, Finset.sum_insert h]
    by_cases hf : f a ≤ 4
    · rw [min_eq_right hf]; omega
    · by_cases hw : w a = 0
      · rw [hw]; simp only [Nat.mul_zero, Nat.zero_add]; exact ih
      · have hm : 4 ≤ (f a)*(w a) := by nlinarith [Nat.one_le_iff_ne_zero.mpr hw]
        rw [min_eq_left (by omega : 4 ≤ f a)]
        omega

def piLiftRule : Prop :=
  ∀ d a v l s j e : ℕ, a < 2^d → v < 2^d → l < 4 → s < 72 → j < 4 → e < 2 →
    piNumLow (2*2^d) (a+2^d*(l/2)) (v+2^d*(l%2)) j e s =
    ∑ t ∈ piMoveSet l s, piNumLow (2^d) a v j e t.1

def piMovesAgree (old l new : ℕ) : Prop :=
  ∀ s t : ℕ, s < 72 → t < 8 →
    piDigit (piCol new s) t = min 4 (∑ q ∈ piMoveSet l s, piDigit (piCol old q.1) t)

theorem piColBoundOfMove (l s : ℕ) {q : ℕ × (Fin 3 × Fin 3)} (h : q ∈ piMoveSet l s) : q.1 < 72 := by
  simp only [piMoveSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
  exact h.1.1

theorem piRelStep (hLift : piLiftRule) {d a v l old new : ℕ} (ha : a < 2^d) (hv : v < 2^d)
    (hl : l < 4) (hOld : piLowRel (2^d) a v old) (hLane : piMovesAgree old l new)
    (hA : piCol new 72 = piFlagA (d == 0) l (piCol old 72))
    (hV : piCol new 73 = piFlagV l (piCol old 73)) :
    piLowRel (2*2^d) (a+2^d*(l/2)) (v+2^d*(l%2)) new := by
  obtain ⟨hAo,hVo,hLo⟩ := hOld
  have hK : 0 < 2^d := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [hA,hAo]
    unfold piFlagA
    by_cases hl2 : 2 ≤ l
    · rw [if_pos hl2, show l/2=1 by omega, Nat.mul_one]
      by_cases hd : d = 0
      · subst d; simp_all
      · have h2 : 2 ≤ 2^d := by
          calc
            2 = 2^1 := by norm_num
            _ ≤ 2^d := Nat.pow_le_pow_right (by omega) (by omega)
        simp [hd]; omega
    · rw [if_neg hl2, show l/2=0 by omega, Nat.mul_zero, Nat.add_zero]
  · rw [hV,hVo]; unfold piFlagV
    by_cases h : l%2=0
    · simp [h]
    · have h1 : l%2=1 := by omega
      simp [h,h1]; omega
  · intro s t hs ht
    rw [hLane s t hs ht, hLift d a v l s (t/2) (t%2) ha hv hl hs (by omega) (by omega)]
    calc
      _ = min 4 (∑ q ∈ piMoveSet l s, min 4 (piNumLow (2^d) a v (t/2) (t%2) q.1)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro q hq
        exact hLo _ _ (piColBoundOfMove _ _ hq) ht
      _ = _ := piClipSum _ _

def piVerifiedFirst : Prop :=
  ∀ l : ℕ, l < 4 → ∃ i : ℕ, i < 683 ∧ piMovesAgree piStart l piRowList[i]! ∧
    piCol piRowList[i]! 72 = piFlagA true l (piCol piStart 72) ∧
    piCol piRowList[i]! 73 = piFlagV l (piCol piStart 73)

def piBounded (v : ℕ) : Prop := ∀ s t : ℕ, s < 72 → t < 8 → piDigit (piCol v s) t ≤ 4

theorem piRelBounded {k a v row : ℕ} (h : piLowRel k a v row) : piBounded row := by
  intro s t hs ht; rw [h.2.2 s t hs ht]; exact min_le_left _ _

def piVerifiedStep : Prop :=
  ∀ i l : ℕ, i < 683 → l < 4 → piBounded piRowList[i]! → ∃ j : ℕ, j < 683 ∧ piMovesAgree piRowList[i]! l piRowList[j]! ∧
    piCol piRowList[j]! 72 = piFlagA false l (piCol piRowList[i]! 72) ∧
    piCol piRowList[j]! 73 = piFlagV l (piCol piRowList[i]! 73)

theorem piEitherNat (x : ℕ) (hx : x<2) : x=0 ∨ x=1 := by omega

theorem piReach (liftRule : piLiftRule) (first : piVerifiedFirst) (step : piVerifiedStep)
    (d : ℕ) (hd : 0 < d) (a v : ℕ) (ha : a < 2^d) (hv : v < 2^d) :
    ∃ i : ℕ, i < 683 ∧ piLowRel (2^d) a v piRowList[i]! := by
  induction d generalizing a v with
  | zero => omega
  | succ d ih =>
    let k := 2^d
    have hk : 0 < k := by dsimp [k]; positivity
    have har : a < 2*k := by simpa [k,pow_succ, Nat.mul_comm] using ha
    have hvr : v < 2*k := by simpa [k,pow_succ, Nat.mul_comm] using hv
    have hau : a/k < 2 := (Nat.div_lt_iff_lt_mul hk).mpr har
    have hvu : v/k < 2 := (Nat.div_lt_iff_lt_mul hk).mpr hvr
    let l := 2*(a/k) + v/k
    have hl : l < 4 := by dsimp [l]; omega
    have hA := piEitherNat (a/k) hau
    have hV := piEitherNat (v/k) hvu
    have hla : l/2 = a/k := by rcases hA with z|z <;> rcases hV with w|w <;> simp [l,z,w]
    have hlv : l%2 = v/k := by rcases hA with z|z <;> rcases hV with w|w <;> simp [l,z,w]
    have hnext : ∀ old new, piLowRel k (a%k) (v%k) old → piMovesAgree old l new →
        piCol new 72 = piFlagA (d == 0) l (piCol old 72) →
        piCol new 73 = piFlagV l (piCol old 73) → piLowRel (2^(d+1)) a v new := by
      intro old new ho hn hA hV
      have h := piRelStep liftRule (d:=d) (Nat.mod_lt a hk) (Nat.mod_lt v hk) hl ho hn hA hV
      simpa only [← show k = 2^d from rfl,hla,hlv,Nat.mod_add_div, pow_succ, Nat.mul_comm k 2] using h
    by_cases hd0 : d = 0
    · obtain ⟨i,hi,hm,hA,hV⟩ := first l hl
      refine ⟨i,hi,hnext piStart _ ?_ hm (by simpa [hd0] using hA) hV⟩
      simpa only [k, hd0, pow_zero, Nat.mod_one] using piStartRel
    · obtain ⟨i,hi,ho⟩ := ih (by omega) _ _ (Nat.mod_lt a hk) (Nat.mod_lt v hk)
      obtain ⟨j,hj,hm,hA,hV⟩ := step i l hi hl (piRelBounded ho)
      exact ⟨j,hj,hnext _ _ ho hm (by rw [show (d == 0) = false by exact beq_eq_false_iff_ne.mpr hd0]; exact hA) hV⟩
