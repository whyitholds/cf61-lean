import Mathlib

def piWCoef (ps : List (ℕ × ℕ × ℕ)) (s t : ℕ) :=
  (ps.map fun p => if p.1 = s ∧ p.2.1 = t then p.2.2 else 0).sum

theorem piWFold (ps : List (ℕ × ℕ × ℕ)) (f : ℕ → ℕ → ℕ) (a : ℕ) :
    ps.foldl (fun n p => n+f p.1 p.2.1*p.2.2) a =
    a + (ps.map (fun p => f p.1 p.2.1*p.2.2)).sum := by
  induction ps generalizing a with
  | nil => simp
  | cons p ps ih => simp only [List.foldl_cons, List.map_cons,List.sum_cons,ih]; omega

theorem piWSparse (N M : ℕ) (ps : List (ℕ × ℕ × ℕ)) (f : ℕ → ℕ → ℕ)
    (h : ∀ p ∈ ps, p.1 < N ∧ p.2.1 < M) :
    ps.foldl (fun n p => n+f p.1 p.2.1*p.2.2) 0 =
    ∑ s ∈ Finset.range N, ∑ t ∈ Finset.range M, f s t * piWCoef ps s t := by
  rw [piWFold,Nat.zero_add]
  induction ps with
  | nil => simp [piWCoef]
  | cons p ps ih =>
    have hp := h p (by simp)
    have hl : ∀ q ∈ ps, q.1 < N ∧ q.2.1 < M := fun q hq => h _ (List.mem_cons_of_mem _ hq)
    have he : ∀ s t, piWCoef (p::ps) s t = (if p.1=s ∧ p.2.1=t then p.2.2 else 0)+piWCoef ps s t := by
      intro s t
      simp [piWCoef]
    simp only [List.map_cons,List.sum_cons,he,mul_add,Finset.sum_add_distrib,ih hl]
    apply congrArg (fun z => z + _)
    symm
    calc
      _ = ∑ s ∈ Finset.range N, ∑ t ∈ Finset.range M,
          if p.1=s then (if p.2.1=t then f s t*p.2.2 else 0) else 0 := by
            apply Finset.sum_congr rfl
            intro s hs
            apply Finset.sum_congr rfl
            intro t ht
            by_cases h1 : p.1=s <;> by_cases h2 : p.2.1=t <;> simp [h1,h2]
      _ = f p.1 p.2.1*p.2.2 := by
          simp [Finset.sum_ite_irrel, Finset.mem_range.mpr hp.1,Finset.mem_range.mpr hp.2, hp.1,hp.2]
