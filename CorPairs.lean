import Mathlib

def corPairs (j : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (2^j) ×ˢ Finset.range (2^j)).filter fun p => p.1 &&& p.2 = 0

theorem corMemPairs {j u v : ℕ} :
    (u,v) ∈ corPairs j ↔ u < 2^j ∧ v < 2^j ∧ u &&& v = 0 := by
  simp [corPairs, and_assoc]

theorem corPairDigit {u v : ℕ} :
    u &&& v = 0 ↔ u/2 &&& (v/2) = 0 ∧ ¬(u%2 = 1 ∧ v%2 = 1) := by
  have := Nat.and_div_two (a := u) (b := v)
  have := Nat.and_mod_two_eq_one (a := u) (b := v)
  omega

def corLowDigit (i : Fin 3) : ℕ × ℕ := ![(0,0), (1,0), (0,1)] i

theorem corLowDigitBounds (i : Fin 3) :
    (corLowDigit i).1 < 2 ∧ (corLowDigit i).2 < 2 ∧
    ¬((corLowDigit i).1 = 1 ∧ (corLowDigit i).2 = 1) := by
  fin_cases i <;> decide

def corAppendDigit (w : (ℕ × ℕ) × Fin 3) : ℕ × ℕ :=
  (2*w.1.1 + (corLowDigit w.2).1, 2*w.1.2 + (corLowDigit w.2).2)

theorem corAppendInj : Function.Injective corAppendDigit := by
  rintro ⟨⟨u,v⟩,i⟩ ⟨⟨u',v'⟩,i'⟩ h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  change 2*u + (corLowDigit i).1 = 2*u' + (corLowDigit i').1 at h₁
  change 2*v + (corLowDigit i).2 = 2*v' + (corLowDigit i').2 at h₂
  obtain ⟨ha,hb,_⟩ := corLowDigitBounds i
  obtain ⟨ha',hb',_⟩ := corLowDigitBounds i'
  have hi : Function.Injective corLowDigit := by decide
  have he : i = i' := hi (Prod.ext (by omega) (by omega))
  obtain rfl : u = u' := by omega
  obtain rfl : v = v' := by omega
  rw [he]

theorem corPairsCard (j : ℕ) : (corPairs j).card = 3^j := by
  induction j with
  | zero => decide
  | succ j ih =>
    have step : ((corPairs j) ×ˢ (Finset.univ : Finset (Fin 3))).card =
        (corPairs (j+1)).card := by
      apply Finset.card_bij (fun w _ => corAppendDigit w)
      · rintro ⟨⟨u,v⟩,i⟩ hw
        obtain ⟨hu,hv,hd⟩ := corMemPairs.mp (Finset.mem_product.mp hw).1
        obtain ⟨ha,hb,hl⟩ := corLowDigitBounds i
        apply corMemPairs.mpr
        dsimp only [corAppendDigit, Prod.fst, Prod.snd]
        rw [pow_succ, corPairDigit]
        refine ⟨by omega, by omega, ?_, by omega⟩
        rwa [show (2*u+(corLowDigit i).1)/2 = u by omega,
          show (2*v+(corLowDigit i).2)/2 = v by omega]
      · exact fun _ _ _ _ h => corAppendInj h
      · rintro ⟨u,v⟩ h
        obtain ⟨hu,hv,hd⟩ := corMemPairs.mp h
        rw [pow_succ] at hu hv
        obtain ⟨hh,hl⟩ := corPairDigit.mp hd
        have hit : ∃ i, corLowDigit i = (u%2,v%2) := by
          by_cases ha : u%2 = 1
          · exact ⟨1, Prod.ext (by change 1 = _; omega) (by change 0 = _; omega)⟩
          by_cases hb : v%2 = 1
          · exact ⟨2, Prod.ext (by change 0 = _; omega) (by change 1 = _; omega)⟩
          · exact ⟨0, Prod.ext (by change 0 = _; omega) (by change 0 = _; omega)⟩
        obtain ⟨i,hi⟩ := hit
        refine ⟨((u/2,v/2),i), Finset.mem_product.mpr
          ⟨corMemPairs.mpr ⟨by omega, by omega, hh⟩, Finset.mem_univ _⟩, ?_⟩
        apply Prod.ext <;> simp only [corAppendDigit, hi] <;> omega
    rw [← step, Finset.card_product, ih, Finset.card_univ, Fintype.card_fin, pow_succ]
