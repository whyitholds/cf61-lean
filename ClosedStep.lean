import ClosedGeo
open CF61

theorem cfClosedBit (m n : ℕ) (hm : 3 ≤ m) (hn : 1 ≤ n) : y m n ≤ 1 := by
  rcases cfBitsEquations m hm with ⟨h₁,h₂,h₃⟩
  rcases lt_trichotomy n (8*K m) with h|h|h
  · rw [h₁ n hn h]; decide
  · subst n; omega
  · rw [h₃ n h]; split <;> decide

theorem cfClosedSum (a b c : ℕ) (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) :
    ((if a+b+c=1 then 1 else 0 : ℕ) = 1) ↔
      cfClosedOne (a=1) (b=1) (c=1) := by
  unfold cfClosedOne
  split <;> omega

theorem cfClosedRunStep (m n : ℕ) (hm : 3 ≤ m) (hp : 8*K m<n) (l t r : ℤ)
    (hl : 0 ≤ l) (hu : l<2*(K m:ℤ)) (ht : 0 ≤ t) (ht' : t<4*(K m:ℤ)) (hr : 1 ≤ r) (hr' : r ≤ 4)
    (E : (n:ℤ)=16*(K m:ℤ)*l+8*(K m:ℤ)+4*t+r)
    (ih : ∀ i : ℕ, i<n → 1 ≤ i → ∀ l c r : ℤ, Coords m i l c r → y m i=Y m l c r)
    (step : cfClosedLocal m) : y m n=1 ↔ cfClosedRow (K m) l t r := by
  let k : ℤ := K m
  have kp : 0<K m := by unfold K; positivity
  have kp' : 0 < k := by dsimp only [k]; exact_mod_cast kp
  have prev (a : ℕ) (d s : ℤ) (ha : 0<a) (has : a<n)
      (hd : 0 ≤ d) (hd' : d ≤ 4*k) (hs : 1 ≤ s) (hs' : s ≤ 4) (e : 4*d+r-s=(a:ℤ)) :
      y m (n-a)=1 ↔ cfClosedPrev k l t d s := by
    have B := cfClosedBack k n l t r a d s E e
    have C : ((n-a:ℕ):ℤ)=(n:ℤ)-(a:ℤ) := Nat.cast_sub (by omega)
    rw [← C] at B
    exact cfClosedPrevRead m (n-a) l t d s hl hu ht ht' hd hd' hs hs'
      (ih (n-a) (by omega) (by omega)) B.1 B.2
  have p1 := prev 2 (if r ≤ 2 then 1 else 0) (if r ≤ 2 then r+2 else r-2)
    (by decide) (by omega) (by split <;> omega) (by split <;> omega)
    (by split <;> omega) (by split <;> omega) (by split_ifs <;> omega)
  have p2 := prev (4*K m+1) (if r=1 then k+1 else k) (if r=1 then 4 else r-1)
    (by omega) (by omega) (by split <;> omega) (by split <;> omega)
    (by split <;> omega) (by split <;> omega)
    (by push_cast; change _ = 4*k+1; split_ifs <;> omega)
  have p3 := prev (8*K m) (2*k) r (by omega) hp (by omega) (by omega) hr hr'
    (by push_cast; change 4*(2*k)+r-r=8*k; ring)
  have eq := (cfBitsEquations m hm).2.2 n hp
  rw [show n-4*K m-1=n-(4*K m+1) by omega] at eq
  rw [eq,cfClosedSum _ _ _ (cfClosedBit m (n-2) hm (by omega))
    (cfClosedBit m (n-(4*K m+1)) hm (by omega)) (cfClosedBit m (n-8*K m) hm (by omega)),p1,p2,p3]
  exact (step l t r hl hu ht ht' hr hr').symm
