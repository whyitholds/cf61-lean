import ClosedBase
import BitBase
open CF61

theorem cfClosedBlock (n k l t r : ℤ) (hk : 0<k) (hn : 1≤n) (hm : n ≤ 32*k^2+8*k)
    (ht : 0≤t) (ht' : t<4*k) (hr : 1≤r) (hr' : r≤4) (E : n=16*k*l+8*k+4*t+r) :
    -1≤l ∧ l<2*k := by
  constructor
  · by_contra! h
    have h' : l+2≤0 := by omega
    have p := mul_nonpos_of_nonneg_of_nonpos hk.le h'
    nlinarith only [E,p,ht',hr',hn,hk]
  · by_contra! h
    have p := mul_nonneg hk.le (sub_nonneg.mpr h)
    nlinarith only [E,p,hm,ht,hr]

theorem cfClosedNormCoord (k l c t r n : ℤ) (E : n=16*k*l+4*c+r) (T : 2*k+t=c) :
    n=16*k*l+8*k+4*t+r := by linear_combination E-4*T

theorem cfClosedOrigin (k n t r : ℤ) (ht : t<4*k) (hr : 1≤r) (hr' : r≤4)
    (E : n=16*k*(-1)+8*k+4*t+r) : n≤8*k ∧ (n=8*k ↔ r=4 ∧ t=4*k-1) := by
  ring_nf at E
  omega

theorem cfClosedPost (n k l t r : ℤ) (hk : 0<k) (hl : 0≤l) (ht : 0≤t) (hr : 1≤r)
    (E : n=16*k*l+8*k+4*t+r) : 8*k<n := by nlinarith only [E,mul_nonneg hk.le hl,ht,hr]

theorem cfClosedBack (k n l t r a d s : ℤ) (E : n=16*k*l+8*k+4*t+r) (h : 4*d+r-s=a) :
    n-a=16*k*(l-1)+4*(2*k+(t+4*k-d))+s ∧ n-a=16*k*l+4*(2*k+(t-d))+s := by
  constructor <;> linear_combination E+h

theorem cfClosedPrevRead (m n : ℕ) (l t d s : ℤ)
    (hl : 0≤l) (hu : l<2*(K m:ℤ)) (ht : 0≤t) (ht' : t<4*(K m:ℤ))
    (hd : 0≤d) (hd' : d≤4*(K m:ℤ)) (hs : 1≤ s) (hs' : s≤4)
    (iH : ∀ l c r : ℤ, Coords m n l c r → y m n = Y m l c r)
    (eb : (n:ℤ)=16*(K m:ℤ)*(l-1)+4*(2*(K m:ℤ)+(t+4*(K m:ℤ)-d))+s)
    (es : (n:ℤ)=16*(K m:ℤ)*l+4*(2*(K m:ℤ)+(t-d))+s) :
    y m n=1 ↔ cfClosedPrev (K m) l t d s := by
  let k : ℤ := K m
  by_cases h : t<d
  · let v := t+4*k-d
    have hv : 0≤v := by dsimp [v,k]; omega
    have hv' : v<4*(K m:ℤ) := by dsimp [v,k]; omega
    have ec : Coords m n (l-1) (2*k+v) s := ⟨eb,by dsimp [k]; omega,by dsimp [k]; omega,hs,hs'⟩
    rw [iH _ _ _ ec]
    simpa only [cfClosedPrev,if_pos h] using cfClosedRowIff m (l-1) v s (by omega) (by omega) hv hv'
  · let v := t-d
    have hv : 0≤v := by dsimp [v]; omega
    have hv' : v<4*(K m:ℤ) := by dsimp [v]; omega
    have ec : Coords m n l (2*k+v) s := ⟨es,by dsimp [k]; omega,by dsimp [k]; omega,hs,hs'⟩
    rw [iH _ _ _ ec]
    simpa only [cfClosedPrev,if_neg h] using cfClosedRowIff m l v s (by omega) hu hv hv'
