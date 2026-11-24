import Mathlib

def piWord : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n+1, f => f 0+1024*piWord n (fun i => f (i+1))

def piBaseDigit (v i : ℕ) := (v >>> (10*i)) % 1024

theorem piBaseDigitSucc (x i : ℕ) :
    piBaseDigit x (i+1)=piBaseDigit (x/1024) i := by
  simp only [piBaseDigit,Nat.shiftRight_eq_div_pow,Nat.div_div_eq_div_mul]
  rw [show 10*(i+1)=10+10*i by omega, pow_add]
  rfl

theorem piWordExt {n : ℕ} {f g : ℕ → ℕ} (h : ∀ i, i<n → f i=g i) :
    piWord n f=piWord n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [piWord]
    rw [h 0 (by omega),ih (f:=fun i => f (i+1)) (g:=fun i => g (i+1)) (fun i hi => h _ (by omega))]

theorem piWordAdd (n : ℕ) (f g : ℕ → ℕ) :
    piWord n f+piWord n g=piWord n (fun i => f i+g i) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [piWord]
    rw [← ih (fun i => f (i+1)) (fun i => g (i+1))]
    omega

theorem piWordMul (n u : ℕ) (f : ℕ → ℕ) :
    u*piWord n f=piWord n (fun i => u*f i) := by
  induction n generalizing f with
  | zero => simp [piWord]
  | succ n ih =>
    simp only [piWord]
    rw [← ih (fun i => f (i+1))]
    ring

theorem piWordSub {n : ℕ} {f g : ℕ → ℕ} (h : ∀ i, i<n → g i ≤ f i) :
    piWord n f-piWord n g=piWord n (fun i => f i-g i) := by
  have hplus : piWord n (fun i => f i-g i)+piWord n g=piWord n f := by
    rw [piWordAdd]
    exact piWordExt fun i hi => Nat.sub_add_cancel (h i hi)
  omega

theorem piWordZero (n : ℕ) : piWord n (fun _ => 0)=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [piWord,ih]

theorem piBaseDigitWord {n : ℕ} {f : ℕ → ℕ} (h : ∀ i, i<n → f i<1024)
    {t : ℕ} (ht : t<n) : piBaseDigit (piWord n f) t=f t := by
  induction n generalizing t f with
  | zero => omega
  | succ n ih =>
    have hz := h 0 (by omega)
    cases t with
    | zero => simpa [piBaseDigit,piWord,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hz]
    | succ t =>
      rw [piBaseDigitSucc]
      simp only [piWord, Nat.add_mul_div_left _ _ (by decide : 0<1024), Nat.div_eq_of_lt hz,
        Nat.zero_add]
      exact ih (f:=fun i => f (i+1)) (fun i hi => h _ (by omega)) (by omega)

theorem piWordRecover {n x : ℕ} (h : x<1024^n) : piWord n (piBaseDigit x)=x := by
  induction n generalizing x with
  | zero => simp only [pow_zero] at h; change 0=x; omega
  | succ n ih =>
    have h2 : x/1024<1024^n := (Nat.div_lt_iff_lt_mul (by decide)).2 (by
      simpa [pow_succ] using h)
    change piBaseDigit x 0+1024*piWord n (fun i => piBaseDigit x (i+1))=x
    rw [show (fun i => piBaseDigit x (i+1))=piBaseDigit (x/1024) from funext (piBaseDigitSucc x), ih h2]
    change x%1024+1024*(x/1024)=x
    exact Nat.mod_add_div x 1024

theorem piSplitAnd {a b : ℕ} (ha : a<1024) (hb : b<1024) (c d : ℕ) :
    (a+1024*c) &&& (b+1024*d) = (a &&& b)+1024*(c &&& d) := by
  have h := Nat.mod_add_div ((a+1024*c) &&& (b+1024*d)) (2^10)
  rw [Nat.and_mod_two_pow,Nat.and_div_two_pow] at h
  norm_num only [Nat.reducePow] at h
  simpa only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb,
    Nat.add_mul_div_left _ _ (by decide : 0<1024),Nat.div_eq_of_lt ha,Nat.div_eq_of_lt hb,
    Nat.zero_add] using h.symm

theorem piSplitOr {a b : ℕ} (ha : a<1024) (hb : b<1024) (c d : ℕ) :
    (a+1024*c) ||| (b+1024*d) = (a ||| b)+1024*(c ||| d) := by
  have h := Nat.mod_add_div ((a+1024*c) ||| (b+1024*d)) (2^10)
  rw [Nat.or_mod_two_pow,Nat.or_div_two_pow] at h
  norm_num only [Nat.reducePow] at h
  simpa only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb,
    Nat.add_mul_div_left _ _ (by decide : 0<1024),Nat.div_eq_of_lt ha,Nat.div_eq_of_lt hb,
    Nat.zero_add] using h.symm

theorem piWordAnd {n : ℕ} {f g : ℕ → ℕ}
    (hf : ∀ i, i<n → f i<1024) (hg : ∀ i, i<n → g i<1024) :
    piWord n f &&& piWord n g=piWord n (fun i => f i &&& g i) := by
  induction n generalizing f g with
  | zero => simp [piWord]
  | succ n ih =>
    simp only [piWord]
    rw [piSplitAnd (hf 0 (by omega)) (hg 0 (by omega))]
    rw [ih (f:=fun i => f (i+1)) (g:=fun i => g (i+1))
      (fun i hi => hf _ (by omega)) (fun i hi => hg _ (by omega))]

theorem piWordOr {n : ℕ} {f g : ℕ → ℕ}
    (hf : ∀ i, i<n → f i<1024) (hg : ∀ i, i<n → g i<1024) :
    piWord n f ||| piWord n g=piWord n (fun i => f i ||| g i) := by
  induction n generalizing f g with
  | zero => simp [piWord]
  | succ n ih =>
    simp only [piWord]
    rw [piSplitOr (hf 0 (by omega)) (hg 0 (by omega))]
    rw [ih (f:=fun i => f (i+1)) (g:=fun i => g (i+1))
      (fun i hi => hf _ (by omega)) (fun i hi => hg _ (by omega))]
