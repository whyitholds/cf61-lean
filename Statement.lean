import UlamDefs
import Bits

open OneAdd CF61

/-! Six statements on Cassaigne and Finch's Conjecture 6.1 and the even terms of U(4, 2^m − 1).
CF61_Main is on UlamDefs alone (its `IsUlam`, `UlamExists`, unchanged); the next four are on Bits.lean (the
bits y, S, the coordinates, the table Y) and carry `BitsEquations` as a conjunct; the sixth, CF61_Coords, reads only
Bits.lean's `Coords` (no bit, so no `BitsEquations`).  Every
quotation in guillemets is verbatim from the note.  The rule: «the increasing sequence whose first two
terms are $a$ and $b$ and each of whose further terms is the least integer greater than the previous term that has
exactly one representation as a sum of two distinct earlier terms.»  A sequence obeying it from (4, b) is `x` with
`IsUlam 4 b x`, indexed from 1 (x 1 = 4, x 2 = b); an even term is a value τ = x i (i ≥ 1) with τ even. -/

/-- THE MAIN THEOREM, on the Ulam definitions alone, for every sequence obeying the rule, with the existence clause:
«Let $m\ge3$ and $b=2^m-1$. The even terms of $U(4,b)$ not exceeding $\Nb=4b^2+2b-4$ are exactly $4$, $2b+4$, $4b+4$
and $\Nb$.» -/
def CF61_Main : Prop :=
  UlamExists ∧
  ∀ m : ℕ, 3 ≤ m →
    let b := 2 ^ m - 1
    let Nb := 4 * b ^ 2 + 2 * b - 4
    ∀ x : ℕ → ℕ, IsUlam 4 b x →
      ∀ τ : ℕ, τ ≤ Nb →
        (((∃ i : ℕ, 1 ≤ i ∧ x i = τ) ∧ τ % 2 = 0) ↔ (τ = 4 ∨ τ = 2 * b + 4 ∨ τ = 4 * b + 4 ∨ τ = Nb))

/-- THE SECOND PART of the conjecture: «\item[(ii)] $S(n_0)=1$, and the only pair at $n_0$ is
$(p,q)=(16K^2-4K,\ 16K^2+4K)$.» -/
def CF61_PartII : Prop :=
  BitsEquations ∧
  ∀ m : ℕ, 3 ≤ m →
    S m (n₀ m) = 1 ∧ IsPair m (n₀ m) (16 * K m ^ 2 - 4 * K m) (16 * K m ^ 2 + 4 * K m)

/-- THE FIRST PART of the conjecture: «\item[(i)] $S(n)\ne1$ for every integer $n$ with $20K+3<n<n_0$.» -/
def CF61_PartI : Prop :=
  BitsEquations ∧
  ∀ m : ℕ, 3 ≤ m → ∀ n : ℕ, 20 * K m + 3 < n → n < n₀ m → S m n ≠ 1

/-- THE CLOSED FORM: «For every $n$ with $1\le n\le n_0+8K$ we have $y_n=Y(l,c,r)$, where $(l,c,r)$ are the
coordinates of $n$.» -/
def CF61_Closed : Prop :=
  BitsEquations ∧
  ∀ m : ℕ, 3 ≤ m → ∀ n : ℕ, 1 ≤ n → n ≤ n₀ m + 8 * K m →
    ∀ l c r : ℤ, Coords m n l c r → y m n = Y m l c r

/-- ITS SHARPNESS: «At $n=n_0+8K+1$ we have $y_n=1$, while $Y=0$ there.» -/
def CF61_Sharp : Prop :=
  BitsEquations ∧
  ∀ m : ℕ, 3 ≤ m →
    y m (n₀ m + 8 * K m + 1) = 1 ∧
    ∀ l c r : ℤ, Coords m (n₀ m + 8 * K m + 1) l c r → Y m l c r = 0

/-- THE COORDINATES EXIST AND ARE UNIQUE: «Every integer $n$ has a unique representation»
«n=16Kl+4c+r,\qquad 2K\le c\le 6K-1,\quad 1\le r\le4,» — for every n ≥ 1 there is EXACTLY ONE triple (l, c, r) with
`Coords m n l c r`: one exists, and any two are equal (written out, not as `∃! l c r`, whose nested reading is not the
uniqueness of the triple). -/
def CF61_Coords : Prop :=
  ∀ m : ℕ, 3 ≤ m → ∀ n : ℕ, 1 ≤ n →
    (∃ l c r : ℤ, Coords m n l c r) ∧
    ∀ l c r l' c' r' : ℤ, Coords m n l c r → Coords m n l' c' r' → l = l' ∧ c = c' ∧ r = r'
