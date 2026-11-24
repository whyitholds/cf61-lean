import Mathlib
import UlamDefs
import Bits

/-! The challenge: the eight statements of the note, alone.  They read the definitions of `UlamDefs.lean` (the rule
`IsUlam`, the count `reps`, `UlamExists`) and of `Bits.lean` (K, n₀, the bits y with `BitsEquations`, S, `IsPair`,
`Coords`, the table Y).  The text of each statement is byte-identical to its text in `Statement.lean` or
`StatementCor1.lean`.  `Check.lean` proves the eight from the package's `final`. -/

open OneAdd CF61

namespace Challenge

-- Theorem A (for every sequence obeying the rule, with the existence of one)
def CF61_Main : Prop :=
  UlamExists ∧
  ∀ m : ℕ, 3 ≤ m →
    let b := 2 ^ m - 1
    let Nb := 4 * b ^ 2 + 2 * b - 4
    ∀ x : ℕ → ℕ, IsUlam 4 b x →
      ∀ τ : ℕ, τ ≤ Nb →
        (((∃ i : ℕ, 1 ≤ i ∧ x i = τ) ∧ τ % 2 = 0) ↔ (τ = 4 ∨ τ = 2 * b + 4 ∨ τ = 4 * b + 4 ∨ τ = Nb))

-- Theorem C (ii)
def CF61_PartII : Prop :=
  BitsEquations ∧
  ∀ m : ℕ, 3 ≤ m →
    S m (n₀ m) = 1 ∧ IsPair m (n₀ m) (16 * K m ^ 2 - 4 * K m) (16 * K m ^ 2 + 4 * K m)

-- Theorem C (i)
def CF61_PartI : Prop :=
  BitsEquations ∧
  ∀ m : ℕ, 3 ≤ m → ∀ n : ℕ, 20 * K m + 3 < n → n < n₀ m → S m n ≠ 1

-- Theorem B, first sentence
def CF61_Closed : Prop :=
  BitsEquations ∧
  ∀ m : ℕ, 3 ≤ m → ∀ n : ℕ, 1 ≤ n → n ≤ n₀ m + 8 * K m →
    ∀ l c r : ℤ, Coords m n l c r → y m n = Y m l c r

-- Theorem B, second sentence, without its parenthesis
def CF61_Sharp : Prop :=
  BitsEquations ∧
  ∀ m : ℕ, 3 ≤ m →
    y m (n₀ m + 8 * K m + 1) = 1 ∧
    ∀ l c r : ℤ, Coords m (n₀ m + 8 * K m + 1) l c r → Y m l c r = 0

-- display (1.2): the coordinates exist and are unique, n >= 1
def CF61_Coords : Prop :=
  ∀ m : ℕ, 3 ≤ m → ∀ n : ℕ, 1 ≤ n →
    (∃ l c r : ℤ, Coords m n l c r) ∧
    ∀ l c r l' c' r' : ℤ, Coords m n l c r → Coords m n l' c' r' → l = l' ∧ c = c' ∧ r = r'

-- Corollary 1 (i)
def CF61_Cor1_i : Prop :=
  UlamExists ∧
  ∀ m : ℕ, 3 ≤ m →
    let b := 2 ^ m - 1
    let Nb := 4 * b ^ 2 + 2 * b - 4
    ∀ x : ℕ → ℕ, IsUlam 4 b x →
      ∀ N : ℕ, N % 2 = 1 → 0 < N → N < Nb →
        ∀ l c r : ℤ, Coords m ((N + 3 * b + 4) / 2) l c r →
          ((∃ i : ℕ, 1 ≤ i ∧ x i = N) ↔ Y m l c r = 1)

-- Corollary 1 (ii)
def CF61_Cor1_ii : Prop :=
  UlamExists ∧
  ∀ m : ℕ, 3 ≤ m →
    let b := 2 ^ m - 1
    let Nb := 4 * b ^ 2 + 2 * b - 4
    ∀ x : ℕ → ℕ, IsUlam 4 b x →
      ((Finset.range (Nb + 1)).filter fun i => 1 ≤ i ∧ x i ≤ Nb).card = 4 * 3 ^ (m - 1) + 2 ∧
      x (4 * 3 ^ (m - 1) + 2) = Nb

end Challenge
