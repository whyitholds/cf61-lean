import Mathlib

/-! Definitions for 1-additive (Ulam) sequences.  The rule: for coprime integers 0 < a < b the 1-additive sequence
U(a, b) is the increasing sequence whose first two terms are a and b and whose every further term is the least integer
greater than the previous term that has exactly one representation as a sum of two distinct earlier terms.  The
sequence here is defined for the starting terms in increasing order a < b.  Terms are indexed from 1 (x_1 = a,
x_2 = b); index 0 is a placeholder (`seq a b 0 = 0`) that no statement reads. -/

namespace OneAdd

/-- Number of pairs of DISTINCT POSITIONS i < j of the list `h` whose entries sum to `n`.  On a strictly increasing
list distinct positions are distinct terms, and `x + x` is never counted (computable; used by the sequence). -/
def repsList (h : List ℕ) (n : ℕ) : ℕ :=
  (h.tails.map fun t => match t with
    | [] => 0
    | x :: r => (r.filter fun y => x + y = n).length).sum

/-- The next term after the history `h = [x_1, …, x_n]` (n ≥ 2): the least `m > x_n` with exactly one representation as
a sum of two distinct terms of `h`.  The bounded search covers `x_n < m ≤ x_n + x_{n-1}`; `x_n + x_{n-1}` always has
exactly one representation, so the search never falls through (the fallback `last + prev` is never used). -/
def nextTerm (h : List ℕ) : ℕ :=
  let last := h.getLastD 0
  let prev := h.getD (h.length - 2) 0
  match ((List.range prev).map fun d => last + 1 + d).find? (fun m => repsList h m = 1) with
  | some m => m
  | none => last + prev

/-- One step: append the next term. -/
def step (h : List ℕ) : List ℕ := h ++ [nextTerm h]

/-- `hist a b n` = [x_1, …, x_{2+n}] : the starting terms a, b and n steps of the rule. -/
def hist (a b n : ℕ) : List ℕ := step^[n] [a, b]

/-- The Ulam sequence with starting terms `a < b`, term x_n, 1-indexed. -/
def seq (a b n : ℕ) : ℕ := if n = 0 then 0 else (hist a b n).getD (n - 1) 0

/-- The number of representations of `n` as a sum of two DISTINCT terms of the sequence `x` (indexed from 1): the
number of pairs of indices 1 ≤ i < j with x i + x j = n.  For a strictly increasing sequence of positive integers
x j ≥ j, so the indices lie in `[1, n]` and nothing is lost by the bound; distinct indices are distinct terms
(r(n) = #{{x, y} : x ≠ y, x, y ∈ U, x + y = n}). -/
def reps (x : ℕ → ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    fun p => 1 ≤ p.1 ∧ p.1 < p.2 ∧ x p.1 + x p.2 = n).card

/-- `IsUlam a b y`: the sequence `y` (indexed from 1) obeys the printed rule with starting terms a, b: y_1 = a,
y_2 = b; the terms increase; for every n ≥ 2, y_{n+1} has exactly one representation as a sum of two distinct terms
(necessarily earlier, since terms increase and are positive), and no integer strictly between y_n and y_{n+1} has
exactly one. -/
def IsUlam (a b : ℕ) (y : ℕ → ℕ) : Prop :=
  y 1 = a ∧ y 2 = b ∧
  (∀ n : ℕ, 1 ≤ n → y n < y (n + 1)) ∧
  (∀ n : ℕ, 2 ≤ n → reps y (y (n + 1)) = 1) ∧
  (∀ n m : ℕ, 2 ≤ n → y n < m → m < y (n + 1) → reps y m ≠ 1)

/-- The DEFINING EQUATIONS of `seq`, for every start 0 < a < b: `seq a b` obeys the printed rule.  To be PROVED as
part of every statement about `seq`, so nobody has to trust the list encoding. -/
def UlamEquations : Prop :=
  ∀ a b : ℕ, 0 < a → a < b → IsUlam a b (seq a b)

/-- Uniqueness: any sequence obeying the printed rule with starting terms 0 < a < b is `seq a b` (from index 1 on). -/
def UlamUnique : Prop :=
  ∀ a b : ℕ, ∀ y : ℕ → ℕ, 0 < a → a < b → IsUlam a b y → ∀ n : ℕ, 1 ≤ n → y n = seq a b n

/-- Existence: for every start 0 < a < b a sequence obeying the printed rule exists. -/
def UlamExists : Prop :=
  ∀ a b : ℕ, 0 < a → a < b → ∃ y : ℕ → ℕ, IsUlam a b y

end OneAdd
