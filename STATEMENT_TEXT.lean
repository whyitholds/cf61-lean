import Mathlib

/-! The exact Lean text of the eight statements and of every definition they read, transitively, in the package's
own files (UlamDefs.lean, Bits.lean, Statement.lean, StatementCor1.lean), copied in file order with their
docstrings.  Nothing else of those files is needed to read the statements.  The file compiles on its own
over Mathlib. -/

-- from UlamDefs.lean
namespace OneAdd

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

/-- Existence: for every start 0 < a < b a sequence obeying the printed rule exists. -/
def UlamExists : Prop :=
  ∀ a b : ℕ, 0 < a → a < b → ∃ y : ℕ → ℕ, IsUlam a b y

end OneAdd

-- from Bits.lean
namespace CF61

/-- K = 2^(m − 2). -/
def K (m : ℕ) : ℕ := 2 ^ (m - 2)

/-- n₀ = 32K². -/
def n₀ (m : ℕ) : ℕ := 32 * K m ^ 2

/-- One step of the recurrence: the list `h = [y_0, y_1, …, y_(n-1)]`, n = h.length, becomes `[y_0, …, y_n]`.
For n > 8K the three indices n − 2, n − 4K − 1, n − 8K lie in [1, n − 1], so `getD` reads stored bits only. -/
def bitsStep (m : ℕ) (h : List ℕ) : List ℕ :=
  let n := h.length
  h ++ [if n < 8 * K m then 0 else if n = 8 * K m then 1 else
          if h.getD (n - 2) 0 + h.getD (n - 4 * K m - 1) 0 + h.getD (n - 8 * K m) 0 = 1 then 1 else 0]

/-- The bit y_n (n ≥ 1), computed from the recurrence by `bitsStep`; `y m 0` is a placeholder 0 that no statement
reads.  Its defining equations are the named statement `BitsEquations`, proved as part of every statement on y. -/
def y (m n : ℕ) : ℕ := ((bitsStep m)^[n + 1] []).getD n 0

/-- THE DEFINING EQUATIONS of the bits, for every m ≥ 3 (the Iverson bracket [P] is `if P then 1 else 0`):
«For $n\ge1$ let» «y_n=0\ \ (1\le n<8K),\qquad y_{8K}=1,\qquad y_n=\bigl[\,y_{n-2}+y_{n-4K-1}+y_{n-8K}=1\,\bigr]\ \ (n>8K).»
«$[P]$ for the Iverson bracket: $[P]=1$ if the statement $P$ holds and $[P]=0$ otherwise.»
To be PROVED as a conjunct of every statement about `y`, so nobody has to trust the list encoding. -/
def BitsEquations : Prop :=
  ∀ m : ℕ, 3 ≤ m →
    (∀ n : ℕ, 1 ≤ n → n < 8 * K m → y m n = 0) ∧
    y m (8 * K m) = 1 ∧
    (∀ n : ℕ, 8 * K m < n →
      y m n = if y m (n - 2) + y m (n - 4 * K m - 1) + y m (n - 8 * K m) = 1 then 1 else 0)

/-- (p, q) is a pair at n: «S(n)=\#\bigl\{(p,q):\ 1\le p<q,\ p+q=n,\ y_p=y_q=1\bigr\},»
«we call such $(p,q)$ a \emph{pair at $n$}». -/
def IsPair (m n p q : ℕ) : Prop := 1 ≤ p ∧ p < q ∧ p + q = n ∧ y m p = 1 ∧ y m q = 1

instance (m n p q : ℕ) : Decidable (IsPair m n p q) :=
  inferInstanceAs (Decidable (1 ≤ p ∧ p < q ∧ p + q = n ∧ y m p = 1 ∧ y m q = 1))

/-- S(n), the number of pairs at n.  Both members of a pair lie in [1, n], so nothing is lost by the bound. -/
def S (m n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter fun pq => IsPair m n pq.1 pq.2).card

/-- «z(h,l)=\binom{h+l}{l}\bmod 2\quad(h,l\ge0),\qquad z(h,l)=0\quad(h<0\text{ or }l<0),» -/
def z (h l : ℤ) : ℕ := if 0 ≤ h ∧ 0 ≤ l then Nat.choose (h + l).toNat l.toNat % 2 else 0

/-- «$\delta(t)=[t=0]$» -/
def δ (t : ℤ) : ℕ := if t = 0 then 1 else 0

/-- (l, c, r) are the coordinates of n: «n=16Kl+4c+r,\qquad 2K\le c\le 6K-1,\quad 1\le r\le4,»
«We call $(l,c,r)$ the \emph{coordinates} of $n$».  The note: «Every integer $n$ has a unique representation»; a
statement reads Y at EVERY triple with `Coords m n l c r` (there is exactly one: 4c + r runs over 16K consecutive
integers). -/
def Coords (m n : ℕ) (l c r : ℤ) : Prop :=
  let K : ℤ := (CF61.K m : ℤ)
  (n : ℤ) = 16 * K * l + 4 * c + r ∧ 2 * K ≤ c ∧ c ≤ 6 * K - 1 ∧ 1 ≤ r ∧ r ≤ 4

/-- THE TABLE Y(l, c, r), its fourteen lines in the printed order (line, r, range of c, value), each quoted from the
note beside its branch; the first line whose r and range of c hold gives the value.  The caption: «Each range of $c$ is
intersected with $[2K,6K-1]$. For $-1\le l\le 2K-1$ the lines with a given $r$ partition $[2K,6K-1]$.»  The statements
read Y only at coordinates (c in [2K, 6K − 1], r in 1 … 4), where the intersection is automatic; the final `0` (no line)
is reached at no cell of blocks −1 … 2K − 1 (the partition), nor at the one cell of block 2K that a statement reads. -/
def Y (m : ℕ) (l c r : ℤ) : ℕ :=
  let K : ℤ := (CF61.K m : ℤ)
  -- «1 & 1 & $2K\le c\le 3K-1$ & $0$\\»
  if r = 1 ∧ 2 * K ≤ c ∧ c ≤ 3 * K - 1 then 0
  -- «2 & 1 & $3K\le c\le 5K-1$ & $z(c-3K,\,l)$\\»
  else if r = 1 ∧ 3 * K ≤ c ∧ c ≤ 5 * K - 1 then z (c - 3 * K) l
  -- «3 & 1 & $5K\le c\le 5K+l$ & $z(c-5K,\,l+1)$\\»
  else if r = 1 ∧ 5 * K ≤ c ∧ c ≤ 5 * K + l then z (c - 5 * K) (l + 1)
  -- «4 & 1 & $5K+l+1\le c\le 6K-1$ & $0$\\»
  else if r = 1 ∧ 5 * K + l + 1 ≤ c ∧ c ≤ 6 * K - 1 then 0
  -- «5 & 2 & $2K\le c\le 4K-1$ & $z(c-2K,\,l)$\\»
  else if r = 2 ∧ 2 * K ≤ c ∧ c ≤ 4 * K - 1 then z (c - 2 * K) l
  -- «6 & 2 & $4K\le c\le 6K-1$ & $0$\\»
  else if r = 2 ∧ 4 * K ≤ c ∧ c ≤ 6 * K - 1 then 0
  -- «7 & 3 & $2K\le c\le 5K-1$ & $0$\\»
  else if r = 3 ∧ 2 * K ≤ c ∧ c ≤ 5 * K - 1 then 0
  -- «8 & 3 & $5K\le c\le 5K+l$ & $z(c-5K,\,l+1)$\\»
  else if r = 3 ∧ 5 * K ≤ c ∧ c ≤ 5 * K + l then z (c - 5 * K) (l + 1)
  -- «9 & 3 & $5K+l+1\le c\le 6K-1$ & $0$\\»
  else if r = 3 ∧ 5 * K + l + 1 ≤ c ∧ c ≤ 6 * K - 1 then 0
  -- «10 & 4 & $2K\le c\le 2K+l-1$ & $0$\\»
  else if r = 4 ∧ 2 * K ≤ c ∧ c ≤ 2 * K + l - 1 then 0
  -- «11 & 4 & $2K+l\le c\le 4K-2$ & $z(c-2K+1,\,l)$\\»
  else if r = 4 ∧ 2 * K + l ≤ c ∧ c ≤ 4 * K - 2 then z (c - 2 * K + 1) l
  -- «12 & 4 & $4K-1\le c\le 4K+l-1$ & $0$\\»
  else if r = 4 ∧ 4 * K - 1 ≤ c ∧ c ≤ 4 * K + l - 1 then 0
  -- «13 & 4 & $4K+l\le c\le 6K-2$ & $z(c-4K+1,\,l)$\\»
  else if r = 4 ∧ 4 * K + l ≤ c ∧ c ≤ 6 * K - 2 then z (c - 4 * K + 1) l
  -- «14 & 4 & $c=6K-1$ & $\delta(l+1)$\\»
  else if r = 4 ∧ c = 6 * K - 1 then δ (l + 1)
  else 0

end CF61

-- from Statement.lean
open OneAdd CF61

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


-- from StatementCor1.lean
open OneAdd CF61

/-- COROLLARY 1(i), for every sequence obeying the rule, with the existence clause: «**Corollary 1.** Let $m\ge3$ and
$b=2^m-1$.» «\item[(i)] For every odd integer $N$ with $0<N<N_b$, the number $N$ is a term of $U(4,b)$ if and only if
$Y(l,c,r)=1$, where $(l,c,r)$ are the coordinates of $n=(N+3b+4)/2$.»
"N is a term" is `∃ i, 1 ≤ i ∧ x i = N`, as in `CF61_Main`.  "where (l, c, r) are the coordinates of n" is read as in
`CF61_Closed`: at EVERY triple with `Coords m n l c r` (there is exactly one — `CF61_Coords` — so this is not vacuous). -/
def CF61_Cor1_i : Prop :=
  UlamExists ∧
  ∀ m : ℕ, 3 ≤ m →
    let b := 2 ^ m - 1
    let Nb := 4 * b ^ 2 + 2 * b - 4
    ∀ x : ℕ → ℕ, IsUlam 4 b x →
      ∀ N : ℕ, N % 2 = 1 → 0 < N → N < Nb →
        ∀ l c r : ℤ, Coords m ((N + 3 * b + 4) / 2) l c r →
          ((∃ i : ℕ, 1 ≤ i ∧ x i = N) ↔ Y m l c r = 1)

/-- COROLLARY 1(ii), for every sequence obeying the rule, with the existence clause: «**Corollary 1.** Let $m\ge3$ and
$b=2^m-1$.» «\item[(ii)] $U(4,b)$ has exactly $4\cdot3^{m-1}+2$ terms not exceeding $N_b$; that is, counting $4$ as the
first term, $N_b$ is the term number $4\cdot3^{m-1}+2$.»
Both clauses are stated.  "The terms not exceeding N_b" are counted by their indices, as `reps` counts pairs: the number
of i with 1 ≤ i and x i ≤ N_b; the terms increase from x 1 = 4, so x i ≥ i, distinct indices are distinct terms, and every
such i lies in [1, N_b], so nothing is lost by `Finset.range (Nb + 1)`.  "Counting 4 as the first term" is the indexing
x 1 = 4 of `IsUlam 4 b x`, so "the term number t" is x t. -/
def CF61_Cor1_ii : Prop :=
  UlamExists ∧
  ∀ m : ℕ, 3 ≤ m →
    let b := 2 ^ m - 1
    let Nb := 4 * b ^ 2 + 2 * b - 4
    ∀ x : ℕ → ℕ, IsUlam 4 b x →
      ((Finset.range (Nb + 1)).filter fun i => 1 ≤ i ∧ x i ≤ Nb).card = 4 * 3 ^ (m - 1) + 2 ∧
      x (4 * 3 ^ (m - 1) + 2) = Nb
