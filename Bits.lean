import Mathlib

/-! The objects of the statements on Cassaigne and Finch's Conjecture 6.1, in the letters of the note.
Every quotation in guillemets below is verbatim from the note's
LaTeX source.  No proofs; nothing here is assumed.
The parameter is m: «Throughout, $m\ge3$ and» «b=2^m-1,\qquad K=2^{m-2}=\frac{b+1}4,\qquad \Nb=4b^2+2b-4=2(2b^2+b-2),\qquad n_0=32K^2=2(b+1)^2 .»
Every definition takes m first; the letters are functions of m.  Indices n, p, q are natural numbers; the coordinates
l, c, r and the arguments of z are integers (the block l = -1 holds 1 ≤ n ≤ 8K). -/

namespace CF61

/-- b = 2^m − 1. -/
def b (m : ℕ) : ℕ := 2 ^ m - 1

/-- K = 2^(m − 2). -/
def K (m : ℕ) : ℕ := 2 ^ (m - 2)

/-- N_b = 4b² + 2b − 4. -/
def Nb (m : ℕ) : ℕ := 4 * b m ^ 2 + 2 * b m - 4

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
