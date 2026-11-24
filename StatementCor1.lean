import UlamDefs
import Bits

open OneAdd CF61

/-! Corollary 1 of the note on Cassaigne and Finch's Conjecture 6.1, as two statements, in the style of `CF61_Main`
(Statement.lean): for every sequence obeying the rule, with the existence clause `UlamExists` as a conjunct; the letters
b and N_b written out as `let`s exactly as there.  Over UNCHANGED copies of UlamDefs.lean (`IsUlam`,
`UlamExists`) and Bits.lean (`Coords`, `Y`); Statement.lean is not imported.  Neither statement reads the bits y, so
neither carries `BitsEquations` (as `CF61_Coords`).  No proofs; the Props are statements to be proved.
Every quotation in guillemets is verbatim from the note's LaTeX source (line breaks as spaces): the definitions from its
Section 1, the statement from the text of the corollary.
The rule: «For coprime integers $0<a<b$ the \emph{$1$-additive sequence}, or \emph{Ulam sequence}, $U(a,b)$ is the
increasing sequence whose first two terms are $a$ and $b$ and each of whose further terms is the least integer greater
than the previous term that has exactly one representation as a sum of two distinct earlier terms.»
The letters: «Throughout, $m\ge3$ and \[ b=2^m-1,\qquad K=2^{m-2}=\frac{b+1}4,\qquad \Nb=4b^2+2b-4=2(2b^2+b-2),\qquad
n_0=32K^2=2(b+1)^2 . \]»
The coordinates: «Every integer $n$ has a unique representation» «n=16Kl+4c+r,\qquad 2K\le c\le 6K-1,\quad 1\le r\le4,»
«We call $(l,c,r)$ the \emph{coordinates}, or the \emph{cell}, of $n$»; «Let $Y(l,c,r)$ be given by Table~\ref{tab:cf}.»
(Bits.lean's `Coords` and `Y`, unchanged; `Y` quotes the table line by line.)
Natural-number arithmetic: m ≥ 3, so 2^m − 1 ≥ 7, 4b² + 2b − 4 > 0 and m − 1 are exact; N and b are odd, so N + 3b + 4 is
even and `(N + 3 * b + 4) / 2` is the printed n exactly. -/

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
