# Lean supplement: the first four even terms of U(4, 2^m - 1)

This package is a machine-checked proof, in Lean 4 with Mathlib, of Theorems A, B and C and Corollary 1 of the note (the
even terms of U(4, b) not exceeding N_b, the closed form of Cassaigne and Finch with its sharpness, both parts of their
Conjecture 6.1, and the odd terms below N_b with the number of terms up to N_b), for every m >= 3, together with the
existence and uniqueness of the coordinates (1.2) for n >= 1. The formal statements were prepared on the author's side.
The proofs were produced by a second model and checked by Lean's kernel. The package is anonymous.

## What is proved, in the note's numbering

Notation as in the note: b = 2^m - 1, K = 2^(m-2), N_b = 4b^2 + 2b - 4, n_0 = 32K^2; y_n the bits of the recurrence (1.1),
S(n) the number of pairs at n, (l, c, r) the coordinates (1.2) of n, Y(l, c, r) the table of the note (Table 1.1).

| Note | Lean statement (`Statement.lean`) | Content |
|---|---|---|
| Theorem A | `CF61_Main` | for every m >= 3 and every sequence x obeying the rule from (4, b): an integer τ <= N_b is an even term of x iff τ is 4, 2b + 4, 4b + 4 or N_b (the "in particular" sentence is this at the four values); with the existence of such a sequence (`UlamExists`) |
| Theorem B, first sentence | `CF61_Closed` | y_n = Y(l, c, r) for 1 <= n <= n_0 + 8K, at the coordinates (l, c, r) of n |
| Theorem B, second sentence, without its parenthesis | `CF61_Sharp` | y_n = 1 at n = n_0 + 8K + 1, while Y = 0 at its coordinates |
| Theorem C (i) | `CF61_PartI` | S(n) ≠ 1 for every n with 20K + 3 < n < n_0 |
| Theorem C (ii) | `CF61_PartII` | S(n_0) = 1, and (16K^2 - 4K, 16K^2 + 4K) is a pair at n_0 |
| display (1.2), the coordinates | `CF61_Coords` | every n >= 1 has exactly one triple (l, c, r) with n = 16Kl + 4c + r, 2K <= c <= 6K - 1, 1 <= r <= 4 (the note states it for every integer; the theorems use it at n >= 1) |
| Corollary 1 (i) | `CF61_Cor1_i` (in `StatementCor1.lean`) | for every m >= 3 and every sequence x obeying the rule from (4, b): an odd integer N with 0 < N < N_b is a term of x iff Y(l, c, r) = 1 at the coordinates (l, c, r) of n = (N + 3b + 4)/2; with the existence of such a sequence (`UlamExists`) |
| Corollary 1 (ii) | `CF61_Cor1_ii` (in `StatementCor1.lean`) | for every m >= 3 and every sequence x obeying the rule from (4, b): exactly 4·3^(m-1) + 2 terms of x do not exceed N_b, and N_b is the term number 4·3^(m-1) + 2, counting 4 as the first term; with the existence of such a sequence (`UlamExists`) |

`CF61_Main` rests on `UlamDefs.lean` alone: the rule is `IsUlam` (the printed rule itself, for every sequence obeying it).
The other four statements on y (`CF61_Closed`, `CF61_Sharp`, `CF61_PartI`, `CF61_PartII`) each carry as a conjunct the
defining equations `BitsEquations` (y obeys the recurrence (1.1)), so the list encoding of y need not be trusted. In
`CF61_PartII`, "the only pair" is the conjunction of S(n_0) = 1 with the named pair being a pair at n_0. `Final.lean` states
the conjunction of all eight statements as `final`.

Two propositions of the note are not separate Lean statements, being one line away from a checked one: Proposition 14
(every pair at n has a second pair, for 20K + 3 < n < n_0) is Theorem C (i) in other words, since S(n) ≠ 1 says that S(n) is
0 or at least 2; Proposition 16 (no even term N with 4b + 4 < N < N_b) is Theorem A read on that range.

Not covered: Lemmas 2-13 and 15 as separate statements (they are steps of the proofs); the parenthesis of Theorem B
naming the point (2K, 2K, 1); and Remarks 17-21 (an argument from part (ii) alone, computations for other b and for
m = 2, the computational cross-checks, and a comment on Finch's Conjecture 3). The formal proofs do not follow the
proofs printed in the note (that of Corollary 1 follows their outline in part); what Lean checks is the eight
statements above.

## How to check this in minutes

1. **The pin.** `lean-toolchain`: Lean 4.36.0 (`leanprover/lean4:v4.36.0`). `lakefile.toml`: Mathlib at tag v4.36.0,
   commit fc4f59e577feb1a4956671bc04ac18aaaf8cd842; `lake-manifest.json` pins every dependency.
2. **The build.** With elan (https://github.com/leanprover/elan) installed and its bin folder on PATH, in this folder:

       lake exe cache get      # downloads the prebuilt Mathlib for the pinned commit
       lake build

   `lake exe cache get` needs network access to GitHub. The package ships no dependencies. Offline, copy into
   `.lake/packages` a set built for the nine revisions pinned in `lake-manifest.json`, check each revision against the
   manifest, then run `lake build`.

   Expected: no error and no `sorry` warning (style-linter warnings of the generated proofs may be printed); the build
   prints the `#print axioms` lines of `Final.lean`, `Check.lean` and `Axioms.lean`, each
   `[propext, Classical.choice, Quot.sound]`. A compile of every module, one file at a time against the same pinned Lean
   and Mathlib, took about twenty-seven minutes on a laptop.
3. **The challenge.** `Challenge.lean` is the eight statements alone, in one short file that imports only Mathlib,
   `UlamDefs.lean` and `Bits.lean`; the text of each statement is byte-identical to its text in `Statement.lean` or
   `StatementCor1.lean`. `Check.lean` proves `challenge_solved`, the conjunction of the eight challenge statements, by
   `final`: the kernel accepts it only because the challenge's definitions unfold to the same terms as the package's.
   To run the challenge alone after `lake build`: `lake env lean Check.lean` (exits 0 and prints one line,
   `'challenge_solved' depends on axioms: [propext, Classical.choice, Quot.sound]`).
4. **The axioms.** `AXIOMS.txt` holds two header lines (the command and the toolchain), then the output of
   `lake env lean Axioms.lean`: each of the eight theorems, `final` and `challenge_solved` depend on
   `[propext, Classical.choice, Quot.sound]` and nothing else, so no `sorry` and no `native_decide`.
5. **A second, independent kernel.** `SECOND_KERNEL.txt`: the declarations `challenge_solved` and `final`, with
   everything they depend on (Lean's core and Mathlib included), exported with lean4export and checked by nanoda, a
   type checker for Lean written independently of Lean's kernel, with only those three axioms permitted. The export
   checked has sha256 c80a76b5560794ff4064d9b809b5e95195dddccf776f264a0fc2e1586dc75707; the file gives the commands, the tool versions and the checker's output.
6. **Lean's own kernel, replayed.** `lake env leanchecker <Module>` replays the declarations of a module with Lean's
   kernel, outside the elaborator, for example `lake env leanchecker Final`.

## Files

- `UlamDefs.lean`, `Bits.lean`, `Statement.lean`, `StatementCor1.lean`: the definitions and the statements (the part a
  reader must check against the note). `UlamDefs.lean`: the Ulam sequence and the rule `IsUlam`; `Bits.lean`: b, K, N_b,
  n_0, the bits y, S, z, δ, the coordinates `Coords` and the table `Y`, line by line with the note's text beside each
  line; `Statement.lean`: the six statements; `StatementCor1.lean`: the two statements of Corollary 1.
- `STATEMENT_TEXT.lean`: the eight statements and every definition they read, as one file that compiles on its own over
  Mathlib; not read by `lake build`.
- `Proof.lean` (the six theorems `proof_main`, `proof_partII`, `proof_partI`, `proof_closed`, `proof_sharp`,
  `proof_coords`), `ProofCor1.lean` (the two theorems `proof_cor1_i`, `proof_cor1_ii`) and the modules they import
  (`Auto*`, `BitBase`, `Closed*`, `CoordsBase`, `Cor*`, `Encode*`, `Main*`, `NumBits`, `PartI*`, `PartII`,
  `PartIIResult`, `SharpBase`, `UlamExist`, `WAlt*`, `Weight*`): the proofs. Several of them (the `AutoCert*`,
  `PartIFast*` and `WAltCol*` families and a few data modules) are finite certificates written by programs; Lean checks
  them like every other module, so the programs are not needed to check the proof.
- `Final.lean`: the conjunction `final` and `#print axioms final`.
- `Challenge.lean`, `Check.lean`, `Axioms.lean`, `AXIOMS.txt`, `SECOND_KERNEL.txt`: the checks of the section above.
- `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`: the pin.

One hundred and sixty modules carry the statements and the proofs, every one of them imported, directly or not, by
`Final.lean`, and every one holding a declaration that `final` depends on; with `Challenge`, `Check` and `Axioms`, one
hundred and sixty-three.
