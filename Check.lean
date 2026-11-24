import Challenge
import Final

/-! The package proves the challenge: Lean's kernel accepts `final` (Final.lean) at the type of the eight challenge
statements, whose definitions unfold to the same terms. -/
theorem challenge_solved :
    Challenge.CF61_Main ∧ Challenge.CF61_PartII ∧ Challenge.CF61_PartI ∧ Challenge.CF61_Closed ∧
      Challenge.CF61_Sharp ∧ Challenge.CF61_Coords ∧ Challenge.CF61_Cor1_i ∧ Challenge.CF61_Cor1_ii :=
  final

#print axioms challenge_solved
