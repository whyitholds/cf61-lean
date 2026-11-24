import AutoMachine

def autoRestrict (d : AutoF) : AutoF → AutoF
  | .con f g => .con (autoRestrict d f) (autoRestrict d g)
  | .disj f g => .disj (autoRestrict d f) (autoRestrict d g)
  | .neg f => .con d (.neg (autoRestrict d f))
  | p => .con d p

theorem autoRestrictDen (d f : AutoF) (k l t : Nat) :
    autoDen (autoRestrict d f) k l t ↔ autoDen d k l t ∧ autoDen f k l t := by
  induction f <;> simp only [autoRestrict, autoDen, *] <;> grind

def autoNarrow : AutoF → AutoF
  | .disj (.neg d) f => .disj (.neg d) (autoRestrict d f)
  | p => p

theorem autoUnNarrow (p : AutoF) (k l t : Nat) : autoDen (autoNarrow p) k l t → autoDen p k l t := by
  unfold autoNarrow
  split
  · simp only [autoDen, autoRestrictDen]
    grind
  · exact id

theorem autoForall {n : Nat} (P : Fin n → Prop) [DecidablePred P]
    (h : Nat.allLTTR n (fun i hi => decide (P ⟨i,hi⟩)) = true) :
    ∀ i, P i := fun ⟨i,hi⟩ => of_decide_eq_true ((Nat.allLTTR_eq_true.mp h) i hi)
