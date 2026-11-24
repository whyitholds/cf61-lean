import PartISpec

abbrev PIQuad := (ℕ × ℕ) × (ℕ × ℕ)
abbrev PITail := (Fin 3 × Fin 3) × (Fin 6 × Fin 6)

def piCmp (u v : ℕ) : ℕ := if u < v then 0 else if u = v then 1 else 2

def piCmpUp (f u v : ℕ) : ℕ := if u = v then f else piCmp u v

def piHU (t : Fin 3) : ℕ := if t.val = 1 then 1 else 0

def piHV (t : Fin 3) : ℕ := if t.val = 2 then 1 else 0

def piFits (f : ℕ) (t : Fin 6) : Prop :=
  t.val ≤ 1 ∨ (t.val = 2 ∧ f ≤ 1) ∨ (t.val = 3 ∧ f = 0) ∨ (4 ≤ t.val ∧ f = 2)

theorem piFitsCmp (u v : ℕ) (t : Fin 6) : piFits (piCmp u v) t ↔ PITagOK u v t := by
  unfold piFits piCmp PITagOK
  split <;> (try split) <;> omega

def piLowGrid (k : ℕ) : Finset PIQuad :=
  let sq := Finset.range k ×ˢ Finset.range k
  sq ×ˢ sq

def piLowPred (k a v j e c b f g : ℕ) (q : PIQuad) : Prop :=
  q.1.1 &&& q.1.2 = 0 ∧ q.2.1 &&& q.2.2 = 0 ∧
  q.1.1 + q.2.1 + j = a + k*c ∧ q.1.2 + q.2.2 + e = v + k*b ∧
  piCmp q.1.1 q.1.2 = f ∧ piCmp q.2.1 q.2.2 = g

def piLowBucket (k a v j e c b f g : ℕ) : Finset PIQuad := by
  letI : DecidablePred (piLowPred k a v j e c b f g) := fun q => by unfold piLowPred; exact inferInstance
  exact (piLowGrid k).filter (piLowPred k a v j e c b f g)

def piTailPred (ah d r j e c b f g : ℕ) (T : PITail) : Prop :=
  let A := T.1.1
  let B := T.1.2
  let x := T.2.1
  let y := T.2.2
  piFits (piCmpUp f (piHU A) (piHV A)) x ∧ piFits (piCmpUp g (piHU B) (piHV B)) y ∧
  c + piHU A + piHU B = ah ∧
  b + piHV A + piHV B + PITagShift x + PITagShift y = d + 4*j ∧
  PITagResidue x + PITagResidue y = r + 4*e

def piTailChoices (ah d r j e c b f g : ℕ) : Finset PITail := by
  letI : DecidablePred (piTailPred ah d r j e c b f g) := fun q => by unfold piTailPred piFits; exact inferInstance
  exact Finset.univ.filter (piTailPred ah d r j e c b f g)

def piTrueCount (k a v ah d r : ℕ) : ℕ :=
  ∑ s ∈ Finset.range 72, ∑ t ∈ Finset.range 8,
    (piLowBucket k a v (t/2) (t%2) (s/18) (s/9%2) (s/3%3) (s%3)).card *
    (piTailChoices ah d r (t/2) (t%2) (s/18) (s/9%2) (s/3%3) (s%3)).card
