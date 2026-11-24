import PartILowSpec

def piNextLetter (s : ℕ) (x y : Fin 3) : ℕ :=
  2*((s/18 + piHU x + piHU y)%2) + (s/9%2 + piHV x + piHV y)%2

def piNextCol (s : ℕ) (x y : Fin 3) : ℕ :=
  18*((s/18 + piHU x + piHU y)/2) + 9*((s/9%2 + piHV x + piHV y)/2) +
  3*piCmpUp (s/3%3) (piHU x) (piHV x) + piCmpUp (s%3) (piHU y) (piHV y)

def piMoveSet (a s : ℕ) : Finset (ℕ × (Fin 3 × Fin 3)) :=
  ((Finset.range 72) ×ˢ (Finset.univ : Finset (Fin 3 × Fin 3))).filter
    fun t => piNextLetter t.1 t.2.1 t.2.2 = a ∧ piNextCol t.1 t.2.1 t.2.2 = s

def piNumLow (k a v j e s : ℕ) : ℕ :=
  (piLowBucket k a v j e (s/18) (s/9%2) (s/3%3) (s%3)).card
