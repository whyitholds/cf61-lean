import WeightPure

def waU (a : Fin 3) : Nat := if a.val = 1 then 1 else 0
def waV (a : Fin 3) : Nat := if a.val = 2 then 1 else 0
def waCmp (p q z : Nat) := if p=q then z else if p<q then 0 else if p=q then 1 else 2

def waRuleKey (s : Nat) (T : PWChoice) : Option (Nat × Nat) :=
  let A := T.1.1
  let B := T.1.2
  let x := T.2.1
  let y := T.2.2
  let h := s/18 + waU A + waU B
  let v := s/9%2 + waV A + waV B + pwShift x + pwShift y
  let r := pwResidue x + pwResidue y
  if h < 2 ∧ pwFit (waCmp (waU A) (waV A) (s/3%3)) x ∧
      pwFit (waCmp (waU B) (waV B) (s%3)) y then
    some (16*h + 4*(v%4) + r%4, 2*(v/4) + r/4)
  else none

def waEntry (q s : Nat) (p : Nat × Nat × Nat) : List (Nat × Nat) :=
  if p.1 = s then List.replicate p.2.2 (q,p.2.1) else []

def waTableKeys (s : Nat) : List (Nat × Nat) :=
  (List.range 32).flatMap fun q => pwTable[q]!.flatMap (waEntry q s)

def waPass (s : Nat) : Bool :=
  (pwAll.filterMap (waRuleKey s)).isPerm (waTableKeys s)
