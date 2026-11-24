import PartIPacked

def piCol (v i : ℕ) : ℕ := (v >>> (80*i)) % 1208925819614629174706176

def piDigit (v i : ℕ) : ℕ := (v >>> (10*i)) % 1024

def piPackedClamp (v : ℕ) : ℕ :=
  let mask : ℕ := 1181745669222511412225
  let marks := ((v+508*mask) &&& (mask <<< 9)) >>> 9
  (v &&& (3*mask-3*marks)) ||| (marks <<< 2)

def piStepAt (v : ℕ) (a s : ℕ) : ℕ :=
  piPackedClamp (((piIncoming[a]!)[s]!).foldl (fun n i => n + piCol v i) 0)

def piFlagA (first : Bool) (a previous : ℕ) : ℕ :=
  if 2 ≤ a then (if first then 1 else 2) else previous

def piFlagV (a prev : ℕ) : ℕ := if a%2 = 0 then prev else 1

def piTransition (first : Bool) (v : ℕ) (a : ℕ) (w : ℕ) : Bool :=
  ((List.range 72).all fun s => piStepAt v a s == (piCol w s)) &&
  (piFlagA first a (piCol v 72) == (piCol w 72)) && (piFlagV a (piCol v 73) == (piCol w 73))

def piAcceptCount (v : ℕ) (ah d r : ℕ) : ℕ :=
  (piWeights[16*ah+4*d+r]!).foldl (fun acc p => acc + piDigit (piCol v p.1) p.2.1 * p.2.2) 0

def piAllowed (v : ℕ) (ah d : ℕ) : Bool :=
  0 < ah || (1 < (piCol v 72)) || ((piCol v 72) == 1 && (1 < d || (d == 1 && 0 < (piCol v 73))))

def piGood (v : ℕ) : Bool :=
  (List.range 32).all fun i =>
    let count := piAcceptCount v (i/16) (i/4%4) (i%4)
    !piAllowed v (i/16) (i/4%4) || (count != 2 && count != 3)

def piStatePass (i : ℕ) : Bool :=
  let v := piRowList[i]!
  piGood v && ((List.range 4).all fun a =>
    let j := (piEdges[i]!)[a]!
    j < 683 && piTransition false v a piRowList[j]!)

def piFirstPass : Bool :=
  (List.range 4).all fun a =>
    let j := piFirst[a]!
    j < 683 && piTransition true piStart a piRowList[j]!
