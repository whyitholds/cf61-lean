import Std

structure PFTEntry where
  v : Nat
  j0 : Nat
  j1 : Nat
  j2 : Nat
  j3 : Nat
deriving Inhabited

def pfAsEdges (e : PFTEntry) : Array Nat := #[e.j0,e.j1,e.j2,e.j3]

inductive PFTree : Nat → Type where
  | tip (x : PFTEntry) : PFTree 0
  | fork {d : Nat} (l r : PFTree d) : PFTree (d+1)

def pfFlat : {d : Nat} → PFTree d → List PFTEntry
  | _, .tip e => [e]
  | _, .fork l r => pfFlat l ++ pfFlat r

def pfSeek : {d : Nat} → PFTree d → Nat → PFTEntry
  | _, .tip e, _ => e
  | _, .fork (d := d) l r, i =>
    if i < 2^d then pfSeek l i else pfSeek r (i - 2^d)

theorem pfFlatLength (t : PFTree d) : (pfFlat t).length = 2^d := by
  induction t with
  | tip => rfl
  | fork l r hl hr =>
    simp only [pfFlat,List.length_append,hl,hr,Nat.pow_succ]
    omega

theorem pfFlatGet (t : PFTree d) (i : Nat) (hi : i < 2^d) :
    (pfFlat t)[i]? = some (pfSeek t i) := by
  induction t generalizing i with
  | tip e =>
    have : i = 0 := by simpa using hi
    subst i
    rfl
  | @fork d l r hl hr =>
    by_cases h : i < 2^d
    · rw [pfFlat, List.getElem?_append_left (by simpa [pfFlatLength] using h)]
      simpa [pfSeek,h] using hl i h
    · rw [pfFlat, List.getElem?_append_right (by rw [pfFlatLength]; omega), pfFlatLength]
      rw [Nat.pow_succ] at hi
      simpa [pfSeek,h] using hr (i-2^d) (by omega)

def pfProjected (f : PFTEntry → α) (t : PFTree d) (bound : Nat) : Array α :=
  (((pfFlat t).take bound).map f).toArray

theorem pfProjectedGet [Inhabited α] (f : PFTEntry → α) (t : PFTree d) (bound i : Nat)
    (hb : bound ≤ 2^d) (hi : i < bound) :
    (pfProjected f t bound)[i]! = f (pfSeek t i) := by
  have ho : (pfProjected f t bound)[i]? = some (f (pfSeek t i)) := by
    rw [pfProjected, List.getElem?_toArray, List.getElem?_map, List.getElem?_take_of_lt hi,
      pfFlatGet t i (Nat.lt_of_lt_of_le hi hb)]
    rfl
  obtain ⟨h,he⟩ := getElem?_eq_some_iff.mp ho
  rw [getElem!_pos (pfProjected f t bound) i h]
  exact he
