import AutoBase

def clK : AutoLin := ⟨1,0,0,0⟩
def clL : AutoLin := ⟨0,1,0,0⟩
def clT : AutoLin := ⟨0,0,1,0⟩
def clC : AutoLin := ⟨0,0,0,1⟩
def clO : AutoLin := ⟨0,0,0,0⟩

def clAdd (x y : AutoLin) : AutoLin := ⟨x.a+y.a,x.b+y.b,x.c+y.c,x.d+y.d⟩
def clSub (x y : AutoLin) : AutoLin := ⟨x.a-y.a,x.b-y.b,x.c-y.c,x.d-y.d⟩
def clMul (n : Int) (x : AutoLin) : AutoLin := ⟨n*x.a,n*x.b,n*x.c,n*x.d⟩

def clLe (x y : AutoLin) : AutoF := .ge (clSub y x)
def clLt (x y : AutoLin) : AutoF := .ge (clSub (clSub y x) clC)
def clEq (x y : AutoLin) : AutoF := .con (clLe x y) (clLe y x)

def clRow (r : Nat) (l t : AutoLin) : AutoF :=
  let k2 := clMul 2 clK
  let k3 := clMul 3 clK
  let k4 := clMul 4 clK
  let tail := AutoF.con (clLe k3 t) (.con (clLe t (clAdd k3 l)) (.dis (clSub t k3) (clAdd l clC)))
  match r with
  | 1 => .disj (.con (clLe clK t) (.con (clLt t k3) (.dis (clSub t clK) l))) tail
  | 2 => .con (clLt t k2) (.dis t l)
  | 3 => tail
  | 4 => .disj (.con (clLe l t) (.con (clLt t (clSub k2 clC)) (.dis (clAdd t clC) l)))
      (.disj (.con (clLe (clAdd k2 l) t) (.con (clLt t (clSub k4 clC)) (.dis (clAdd (clSub t k2) clC) l)))
        (.con (clEq t (clSub k4 clC)) (clEq l (clSub clO clC))))
  | _ => .no

def clPrev (r : Nat) (l t d : AutoLin) : AutoF :=
  .disj (.con (clLt t d) (clRow r (clSub l clC) (clSub (clAdd t (clMul 4 clK)) d)))
    (.con (clLe d t) (clRow r l (clSub t d)))

def clOne (a b c : AutoF) : AutoF :=
  .disj (.con a (.con (.neg b) (.neg c)))
    (.disj (.con (.neg a) (.con b (.neg c))) (.con (.neg a) (.con (.neg b) c)))

def clGoal (r : Nat) : AutoF :=
  let l := clSub clL clC
  let dom := AutoF.con .pow (.con (clLe clC clL) (.con (clLe clL (clMul 2 clK)) (clLt clT (clMul 4 clK))))
  let x := clRow r l clT
  let a := clPrev (if r ≤ 2 then r+2 else r-2) l clT (if r ≤ 2 then clC else clO)
  let b := clPrev (if r = 1 then 4 else r-1) l clT (if r = 1 then clAdd clK clC else clK)
  let c := clPrev r l clT (clMul 2 clK)
  let y := clOne a b c
  .disj (.neg dom) (.con (.disj (.neg x) y) (.disj (.neg y) x))

def closedR1F := clGoal 1
def closedR2F := clGoal 2
def closedR3F := clGoal 3
def closedR4F := clGoal 4
