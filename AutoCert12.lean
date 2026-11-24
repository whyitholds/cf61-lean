import AutoCert0
import AutoCert1
import AutoCert5
import AutoCert11

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr164 : AutoF := .con autoExpr6 autoExpr163
def autoDfa164 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc164 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst164 (i : Fin 6) : Nat := autoPacked 0x0 1 i.val
def autoNext164 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk164 : autoGood autoExpr164 autoDfa164 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa6 autoDfa163 Bool.and) autoDfa164 autoSrc164 autoDst164 autoNext164
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk163)
  · rfl

def autoExpr165 : AutoF := (.dis ⟨2,0,1,0⟩ ⟨0,1,0,-2⟩)
def autoDfa165 : AutoM Nat := autoPackedTab 0x6fdf7d3eb7ee43df5bb0b7659616db6db1ee56362c6ec44368a288 3
def autoSrc165 (i : Fin 8) : AutoLit := (#[(.dis ⟨2,0,1,0⟩ ⟨0,1,0,-2⟩),(.dis ⟨2,0,1,0⟩ ⟨0,1,0,-1⟩),(.dis ⟨2,0,1,1⟩ ⟨0,1,0,-1⟩),(.no),(.dis ⟨2,0,1,0⟩ ⟨0,1,0,0⟩),(.dis ⟨2,0,1,1⟩ ⟨0,1,0,0⟩),(.dis ⟨2,0,1,2⟩ ⟨0,1,0,-1⟩),(.dis ⟨2,0,1,2⟩ ⟨0,1,0,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst165 (i : Fin 8) : Nat := autoPacked 0xfac688 3 i.val
def autoNext165 (i : Fin 8) (j : Fin 8) : Fin 8 := Fin.ofNat 8 (autoPacked 0x6fdf7df5bf72f7d6ec6ecb2c6db6dbf72b1bb1bb116d1451 3 (8*i.val+j.val))
theorem autoOk165 : autoGood autoExpr165 autoDfa165 0 := by
  apply autoTransfer (N := 7) autoAtom autoDfa165 autoSrc165 autoDst165 autoNext165
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.dis ⟨2,0,1,0⟩ ⟨0,1,0,-2⟩))
  · rfl

def autoExpr166 : AutoF := .con autoExpr6 autoExpr165
def autoDfa166 : AutoM Nat := autoPackedTab 0x924927324f24e64d75d44924920d64d6313c93c83593544488c688 3
def autoSrc166 (i : Fin 21) : Nat × Nat := (autoPacked 0x59659258434d3440 3 i.val, autoPacked 0x28fdcac6dd8da288 3 i.val)
def autoDst166 (i : Fin 21) : Nat := autoPacked 0x4927927926b24688 3 i.val
def autoNext166 (i : Fin 21) (j : Fin 8) : Fin 21 := Fin.ofNat 21 (autoPacked 0x8b5ee6cd725adb36cdb35ad6b5ad725ae2d8b62d8b62d5adac8b56b8b5ee8b5ee6cd6b8b62d5adb35adb36cdac5ad6b5ad6b5c96b5c96b31549315498b6305adac3150741d075ad725ad72314c5314c58b5f46cd7241cc541c838c1ee6b16b41d4941c413144120c41 5 (8*i.val+j.val))
theorem autoOk166 : autoGood autoExpr166 autoDfa166 0 := by
  apply autoTransfer (N := 20) (autoCombine autoDfa6 autoDfa165 Bool.and) autoDfa166 autoSrc166 autoDst166 autoNext166
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk165)
  · rfl

def autoExpr167 : AutoF := .con autoExpr164 autoExpr166
def autoDfa167 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc167 (i : Fin 8) : Nat × Nat := (autoPacked 0x0 1 i.val, autoPacked 0xfac688 3 i.val)
def autoDst167 (i : Fin 8) : Nat := autoPacked 0x0 1 i.val
def autoNext167 (i : Fin 8) (j : Fin 8) : Fin 8 := Fin.ofNat 8 (autoPacked 0x924927927927935d75924924d64d639e49e4d64d519118d1 3 (8*i.val+j.val))
theorem autoOk167 : autoGood autoExpr167 autoDfa167 0 := by
  apply autoTransfer (N := 7) (autoCombine autoDfa164 autoDfa166 Bool.and) autoDfa167 autoSrc167 autoDst167 autoNext167
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk164 autoOk166)
  · rfl

def autoExpr168 : AutoF := .con autoExpr162 autoExpr167
def autoDfa168 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc168 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst168 (i : Fin 6) : Nat := autoPacked 0x0 1 i.val
def autoNext168 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk168 : autoGood autoExpr168 autoDfa168 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa162 autoDfa167 Bool.and) autoDfa168 autoSrc168 autoDst168 autoNext168
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk162 autoOk167)
  · rfl

def autoExpr169 : AutoF := (.ge ⟨0,0,1,0⟩)
def autoDfa169 : AutoM Nat := autoAlways
def autoSrc169 (i : Fin 1) : AutoLit := (#[(.ge ⟨0,0,1,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst169 (i : Fin 1) : Nat := autoPacked 0x0 1 i.val
def autoNext169 (i : Fin 1) (j : Fin 8) : Fin 1 := Fin.ofNat 1 (autoPacked 0x0 1 (8*i.val+j.val))
theorem autoOk169 : autoGood autoExpr169 autoDfa169 0 := by
  apply autoTransfer (N := 0) autoAtom autoDfa169 autoSrc169 autoDst169 autoNext169
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨0,0,1,0⟩))
  · rfl

def autoExpr170 : AutoF := .con autoExpr6 autoExpr169
def autoDfa170 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc170 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst170 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext170 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk170 : autoGood autoExpr170 autoDfa170 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa6 autoDfa169 Bool.and) autoDfa170 autoSrc170 autoDst170 autoNext170
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk169)
  · rfl

def autoExpr171 : AutoF := .con autoExpr28 autoExpr170
def autoDfa171 : AutoM Nat := autoPackedTab 0x49249209249233248d3424923904923440 3
def autoSrc171 (i : Fin 11) : Nat × Nat := (autoPacked 0x11c924688 3 i.val, autoPacked 0x16c688688 3 i.val)
def autoDst171 (i : Fin 11) : Nat := autoPacked 0x11c924688 3 i.val
def autoNext171 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x8888888a8888888988888888888a888a767676768a888a8876547654888a8889767632328a88898876543210 4 (8*i.val+j.val))
theorem autoOk171 : autoGood autoExpr171 autoDfa171 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa28 autoDfa170 Bool.and) autoDfa171 autoSrc171 autoDst171 autoNext171
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk28 autoOk170)
  · rfl

def autoExpr172 : AutoF := .con autoExpr171 autoExpr72
def autoDfa172 : AutoM Nat := autoPackedTab 0x555755578555515794 2
def autoSrc172 (i : Fin 12) : Nat × Nat := (autoPacked 0x8da923440 3 i.val, autoPacked 0x90968b448 3 i.val)
def autoDst172 (i : Fin 12) : Nat := autoPacked 0x755794 2 i.val
def autoNext172 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0x5555555b5555555a5555555955559898555b555b5576557655555555555b555a55769843555559555555982176554321 4 (8*i.val+j.val))
theorem autoOk172 : autoGood autoExpr172 autoDfa172 0 := by
  apply autoTransfer (N := 11) (autoCombine autoDfa171 autoDfa72 Bool.and) autoDfa172 autoSrc172 autoDst172 autoNext172
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk171 autoOk72)
  · rfl

def autoExpr173 : AutoF := .disj autoExpr168 autoExpr172
def autoDfa173 : AutoM Nat := autoPackedTab 0x555755578555515794 2
def autoSrc173 (i : Fin 4) : Nat × Nat := (autoPacked 0x0 1 i.val, autoPacked 0xe4 2 i.val)
def autoDst173 (i : Fin 4) : Nat := autoPacked 0xe4 2 i.val
def autoNext173 (i : Fin 4) (j : Fin 8) : Fin 4 := Fin.ofNat 4 (autoPacked 0x5557555e555555e5 2 (8*i.val+j.val))
theorem autoOk173 : autoGood autoExpr173 autoDfa173 0 := by
  apply autoTransfer (N := 3) (autoCombine autoDfa168 autoDfa172 Bool.or) autoDfa173 autoSrc173 autoDst173 autoNext173
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk168 autoOk172)
  · rfl

def autoExpr174 : AutoF := .disj autoExpr160 autoExpr173
def autoDfa174 : AutoM Nat := autoPackedTab 0x555755578555515794 2
def autoSrc174 (i : Fin 4) : Nat × Nat := (autoPacked 0x0 1 i.val, autoPacked 0xe4 2 i.val)
def autoDst174 (i : Fin 4) : Nat := autoPacked 0xe4 2 i.val
def autoNext174 (i : Fin 4) (j : Fin 8) : Fin 4 := Fin.ofNat 4 (autoPacked 0x5557555e555555e5 2 (8*i.val+j.val))
theorem autoOk174 : autoGood autoExpr174 autoDfa174 0 := by
  apply autoTransfer (N := 3) (autoCombine autoDfa160 autoDfa173 Bool.or) autoDfa174 autoSrc174 autoDst174 autoNext174
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk160 autoOk173)
  · rfl

def autoExpr175 : AutoF := .con autoExpr28 autoExpr174
def autoDfa175 : AutoM Nat := autoPackedTab 0x555755578555515794 2
def autoSrc175 (i : Fin 8) : Nat × Nat := (autoPacked 0x6a3440 3 i.val, autoPacked 0x5794 2 i.val)
def autoDst175 (i : Fin 8) : Nat := autoPacked 0x5794 2 i.val
def autoNext175 (i : Fin 8) (j : Fin 8) : Fin 8 := Fin.ofNat 8 (autoPacked 0xb6db6fb6dfbeb6db6db6db6cb6dfa3b6dbedb6df91b6d8d1 3 (8*i.val+j.val))
theorem autoOk175 : autoGood autoExpr175 autoDfa175 0 := by
  apply autoTransfer (N := 7) (autoCombine autoDfa28 autoDfa174 Bool.and) autoDfa175 autoSrc175 autoDst175 autoNext175
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk28 autoOk174)
  · rfl

def autoExpr176 : AutoF := (.ge ⟨0,-1,1,0⟩)
def autoDfa176 : AutoM Nat := autoPackedTab 0x33c19 1
def autoSrc176 (i : Fin 2) : AutoLit := (#[(.ge ⟨0,-1,1,0⟩),(.ge ⟨0,-1,1,-1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst176 (i : Fin 2) : Nat := autoPacked 0x2 1 i.val
def autoNext176 (i : Fin 2) (j : Fin 8) : Fin 2 := Fin.ofNat 2 (autoPacked 0xcf0c 1 (8*i.val+j.val))
theorem autoOk176 : autoGood autoExpr176 autoDfa176 0 := by
  apply autoTransfer (N := 1) autoAtom autoDfa176 autoSrc176 autoDst176 autoNext176
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨0,-1,1,0⟩))
  · rfl

def autoExpr177 : AutoF := .con autoExpr6 autoExpr176
def autoDfa177 : AutoM Nat := autoPackedTab 0xdb6db73b6db6c36df6dcd963560db7db60d58d3437db6d85843440 3
def autoSrc177 (i : Fin 10) : Nat × Nat := (autoPacked 0x2cb1a688 3 i.val, autoPacked 0x18c 1 i.val)
def autoDst177 (i : Fin 10) : Nat := autoPacked 0x3edac688 3 i.val
def autoNext177 (i : Fin 10) (j : Fin 8) : Fin 10 := Fin.ofNat 10 (autoPacked 0x66668869886688888866888766668866666988695454325488698887325432326966876654103210 4 (8*i.val+j.val))
theorem autoOk177 : autoGood autoExpr177 autoDfa177 0 := by
  apply autoTransfer (N := 9) (autoCombine autoDfa6 autoDfa176 Bool.and) autoDfa177 autoSrc177 autoDst177 autoNext177
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk176)
  · rfl

def autoExpr178 : AutoF := .con autoExpr177 autoExpr150
def autoDfa178 : AutoM Nat := autoPackedTab 0x12492612632a304c651409249244649440 3
def autoSrc178 (i : Fin 16) : Nat × Nat := (autoPacked 0xf635f6b08688 3 i.val, autoPacked 0x72491c6a4688 3 i.val)
def autoDst178 (i : Fin 16) : Nat := autoPacked 0x8492498c9288 3 i.val
def autoNext178 (i : Fin 16) (j : Fin 8) : Fin 16 := Fin.ofNat 16 (autoPacked 0x8888888f888a888aededcbed888a8888cbedcbcb8888888a8888888988888888888a888fed7632768a888888ed54cb54888a8889cb7632328a88898876543210 4 (8*i.val+j.val))
theorem autoOk178 : autoGood autoExpr178 autoDfa178 0 := by
  apply autoTransfer (N := 15) (autoCombine autoDfa177 autoDfa150 Bool.and) autoDfa178 autoSrc178 autoDst178 autoNext178
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk177 autoOk150)
  · rfl

def autoExpr179 : AutoF := (.ge ⟨-2,-1,1,0⟩)
def autoDfa179 : AutoM Nat := autoPackedTab 0xe9ee267a4949911251 2
def autoSrc179 (i : Fin 4) : AutoLit := (#[(.ge ⟨-2,-1,1,0⟩),(.ge ⟨-2,-1,1,-1⟩),(.ge ⟨-2,-1,1,-2⟩),(.ge ⟨-2,-1,1,-3⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst179 (i : Fin 4) : Nat := autoPacked 0xe4 2 i.val
def autoNext179 (i : Fin 4) (j : Fin 8) : Fin 4 := Fin.ofNat 4 (autoPacked 0xe9ee99e994994494 2 (8*i.val+j.val))
theorem autoOk179 : autoGood autoExpr179 autoDfa179 0 := by
  apply autoTransfer (N := 3) autoAtom autoDfa179 autoSrc179 autoDst179 autoNext179
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨-2,-1,1,0⟩))
  · rfl

def autoExpr180 : AutoF := .con autoExpr6 autoExpr179
def autoDfa180 : AutoM Nat := autoPackedTab 0x92493492692488e32a3054651409249244641440 3
def autoSrc180 (i : Fin 12) : Nat × Nat := (autoPacked 0xb2591a688 3 i.val, autoPacked 0x319494 2 i.val)
def autoDst180 (i : Fin 12) : Nat := autoPacked 0xa49263288 3 i.val
def autoNext180 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0x6969766ba776a7a769697669766976787676a77676697676766b7678545432547678a778325432327869787654103210 4 (8*i.val+j.val))
theorem autoOk180 : autoGood autoExpr180 autoDfa180 0 := by
  apply autoTransfer (N := 11) (autoCombine autoDfa6 autoDfa179 Bool.and) autoDfa180 autoSrc180 autoDst180 autoNext180
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk179)
  · rfl

def autoExpr181 : AutoF := .con autoExpr6 autoExpr3
def autoDfa181 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc181 (i : Fin 10) : Nat × Nat := (autoPacked 0x24964688 3 i.val, autoPacked 0x2109a208 3 i.val)
def autoDst181 (i : Fin 10) : Nat := autoPacked 0x24964688 3 i.val
def autoNext181 (i : Fin 10) (j : Fin 8) : Fin 10 := Fin.ofNat 10 (autoPacked 0x98989898545454548787878787875456545498988787545454565456323232325654565432103210 4 (8*i.val+j.val))
theorem autoOk181 : autoGood autoExpr181 autoDfa181 0 := by
  apply autoTransfer (N := 9) (autoCombine autoDfa6 autoDfa3 Bool.and) autoDfa181 autoSrc181 autoDst181 autoNext181
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk3)
  · rfl
