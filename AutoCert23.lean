import AutoCert0
import AutoCert7
import AutoCert21
import AutoCert22

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr328 : AutoF := .disj autoExpr316 autoExpr327
def autoDfa328 : AutoM Nat := autoPackedTab 0x33683a3a039393368033683a68068333a370333333361396568330393468330333333330333336330683368370653433210 4
def autoSrc328 (i : Fin 11) : Nat × Nat := (autoPacked 0x0 1 i.val, autoPacked 0xa9876543210 4 i.val)
def autoDst328 (i : Fin 11) : Nat := autoPacked 0xa9876543210 4 i.val
def autoNext328 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x33683a3a3939336833683a6868333a3733333336396568333934683333333333333336336833683765343321 4 (8*i.val+j.val))
theorem autoOk328 : autoGood autoExpr328 autoDfa328 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa316 autoDfa327 Bool.or) autoDfa328 autoSrc328 autoDst328 autoNext328
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk316 autoOk327)
  · rfl

def autoExpr329 : AutoF := .con autoExpr108 autoExpr328
def autoDfa329 : AutoM Nat := autoPackedTab 0x33683a3a039393368033683a68068333a370333333361396568330393468330333333330333336330683368370653433210 4
def autoSrc329 (i : Fin 15) : Nat × Nat := (autoPacked 0x94083443440 3 i.val, autoPacked 0xa93387653433210 4 i.val)
def autoDst329 (i : Fin 15) : Nat := autoPacked 0xa93387653433210 4 i.val
def autoNext329 (i : Fin 15) (j : Fin 8) : Fin 15 := Fin.ofNat 15 (autoPacked 0x438a4e4e4d4d438acccccccc436b436b438a4e8a8a6b4e69ccccccc84d878a43ccccc4cc4d658a6bccccccc443434343ccccc8cc8a6b8a6987654321 4 (8*i.val+j.val))
theorem autoOk329 : autoGood autoExpr329 autoDfa329 0 := by
  apply autoTransfer (N := 14) (autoCombine autoDfa108 autoDfa328 Bool.and) autoDfa329 autoSrc329 autoDst329 autoNext329
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk108 autoOk328)
  · rfl

def autoExpr330 : AutoF := (.ge ⟨-4,-1,1,1⟩)
def autoDfa330 : AutoM Nat := autoPackedTab 0x1a55a682aab4a8551d5508d18e311c75461146344a2c2289 3
def autoSrc330 (i : Fin 7) : AutoLit := (#[(.ge ⟨-4,-1,1,1⟩),(.ge ⟨-4,-1,1,0⟩),(.ge ⟨-4,-1,1,-2⟩),(.ge ⟨-4,-1,1,-1⟩),(.ge ⟨-4,-1,1,-3⟩),(.ge ⟨-4,-1,1,-4⟩),(.ge ⟨-4,-1,1,-5⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst330 (i : Fin 7) : Nat := autoPacked 0x1ac688 3 i.val
def autoNext330 (i : Fin 7) (j : Fin 8) : Fin 7 := Fin.ofNat 7 (autoPacked 0xd2ad34aaad2aaa3aaa8d18e38e3aa34518d1458451 3 (8*i.val+j.val))
theorem autoOk330 : autoGood autoExpr330 autoDfa330 0 := by
  apply autoTransfer (N := 6) autoAtom autoDfa330 autoSrc330 autoDst330 autoNext330
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨-4,-1,1,1⟩))
  · rfl

def autoExpr331 : AutoF := .con autoExpr6 autoExpr330
def autoDfa331 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc331 (i : Fin 16) : Nat × Nat := (autoPacked 0x92596468b440 3 i.val, autoPacked 0xc53aa38da288 3 i.val)
def autoDst331 (i : Fin 16) : Nat := autoPacked 0x0 1 i.val
def autoNext331 (i : Fin 16) (j : Fin 8) : Fin 16 := Fin.ofNat 16 (autoPacked 0xf9bdf9f9dede98de9898bd9898de989cbdbdf9bd9898bd9cbd98bdbd98de9898bd9cbdba764376769cde9c98989cbd9c434376439c98ba984321762143504321 4 (8*i.val+j.val))
theorem autoOk331 : autoGood autoExpr331 autoDfa331 0 := by
  apply autoTransfer (N := 15) (autoCombine autoDfa6 autoDfa330 Bool.and) autoDfa331 autoSrc331 autoDst331 autoNext331
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk330)
  · rfl

def autoExpr332 : AutoF := (.ge ⟨6,0,-1,-2⟩)
def autoDfa332 : AutoM Nat := autoPackedTab 0xebaeba31c71c651475d4c71f5d1d75d753aeb1c6514514430c2288 3
def autoSrc332 (i : Fin 8) : AutoLit := (#[(.ge ⟨6,0,-1,-2⟩),(.ge ⟨6,0,-1,-1⟩),(.ge ⟨6,0,-1,2⟩),(.ge ⟨6,0,-1,1⟩),(.ge ⟨6,0,-1,4⟩),(.ge ⟨6,0,-1,0⟩),(.ge ⟨6,0,-1,3⟩),(.ge ⟨6,0,-1,5⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst332 (i : Fin 8) : Nat := autoPacked 0xfac688 3 i.val
def autoNext332 (i : Fin 8) (j : Fin 8) : Fin 8 := Fin.ofNat 8 (autoPacked 0xebaeba8e38e3451d758e3ebad75d75d758e3451451618451 3 (8*i.val+j.val))
theorem autoOk332 : autoGood autoExpr332 autoDfa332 0 := by
  apply autoTransfer (N := 7) autoAtom autoDfa332 autoSrc332 autoDst332 autoNext332
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨6,0,-1,-2⟩))
  · rfl

def autoExpr333 : AutoF := .con autoExpr6 autoExpr332
def autoDfa333 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc333 (i : Fin 17) : Nat × Nat := (autoPacked 0x492c96468b440 3 i.val, autoPacked 0x1eaeae361a288 3 i.val)
def autoDst333 (i : Fin 17) : Nat := autoPacked 0x492c96468b440 3 i.val
def autoNext333 (i : Fin 17) (j : Fin 8) : Fin 17 := Fin.ofNat 17 (autoPacked 0x741d0741d07b9ee7b9ee62d8b4a128741d062d8d4a1284a128741d062d8b62d8b62d8d4a1287b9ee62d8b62d8b62d8d62d8d398e620c836358b6358b62d8d4a12a20c8320c836358b4a92820c4120c41398a020c41 5 (8*i.val+j.val))
theorem autoOk333 : autoGood autoExpr333 autoDfa333 0 := by
  apply autoTransfer (N := 16) (autoCombine autoDfa6 autoDfa332 Bool.and) autoDfa333 autoSrc333 autoDst333 autoNext333
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk332)
  · rfl

def autoExpr334 : AutoF := (.dis ⟨-4,0,1,1⟩ ⟨0,1,0,-1⟩)
def autoDfa334 : AutoM Nat := autoPackedTab 0x76b4a311011a3a3a30761176b40321132980767611a30323211760656511321329876110117676760113232321111111110654032110 4
def autoSrc334 (i : Fin 12) : AutoLit := (#[(.dis ⟨-4,0,1,1⟩ ⟨0,1,0,-1⟩),(.no),(.dis ⟨-4,0,1,0⟩ ⟨0,1,0,0⟩),(.dis ⟨-4,0,1,-2⟩ ⟨0,1,0,0⟩),(.dis ⟨-4,0,1,-1⟩ ⟨0,1,0,-1⟩),(.dis ⟨-4,0,1,1⟩ ⟨0,1,0,0⟩),(.dis ⟨-4,0,1,-1⟩ ⟨0,1,0,0⟩),(.dis ⟨-4,0,1,-3⟩ ⟨0,1,0,0⟩),(.dis ⟨-4,0,1,0⟩ ⟨0,1,0,-1⟩),(.dis ⟨-4,0,1,-2⟩ ⟨0,1,0,-1⟩),(.dis ⟨-4,0,1,-4⟩ ⟨0,1,0,0⟩),(.dis ⟨-4,0,1,-3⟩ ⟨0,1,0,-1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst334 (i : Fin 12) : Nat := autoPacked 0xba9876543210 4 i.val
def autoNext334 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0x76b4a31111a3a3a3761176b432113298767611a332321176656511323298761111767676113232321111111165403211 4 (8*i.val+j.val))
theorem autoOk334 : autoGood autoExpr334 autoDfa334 0 := by
  apply autoTransfer (N := 11) autoAtom autoDfa334 autoSrc334 autoDst334 autoNext334
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.dis ⟨-4,0,1,1⟩ ⟨0,1,0,-1⟩))
  · rfl

def autoExpr335 : AutoF := .con autoExpr6 autoExpr334
def autoDfa335 : AutoM Nat := autoPackedTab 0x92493492692488e3249069249209249244681248 3
def autoSrc335 (i : Fin 23) : Nat × Nat := (autoPacked 0x12492c925b1a68b440 3 i.val, autoPacked 0xb4a23298676111165432110 4 i.val)
def autoDst335 (i : Fin 23) : Nat := autoPacked 0x492692492498d1248 3 i.val
def autoNext335 (i : Fin 23) (j : Fin 8) : Fin 23 := Fin.ofNat 23 (autoPacked 0x6bad5a494a94e0f6b94a52a92a4a9252a5394e53529ae6b9ae52a5394e516b94a6bad594d4a94e0f94e53529ae6b9ae52a9294e53529ac5294a5294b5294a5294a5294b5294b4a1284a12894e51529ac398e64a0839460f6b14a529ac6b9ac4a08320c8352d4a52d4a4a0414a041398a020c41 5 (8*i.val+j.val))
theorem autoOk335 : autoGood autoExpr335 autoDfa335 0 := by
  apply autoTransfer (N := 22) (autoCombine autoDfa6 autoDfa334 Bool.and) autoDfa335 autoSrc335 autoDst335 autoNext335
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk334)
  · rfl

def autoExpr336 : AutoF := .con autoExpr333 autoExpr335
def autoDfa336 : AutoM Nat := autoPackedTab 0x92493492692488e3249069249209249244681248 3
def autoSrc336 (i : Fin 11) : Nat × Nat := (autoPacked 0x16c68b440 3 i.val, autoPacked 0x1498d1248 3 i.val)
def autoDst336 (i : Fin 11) : Nat := autoPacked 0x1498d1248 3 i.val
def autoNext336 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x8888888a8888888988888888888a8889767643438a8889888889888943434343898889884321432176504321 4 (8*i.val+j.val))
theorem autoOk336 : autoGood autoExpr336 autoDfa336 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa333 autoDfa335 Bool.and) autoDfa336 autoSrc336 autoDst336 autoNext336
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk333 autoOk335)
  · rfl

def autoExpr337 : AutoF := .con autoExpr331 autoExpr336
def autoDfa337 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc337 (i : Fin 6) : Nat × Nat := (autoPacked 0x0 1 i.val, autoPacked 0x2c688 3 i.val)
def autoDst337 (i : Fin 6) : Nat := autoPacked 0x0 1 i.val
def autoNext337 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x24924d24d2498e32493492492492498d0249 3 (8*i.val+j.val))
theorem autoOk337 : autoGood autoExpr337 autoDfa337 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa331 autoDfa336 Bool.and) autoDfa337 autoSrc337 autoDst337 autoNext337
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk331 autoOk336)
  · rfl

def autoExpr338 : AutoF := (.ge ⟨6,0,-1,-1⟩)
def autoDfa338 : AutoM Nat := autoPackedTab 0x18e38e25a69a68904596169ac7136596586cb1a689041040 3
def autoSrc338 (i : Fin 7) : AutoLit := (#[(.ge ⟨6,0,-1,-1⟩),(.ge ⟨6,0,-1,2⟩),(.ge ⟨6,0,-1,1⟩),(.ge ⟨6,0,-1,4⟩),(.ge ⟨6,0,-1,0⟩),(.ge ⟨6,0,-1,3⟩),(.ge ⟨6,0,-1,5⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst338 (i : Fin 7) : Nat := autoPacked 0x1ac688 3 i.val
def autoNext338 (i : Fin 7) (j : Fin 8) : Fin 7 := Fin.ofNat 7 (autoPacked 0xc71c7169a69a208b2c69ac71b2cb2cb2c69a208208 3 (8*i.val+j.val))
theorem autoOk338 : autoGood autoExpr338 autoDfa338 0 := by
  apply autoTransfer (N := 6) autoAtom autoDfa338 autoSrc338 autoDst338 autoNext338
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨6,0,-1,-1⟩))
  · rfl

def autoExpr339 : AutoF := .con autoExpr6 autoExpr338
def autoDfa339 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc339 (i : Fin 13) : Nat × Nat := (autoPacked 0x492c964688 3 i.val, autoPacked 0xc6589a208 3 i.val)
def autoDst339 (i : Fin 13) : Nat := autoPacked 0x492c964688 3 i.val
def autoNext339 (i : Fin 13) (j : Fin 8) : Fin 13 := Fin.ofNat 13 (autoPacked 0xacacacacbabababa87875454acac878954545454acac8787878787895454baba8787878787895456323232328987565432103210 4 (8*i.val+j.val))
theorem autoOk339 : autoGood autoExpr339 autoDfa339 0 := by
  apply autoTransfer (N := 12) (autoCombine autoDfa6 autoDfa338 Bool.and) autoDfa339 autoSrc339 autoDst339 autoNext339
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk338)
  · rfl
