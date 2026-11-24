import AutoCert0
import AutoCert1
import AutoCert6
import AutoCert7

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr117 : AutoF := .con autoExpr108 autoExpr116
def autoDfa117 : AutoM Nat := autoPackedTab 0x84864b4b0444a4a8a084494789044444448184894787084464b4604a448a4504444444408a4687430444448440892487410462543210 4
def autoSrc117 (i : Fin 16) : Nat × Nat := (autoPacked 0x49441a283440 3 i.val, autoPacked 0x4ba4948746543210 4 i.val)
def autoDst117 (i : Fin 16) : Nat := autoPacked 0x4ba4948746543210 4 i.val
def autoNext117 (i : Fin 16) (j : Fin 8) : Fin 16 := Fin.ofNat 16 (autoPacked 0x4f4f4f4f9f964e4e4f4d4d9dcccccccc9f4b489b4f7a4f7accccccc99f9b4898ccccc4cc9f464e464d7a9d75ccccccc49d469843ccccc9cc9b2a987146254321 4 (8*i.val+j.val))
theorem autoOk117 : autoGood autoExpr117 autoDfa117 0 := by
  apply autoTransfer (N := 15) (autoCombine autoDfa108 autoDfa116 Bool.and) autoDfa117 autoSrc117 autoDst117 autoNext117
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk108 autoOk116)
  · rfl

def autoExpr118 : AutoF := (.ge ⟨-2,0,1,0⟩)
def autoDfa118 : AutoM Nat := autoPackedTab 0x26664449911111 2
def autoSrc118 (i : Fin 3) : AutoLit := (#[(.ge ⟨-2,0,1,0⟩),(.ge ⟨-2,0,1,-1⟩),(.ge ⟨-2,0,1,-2⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst118 (i : Fin 3) : Nat := autoPacked 0x24 2 i.val
def autoNext118 (i : Fin 3) (j : Fin 8) : Fin 3 := Fin.ofNat 3 (autoPacked 0x999944994444 2 (8*i.val+j.val))
theorem autoOk118 : autoGood autoExpr118 autoDfa118 0 := by
  apply autoTransfer (N := 2) autoAtom autoDfa118 autoSrc118 autoDst118 autoNext118
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨-2,0,1,0⟩))
  · rfl

def autoExpr119 : AutoF := .con autoExpr6 autoExpr118
def autoDfa119 : AutoM Nat := autoPackedTab 0x2492494c9249209259240d34d3425924903443440 3
def autoSrc119 (i : Fin 9) : Nat × Nat := (autoPacked 0x5964688 3 i.val, autoPacked 0x1944 2 i.val)
def autoDst119 (i : Fin 9) : Nat := autoPacked 0x5924688 3 i.val
def autoNext119 (i : Fin 9) (j : Fin 8) : Fin 9 := Fin.ofNat 9 (autoPacked 0x474747484747474747475456545454544747545447485456323232324847565432103210 4 (8*i.val+j.val))
theorem autoOk119 : autoGood autoExpr119 autoDfa119 0 := by
  apply autoTransfer (N := 8) (autoCombine autoDfa6 autoDfa118 Bool.and) autoDfa119 autoSrc119 autoDst119 autoNext119
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk118)
  · rfl

def autoExpr120 : AutoF := .con autoExpr17 autoExpr88
def autoDfa120 : AutoM Nat := autoPackedTab 0x924934926924834924910c4514092492444c9440 3
def autoSrc120 (i : Fin 11) : Nat × Nat := (autoPacked 0x16c6a3088 3 i.val, autoPacked 0x69263288 3 i.val)
def autoDst120 (i : Fin 11) : Nat := autoPacked 0x69263288 3 i.val
def autoNext120 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x1111111a11111119111a11111a11111186861616111911111911111186731613565212121111111152431210 4 (8*i.val+j.val))
theorem autoOk120 : autoGood autoExpr120 autoDfa120 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa17 autoDfa88 Bool.and) autoDfa120 autoSrc120 autoDst120 autoNext120
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk17 autoOk88)
  · rfl

def autoExpr121 : AutoF := (.ge ⟨5,1,-1,-1⟩)
def autoDfa121 : AutoM Nat := autoPackedTab 0x18d3a6269af1a4d71d35988a8e22511114638ab8c90c1440 3
def autoSrc121 (i : Fin 7) : AutoLit := (#[(.ge ⟨5,1,-1,-1⟩),(.ge ⟨5,1,-1,2⟩),(.ge ⟨5,1,-1,0⟩),(.ge ⟨5,1,-1,1⟩),(.ge ⟨5,1,-1,3⟩),(.ge ⟨5,1,-1,4⟩),(.ge ⟨5,1,-1,5⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst121 (i : Fin 7) : Nat := autoPacked 0x1ac688 3 i.val
def autoNext121 (i : Fin 7) (j : Fin 8) : Fin 7 := Fin.ofNat 7 (autoPacked 0xc69d31a6bc69ae3a6b88a8e228888a8e2ae3218288 3 (8*i.val+j.val))
theorem autoOk121 : autoGood autoExpr121 autoDfa121 0 := by
  apply autoTransfer (N := 6) autoAtom autoDfa121 autoSrc121 autoDst121 autoNext121
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨5,1,-1,-1⟩))
  · rfl

def autoExpr122 : AutoF := .con autoExpr6 autoExpr121
def autoDfa122 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc122 (i : Fin 17) : Nat × Nat := (autoPacked 0x48e5725911688 3 i.val, autoPacked 0xcca8ab8c3288 3 i.val)
def autoDst122 (i : Fin 17) : Nat := autoPacked 0x48e5725911688 3 i.val
def autoNext122 (i : Fin 17) (j : Fin 8) : Fin 17 := Fin.ofNat 17 (autoPacked 0x6c0d06a9b07b52d79ded3a9ac398ec398ea498e66a9b03a9ac498e84b5286a9b03a9aa4b5267b52d3a9aa398ec498e64b5263a9aa398ea195c5188653b1aa3a0ea398ec498e818865588623a0ea4a0e61948018820 5 (8*i.val+j.val))
theorem autoOk122 : autoGood autoExpr122 autoDfa122 0 := by
  apply autoTransfer (N := 16) (autoCombine autoDfa6 autoDfa121 Bool.and) autoDfa122 autoSrc122 autoDst122 autoNext122
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk121)
  · rfl

def autoExpr123 : AutoF := (.dis ⟨-5,0,1,0⟩ ⟨0,1,0,0⟩)
def autoDfa123 : AutoM Nat := autoPackedTab 0x9e79621020a34451a79828d5650924924159628c34c2041 3
def autoSrc123 (i : Fin 7) : AutoLit := (#[(.dis ⟨-5,0,1,0⟩ ⟨0,1,0,0⟩),(.dis ⟨-5,0,1,-3⟩ ⟨0,1,0,0⟩),(.no),(.dis ⟨-5,0,1,-2⟩ ⟨0,1,0,0⟩),(.dis ⟨-5,0,1,-4⟩ ⟨0,1,0,0⟩),(.dis ⟨-5,0,1,-1⟩ ⟨0,1,0,0⟩),(.dis ⟨-5,0,1,-5⟩ ⟨0,1,0,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst123 (i : Fin 7) : Nat := autoPacked 0x1ac688 3 i.val
def autoNext123 (i : Fin 7) (j : Fin 8) : Fin 7 := Fin.ofNat 7 (autoPacked 0x4f3cb140828d8a34f328d5654924925658a3698408 3 (8*i.val+j.val))
theorem autoOk123 : autoGood autoExpr123 autoDfa123 0 := by
  apply autoTransfer (N := 6) autoAtom autoDfa123 autoSrc123 autoDst123 autoNext123
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.dis ⟨-5,0,1,0⟩ ⟨0,1,0,0⟩))
  · rfl

def autoExpr124 : AutoF := .con autoExpr6 autoExpr123
def autoDfa124 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc124 (i : Fin 18) : Nat × Nat := (autoPacked 0x2c91cb2c8d1688 3 i.val, autoPacked 0x18c4ab546d3408 3 i.val)
def autoDst124 (i : Fin 18) : Nat := autoPacked 0x0 1 i.val
def autoNext124 (i : Fin 18) (j : Fin 8) : Fin 18 := Fin.ofNat 18 (autoPacked 0x731ca6290b3b0f0641d061de77b1ee6290a431076290b431116318c6318c641d0731cb641d0731ca6318c631894310761de7731ca6290a731cb6290b1946519465725ca62d0a6318963189314c2189a262d0a425073148018820 5 (8*i.val+j.val))
theorem autoOk124 : autoGood autoExpr124 autoDfa124 0 := by
  apply autoTransfer (N := 17) (autoCombine autoDfa6 autoDfa123 Bool.and) autoDfa124 autoSrc124 autoDst124 autoNext124
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk123)
  · rfl

def autoExpr125 : AutoF := .con autoExpr122 autoExpr124
def autoDfa125 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc125 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst125 (i : Fin 6) : Nat := autoPacked 0x0 1 i.val
def autoNext125 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk125 : autoGood autoExpr125 autoDfa125 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa122 autoDfa124 Bool.and) autoDfa125 autoSrc125 autoDst125 autoNext125
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk122 autoOk124)
  · rfl

def autoExpr126 : AutoF := .con autoExpr93 autoExpr125
def autoDfa126 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc126 (i : Fin 1) : Nat × Nat := (autoPacked 0x0 1 i.val, autoPacked 0x0 1 i.val)
def autoDst126 (i : Fin 1) : Nat := autoPacked 0x0 1 i.val
def autoNext126 (i : Fin 1) (j : Fin 8) : Fin 1 := Fin.ofNat 1 (autoPacked 0x0 1 (8*i.val+j.val))
theorem autoOk126 : autoGood autoExpr126 autoDfa126 0 := by
  apply autoTransfer (N := 0) (autoCombine autoDfa93 autoDfa125 Bool.and) autoDfa126 autoSrc126 autoDst126 autoNext126
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk93 autoOk125)
  · rfl

def autoExpr127 : AutoF := .disj autoExpr120 autoExpr126
def autoDfa127 : AutoM Nat := autoPackedTab 0x924934926924834924910c4514092492444c9440 3
def autoSrc127 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst127 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext127 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x24924d24d24934924986228a249249899288 3 (8*i.val+j.val))
theorem autoOk127 : autoGood autoExpr127 autoDfa127 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa120 autoDfa126 Bool.or) autoDfa127 autoSrc127 autoDst127 autoNext127
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk120 autoOk126)
  · rfl

def autoExpr128 : AutoF := .con autoExpr119 autoExpr127
def autoDfa128 : AutoM Nat := autoPackedTab 0x924934926924834924910c4514092492444c9440 3
def autoSrc128 (i : Fin 11) : Nat × Nat := (autoPacked 0x1558c8688 3 i.val, autoPacked 0x149319288 3 i.val)
def autoDst128 (i : Fin 11) : Nat := autoPacked 0x149319288 3 i.val
def autoNext128 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x7777777a393939397777777877777777777a77777a7777773914391477787777696232327877777762543210 4 (8*i.val+j.val))
theorem autoOk128 : autoGood autoExpr128 autoDfa128 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa119 autoDfa127 Bool.and) autoDfa128 autoSrc128 autoDst128 autoNext128
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk119 autoOk127)
  · rfl

def autoExpr129 : AutoF := .disj autoExpr117 autoExpr128
def autoDfa129 : AutoM Nat := autoPackedTab 0xc4c74e4e0444d4dad0444a444a1c48b49ab04444444a1c4cb49a90444a44440c4874e4704a444a4404d44ad450444444440cd87a943044444a440cb64a9410876543210 4
def autoSrc129 (i : Fin 16) : Nat × Nat := (autoPacked 0xb4a8987462543210 4 i.val, autoPacked 0x54c4544c9440 3 i.val)
def autoDst129 (i : Fin 16) : Nat := autoPacked 0xeadcba9876543210 4 i.val
def autoNext129 (i : Fin 16) (j : Fin 8) : Fin 16 := Fin.ofNat 16 (autoPacked 0xc4c74f4f4444444e444d4dad444e444ac48b49ab4444444ac4cb49a9444e4444c4874f474e444a444d44ad4544444444cd87a94344444a44cb64a94187654321 4 (8*i.val+j.val))
theorem autoOk129 : autoGood autoExpr129 autoDfa129 0 := by
  apply autoTransfer (N := 15) (autoCombine autoDfa117 autoDfa128 Bool.or) autoDfa129 autoSrc129 autoDst129 autoNext129
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk117 autoOk128)
  · rfl

def autoExpr130 : AutoF := .neg autoExpr129
def autoDfa130 : AutoM Nat := autoFlip autoDfa129
theorem autoOk130 : autoGood autoExpr130 autoDfa130 0 := (autoGoodNeg _ autoOk129)
