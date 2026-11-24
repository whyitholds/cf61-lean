import AutoCert0
import AutoCert5

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr87 : AutoF := .con autoExpr6 autoExpr86
def autoDfa87 : AutoM Nat := autoPackedTab 0x924934926924834924910c4514092492444c9440 3
def autoSrc87 (i : Fin 20) : Nat × Nat := (autoPacked 0x92c924a9d8c8688 3 i.val, autoPacked 0x890eeea49361688 3 i.val)
def autoDst87 (i : Fin 20) : Nat := autoPacked 0x269249249319288 3 i.val
def autoNext87 (i : Fin 20) (j : Fin 8) : Fin 20 := Fin.ofNat 20 (autoPacked 0x748f0735e769db23c9d269db23c9d16ca67748f0735e7634f371dcd3b58d3c9d271dcd3b58d61d8e3c9d271dcb4a92a4a92a39ce839ce839ce739ce839ce739ce73c9d171dcb744f072de74a8244a82471dcb3b58b328c2488623a0e73a0e7308a418820 5 (8*i.val+j.val))
theorem autoOk87 : autoGood autoExpr87 autoDfa87 0 := by
  apply autoTransfer (N := 19) (autoCombine autoDfa6 autoDfa86 Bool.and) autoDfa87 autoSrc87 autoDst87 autoNext87
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk86)
  · rfl

def autoExpr88 : AutoF := .con autoExpr85 autoExpr87
def autoDfa88 : AutoM Nat := autoPackedTab 0x924934926924834924910c4514092492444c9440 3
def autoSrc88 (i : Fin 11) : Nat × Nat := (autoPacked 0x1558c8688 3 i.val, autoPacked 0x149319288 3 i.val)
def autoDst88 (i : Fin 11) : Nat := autoPacked 0x149319288 3 i.val
def autoNext88 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x7777777a393939397777777877777777777a77787a7778773914391477787778696232327877787762543210 4 (8*i.val+j.val))
theorem autoOk88 : autoGood autoExpr88 autoDfa88 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa85 autoDfa87 Bool.and) autoDfa88 autoSrc88 autoDst88 autoNext88
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk85 autoOk87)
  · rfl

def autoExpr89 : AutoF := .con autoExpr83 autoExpr88
def autoDfa89 : AutoM Nat := autoPackedTab 0x924934926924826328b049651409249241649440 3
def autoSrc89 (i : Fin 14) : Nat × Nat := (autoPacked 0x2d90b459088 3 i.val, autoPacked 0xd329313288 3 i.val)
def autoDst89 (i : Fin 14) : Nat := autoPacked 0xd309259288 3 i.val
def autoNext89 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0x1111111d1111111c111d1111111c11111111111918b81718171817171119111168a512151911111118131713676512121111111165431210 4 (8*i.val+j.val))
theorem autoOk89 : autoGood autoExpr89 autoDfa89 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa83 autoDfa88 Bool.and) autoDfa89 autoSrc89 autoDst89 autoNext89
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk83 autoOk88)
  · rfl

def autoExpr90 : AutoF := (.ge ⟨5,0,-1,0⟩)
def autoDfa90 : AutoM Nat := autoPackedTab 0x2bae9a4c71d7592088202d34514208238c9451041 3
def autoSrc90 (i : Fin 6) : AutoLit := (#[(.ge ⟨5,0,-1,0⟩),(.ge ⟨5,0,-1,2⟩),(.ge ⟨5,0,-1,-1⟩),(.ge ⟨5,0,-1,1⟩),(.ge ⟨5,0,-1,3⟩),(.ge ⟨5,0,-1,4⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst90 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext90 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0xaeba698e3aeb20882069a28a8208e328a208 3 (8*i.val+j.val))
theorem autoOk90 : autoGood autoExpr90 autoDfa90 0 := by
  apply autoTransfer (N := 5) autoAtom autoDfa90 autoSrc90 autoDst90 autoNext90
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨5,0,-1,0⟩))
  · rfl

def autoExpr91 : AutoF := .con autoExpr6 autoExpr90
def autoDfa91 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc91 (i : Fin 16) : Nat × Nat := (autoPacked 0x923365910688 3 i.val, autoPacked 0x54b6038d2208 3 i.val)
def autoDst91 (i : Fin 16) : Nat := autoPacked 0x923365910688 3 i.val
def autoNext91 (i : Fin 16) (j : Fin 8) : Fin 16 := Fin.ofNat 16 (autoPacked 0x6f6fdfdfe6e6eded79797676d9da797adad97a79dfdfd9dadfdfd9d9d9d9797a7676e6e6d9d97979c5c53535c5b43514797a7678353532327a79787635143210 4 (8*i.val+j.val))
theorem autoOk91 : autoGood autoExpr91 autoDfa91 0 := by
  apply autoTransfer (N := 15) (autoCombine autoDfa6 autoDfa90 Bool.and) autoDfa91 autoSrc91 autoDst91 autoNext91
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk90)
  · rfl

def autoExpr92 : AutoF := (.ge ⟨-5,0,1,0⟩)
def autoDfa92 : AutoM Nat := autoPackedTab 0x2aaa9a4104186069aaaa0618e381c71a682081041 3
def autoSrc92 (i : Fin 6) : AutoLit := (#[(.ge ⟨-5,0,1,0⟩),(.ge ⟨-5,0,1,-3⟩),(.ge ⟨-5,0,1,-2⟩),(.ge ⟨-5,0,1,-4⟩),(.ge ⟨-5,0,1,-1⟩),(.ge ⟨-5,0,1,-5⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst92 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext92 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0xaaaa6920830c69aaaa30c71c71c69a410208 3 (8*i.val+j.val))
theorem autoOk92 : autoGood autoExpr92 autoDfa92 0 := by
  apply autoTransfer (N := 5) autoAtom autoDfa92 autoSrc92 autoDst92 autoNext92
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨-5,0,1,0⟩))
  · rfl

def autoExpr93 : AutoF := .con autoExpr6 autoExpr92
def autoDfa93 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc93 (i : Fin 14) : Nat × Nat := (autoPacked 0x24965919688 3 i.val, autoPacked 0x5322692208 3 i.val)
def autoDst93 (i : Fin 14) : Nat := autoPacked 0x0 1 i.val
def autoNext93 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0x6d6dbdbdc6c6cbcb79797676bdbdb9babdbdb9b9b9b9797a7676c6c6b9b97979b9ba797abab97a79797a7678525232327a79787652403210 4 (8*i.val+j.val))
theorem autoOk93 : autoGood autoExpr93 autoDfa93 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa6 autoDfa92 Bool.and) autoDfa93 autoSrc93 autoDst93 autoNext93
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk92)
  · rfl

def autoExpr94 : AutoF := .con autoExpr91 autoExpr93
def autoDfa94 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc94 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst94 (i : Fin 6) : Nat := autoPacked 0x0 1 i.val
def autoNext94 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk94 : autoGood autoExpr94 autoDfa94 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa91 autoDfa93 Bool.and) autoDfa94 autoSrc94 autoDst94 autoNext94
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk91 autoOk93)
  · rfl

def autoExpr95 : AutoF := (.ge ⟨0,-1,0,0⟩)
def autoDfa95 : AutoM Nat := autoPackedTab 0x3fd99 1
def autoSrc95 (i : Fin 2) : AutoLit := (#[(.ge ⟨0,-1,0,0⟩),(.ge ⟨0,-1,0,-1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst95 (i : Fin 2) : Nat := autoPacked 0x2 1 i.val
def autoNext95 (i : Fin 2) (j : Fin 8) : Fin 2 := Fin.ofNat 2 (autoPacked 0xffcc 1 (8*i.val+j.val))
theorem autoOk95 : autoGood autoExpr95 autoDfa95 0 := by
  apply autoTransfer (N := 1) autoAtom autoDfa95 autoSrc95 autoDst95 autoNext95
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨0,-1,0,0⟩))
  · rfl

def autoExpr96 : AutoF := .con autoExpr6 autoExpr95
def autoDfa96 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc96 (i : Fin 7) : Nat × Nat := (autoPacked 0x12c688 3 i.val, autoPacked 0x6c 1 i.val)
def autoDst96 (i : Fin 7) : Nat := autoPacked 0x0 1 i.val
def autoNext96 (i : Fin 7) (j : Fin 8) : Fin 7 := Fin.ofNat 7 (autoPacked 0xdb6db6db6db5da4da4db5db569a69ad64d64688688 3 (8*i.val+j.val))
theorem autoOk96 : autoGood autoExpr96 autoDfa96 0 := by
  apply autoTransfer (N := 6) (autoCombine autoDfa6 autoDfa95 Bool.and) autoDfa96 autoSrc96 autoDst96 autoNext96
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk95)
  · rfl

def autoExpr97 : AutoF := (.ge ⟨0,1,0,0⟩)
def autoDfa97 : AutoM Nat := autoAlways
def autoSrc97 (i : Fin 1) : AutoLit := (#[(.ge ⟨0,1,0,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst97 (i : Fin 1) : Nat := autoPacked 0x0 1 i.val
def autoNext97 (i : Fin 1) (j : Fin 8) : Fin 1 := Fin.ofNat 1 (autoPacked 0x0 1 (8*i.val+j.val))
theorem autoOk97 : autoGood autoExpr97 autoDfa97 0 := by
  apply autoTransfer (N := 0) autoAtom autoDfa97 autoSrc97 autoDst97 autoNext97
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨0,1,0,0⟩))
  · rfl

def autoExpr98 : AutoF := .con autoExpr6 autoExpr97
def autoDfa98 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc98 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst98 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext98 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk98 : autoGood autoExpr98 autoDfa98 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa6 autoDfa97 Bool.and) autoDfa98 autoSrc98 autoDst98 autoNext98
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk97)
  · rfl

def autoExpr99 : AutoF := .con autoExpr96 autoExpr98
def autoDfa99 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc99 (i : Fin 6) : Nat × Nat := (autoPacked 0x0 1 i.val, autoPacked 0x2c688 3 i.val)
def autoDst99 (i : Fin 6) : Nat := autoPacked 0x0 1 i.val
def autoNext99 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk99 : autoGood autoExpr99 autoDfa99 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa96 autoDfa98 Bool.and) autoDfa99 autoSrc99 autoDst99 autoNext99
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk96 autoOk98)
  · rfl

def autoExpr100 : AutoF := .con autoExpr94 autoExpr99
def autoDfa100 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc100 (i : Fin 1) : Nat × Nat := (autoPacked 0x0 1 i.val, autoPacked 0x0 1 i.val)
def autoDst100 (i : Fin 1) : Nat := autoPacked 0x0 1 i.val
def autoNext100 (i : Fin 1) (j : Fin 8) : Fin 1 := Fin.ofNat 1 (autoPacked 0x0 1 (8*i.val+j.val))
theorem autoOk100 : autoGood autoExpr100 autoDfa100 0 := by
  apply autoTransfer (N := 0) (autoCombine autoDfa94 autoDfa99 Bool.and) autoDfa100 autoSrc100 autoDst100 autoNext100
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk94 autoOk99)
  · rfl

def autoExpr101 : AutoF := .disj autoExpr89 autoExpr100
def autoDfa101 : AutoM Nat := autoPackedTab 0x924934926924826328b049651409249241649440 3
def autoSrc101 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst101 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext101 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x24924d24d24926328b24b28a2492492c9288 3 (8*i.val+j.val))
theorem autoOk101 : autoGood autoExpr101 autoDfa101 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa89 autoDfa100 Bool.or) autoDfa101 autoSrc101 autoDst101 autoNext101
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk89 autoOk100)
  · rfl

def autoExpr102 : AutoF := .disj autoExpr81 autoExpr101
def autoDfa102 : AutoM Nat := autoPackedTab 0x49a49a492493493a14e024d24904985340924924184b440 3
def autoSrc102 (i : Fin 8) : Nat × Nat := (autoPacked 0x36c688 3 i.val, autoPacked 0xb0b288 3 i.val)
def autoDst102 (i : Fin 8) : Nat := autoPacked 0xbac688 3 i.val
def autoNext102 (i : Fin 8) (j : Fin 8) : Fin 8 := Fin.ofNat 8 (autoPacked 0x24924f24f24d24924d27429c24d24924c29a249249309688 3 (8*i.val+j.val))
theorem autoOk102 : autoGood autoExpr102 autoDfa102 0 := by
  apply autoTransfer (N := 7) (autoCombine autoDfa81 autoDfa101 Bool.or) autoDfa102 autoSrc102 autoDst102 autoNext102
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk81 autoOk101)
  · rfl

def autoExpr103 : AutoF := .con autoExpr78 autoExpr102
def autoDfa103 : AutoM Nat := autoPackedTab 0x49a49a492493493a14e024d24904985340924924184b440 3
def autoSrc103 (i : Fin 15) : Nat × Nat := (autoPacked 0x959875763543210 4 i.val, autoPacked 0x191349261688 3 i.val)
def autoDst103 (i : Fin 15) : Nat := autoPacked 0x191349261688 3 i.val
def autoNext103 (i : Fin 15) (j : Fin 8) : Fin 15 := Fin.ofNat 15 (autoPacked 0x777a777ac9c56d3d77787778787778777777777ac9c96969777777787777777777787777c9e56d35c9b46914777a7777696562327877777765143210 4 (8*i.val+j.val))
theorem autoOk103 : autoGood autoExpr103 autoDfa103 0 := by
  apply autoTransfer (N := 14) (autoCombine autoDfa78 autoDfa102 Bool.and) autoDfa103 autoSrc103 autoDst103 autoNext103
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk78 autoOk102)
  · rfl
