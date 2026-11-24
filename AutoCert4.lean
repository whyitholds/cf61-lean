import AutoCert0
import AutoCert3

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr58 : AutoF := .con autoExpr55 autoExpr57
def autoDfa58 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc58 (i : Fin 8) : Nat × Nat := (autoPacked 0x0 1 i.val, autoPacked 0xfac688 3 i.val)
def autoDst58 (i : Fin 8) : Nat := autoPacked 0x0 1 i.val
def autoNext58 (i : Fin 8) (j : Fin 8) : Fin 8 := Fin.ofNat 8 (autoPacked 0x924927927927d35975924924d64d639e49e4d54d619118d1 3 (8*i.val+j.val))
theorem autoOk58 : autoGood autoExpr58 autoDfa58 0 := by
  apply autoTransfer (N := 7) (autoCombine autoDfa55 autoDfa57 Bool.and) autoDfa58 autoSrc58 autoDst58 autoNext58
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk55 autoOk57)
  · rfl

def autoExpr59 : AutoF := .con autoExpr53 autoExpr58
def autoDfa59 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc59 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst59 (i : Fin 6) : Nat := autoPacked 0x0 1 i.val
def autoNext59 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk59 : autoGood autoExpr59 autoDfa59 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa53 autoDfa58 Bool.and) autoDfa59 autoSrc59 autoDst59 autoNext59
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk53 autoOk58)
  · rfl

def autoExpr60 : AutoF := (.ge ⟨1,-1,1,1⟩)
def autoDfa60 : AutoM Nat := autoPackedTab 0x19698516544145 2
def autoSrc60 (i : Fin 3) : AutoLit := (#[(.ge ⟨1,-1,1,1⟩),(.ge ⟨1,-1,1,0⟩),(.ge ⟨1,-1,1,-1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst60 (i : Fin 3) : Nat := autoPacked 0x24 2 i.val
def autoNext60 (i : Fin 3) (j : Fin 8) : Fin 3 := Fin.ofNat 3 (autoPacked 0x65a651651051 2 (8*i.val+j.val))
theorem autoOk60 : autoGood autoExpr60 autoDfa60 0 := by
  apply autoTransfer (N := 2) autoAtom autoDfa60 autoSrc60 autoDst60 autoNext60
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨1,-1,1,1⟩))
  · rfl

def autoExpr61 : AutoF := .con autoExpr6 autoExpr60
def autoDfa61 : AutoM Nat := autoPackedTab 0x777877770777777781777777770464396460787777770777877781434346430787778770432146510432043210 4
def autoSrc61 (i : Fin 15) : Nat × Nat := (autoPacked 0xed96445b440 3 i.val, autoPacked 0x28919144 2 i.val)
def autoDst61 (i : Fin 15) : Nat := autoPacked 0x978787765443210 4 i.val
def autoNext61 (i : Fin 15) (j : Fin 8) : Fin 15 := Fin.ofNat 15 (autoPacked 0x8b8abb8d8b88bb8d9899889a8b88bb8b88988b8a9899889888988b884743e7478a988d88989c889a889a8b8a435347439a998a984321476153204321 4 (8*i.val+j.val))
theorem autoOk61 : autoGood autoExpr61 autoDfa61 0 := by
  apply autoTransfer (N := 14) (autoCombine autoDfa6 autoDfa60 Bool.and) autoDfa61 autoSrc61 autoDst61 autoNext61
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk60)
  · rfl

def autoExpr62 : AutoF := (.ge ⟨1,0,-1,-1⟩)
def autoDfa62 : AutoM Nat := autoPackedTab 0x2be14 1
def autoSrc62 (i : Fin 2) : AutoLit := (#[(.ge ⟨1,0,-1,-1⟩),(.ge ⟨1,0,-1,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst62 (i : Fin 2) : Nat := autoPacked 0x2 1 i.val
def autoNext62 (i : Fin 2) (j : Fin 8) : Fin 2 := Fin.ofNat 2 (autoPacked 0xaf0a 1 (8*i.val+j.val))
theorem autoOk62 : autoGood autoExpr62 autoDfa62 0 := by
  apply autoTransfer (N := 1) autoAtom autoDfa62 autoSrc62 autoDst62 autoNext62
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨1,0,-1,-1⟩))
  · rfl

def autoExpr63 : AutoF := .con autoExpr6 autoExpr62
def autoDfa63 : AutoM Nat := autoPackedTab 0x49249209249233144d3424923904503440 3
def autoSrc63 (i : Fin 10) : Nat × Nat := (autoPacked 0x2cb19688 3 i.val, autoPacked 0xca 1 i.val)
def autoDst63 (i : Fin 10) : Nat := autoPacked 0x24724688 3 i.val
def autoNext63 (i : Fin 10) (j : Fin 8) : Fin 10 := Fin.ofNat 10 (autoPacked 0x88886869888868686868666768686666888968698988696868696667525232326968676652403210 4 (8*i.val+j.val))
theorem autoOk63 : autoGood autoExpr63 autoDfa63 0 := by
  apply autoTransfer (N := 9) (autoCombine autoDfa6 autoDfa62 Bool.and) autoDfa63 autoSrc63 autoDst63 autoNext63
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk62)
  · rfl

def autoExpr64 : AutoF := (.dis ⟨1,0,1,0⟩ ⟨0,1,0,-2⟩)
def autoDfa64 : AutoM Nat := autoPackedTab 0x15b6ab0d562921b53b1a09249242c6a44434ca248 3
def autoSrc64 (i : Fin 6) : AutoLit := (#[(.dis ⟨1,0,1,0⟩ ⟨0,1,0,-2⟩),(.dis ⟨1,0,1,0⟩ ⟨0,1,0,-1⟩),(.no),(.dis ⟨1,0,1,1⟩ ⟨0,1,0,-1⟩),(.dis ⟨1,0,1,0⟩ ⟨0,1,0,0⟩),(.dis ⟨1,0,1,1⟩ ⟨0,1,0,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst64 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext64 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x56daacaac524b53b1a492492b1a911699449 3 (8*i.val+j.val))
theorem autoOk64 : autoGood autoExpr64 autoDfa64 0 := by
  apply autoTransfer (N := 5) autoAtom autoDfa64 autoSrc64 autoDst64 autoNext64
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.dis ⟨1,0,1,0⟩ ⟨0,1,0,-2⟩))
  · rfl

def autoExpr65 : AutoF := .con autoExpr6 autoExpr64
def autoDfa65 : AutoM Nat := autoPackedTab 0x924927324f24e74d65d44924920d64d6313c93c83553584488c688 3
def autoSrc65 (i : Fin 22) : Nat × Nat := (autoPacked 0x2db24b230d168b440 3 i.val, autoPacked 0x1d55c88d52269a248 3 i.val)
def autoDst65 (i : Fin 22) : Nat := autoPacked 0x27924f269ac914688 3 i.val
def autoNext65 (i : Fin 22) (j : Fin 8) : Fin 22 := Fin.ofNat 22 (autoPacked 0x949d19423374a5293a4f739ce739d374a5293a50949d19422e93a507421093a507420f739ce739ce9422e841cd74a5493a4f2190b2190b93a4f7420f619892254974dce74dce949d5942332188621886951d193e2e739d3739d3624e65248393e2e83dcd624ab52501398a120c41 5 (8*i.val+j.val))
theorem autoOk65 : autoGood autoExpr65 autoDfa65 0 := by
  apply autoTransfer (N := 21) (autoCombine autoDfa6 autoDfa64 Bool.and) autoDfa65 autoSrc65 autoDst65 autoNext65
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk64)
  · rfl

def autoExpr66 : AutoF := .con autoExpr63 autoExpr65
def autoDfa66 : AutoM Nat := autoPackedTab 0x1b6db74b6e39606db6db0db6eb61c6ec6436cb288 3
def autoSrc66 (i : Fin 15) : Nat × Nat := (autoPacked 0x11c0d18a3440 3 i.val, autoPacked 0x1fe9ac914688 3 i.val)
def autoDst66 (i : Fin 15) : Nat := autoPacked 0xeb7636db288 3 i.val
def autoNext66 (i : Fin 15) (j : Fin 8) : Fin 15 := Fin.ofNat 15 (autoPacked 0x7777777e7777777d777e777e767b468b777e777dc6c949a97777747777777777767646467e777e7777777774c976a9437e777d77c95ba98176514321 4 (8*i.val+j.val))
theorem autoOk66 : autoGood autoExpr66 autoDfa66 0 := by
  apply autoTransfer (N := 14) (autoCombine autoDfa63 autoDfa65 Bool.and) autoDfa66 autoSrc66 autoDst66 autoNext66
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk63 autoOk65)
  · rfl

def autoExpr67 : AutoF := .con autoExpr61 autoExpr66
def autoDfa67 : AutoM Nat := autoPackedTab 0x1b6db74b6e39606db6db0db6eb61c6ec6436cb288 3
def autoSrc67 (i : Fin 19) : Nat × Nat := (autoPacked 0x9608873146532043210 4 i.val, autoPacked 0xdb75c7636cb288 3 i.val)
def autoDst67 (i : Fin 19) : Nat := autoPacked 0xdb75c7636cb288 3 i.val
def autoNext67 (i : Fin 19) (j : Fin 8) : Fin 19 := Fin.ofNat 19 (autoPacked 0x6b5af6b5ad244879449121cd021ccb6b5ad6b5af6b5ad6b5ae6b5ad6b5ad21c8c2254c21ccb2450b6b5af6b5ae2448c925496bdad6b5ad21c87244876bdad6bdad230d0530c16b5af6b5af23087524836bdad6b9ad230cb5250121cc520c41 5 (8*i.val+j.val))
theorem autoOk67 : autoGood autoExpr67 autoDfa67 0 := by
  apply autoTransfer (N := 18) (autoCombine autoDfa61 autoDfa66 Bool.and) autoDfa67 autoSrc67 autoDst67 autoNext67
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk61 autoOk66)
  · rfl

def autoExpr68 : AutoF := .con autoExpr51 autoExpr9
def autoDfa68 : AutoM Nat := autoPackedTab 0x124926124930910c2514092492442c9440 3
def autoSrc68 (i : Fin 14) : Nat × Nat := (autoPacked 0x1ed9e74c688 3 i.val, autoPacked 0x3d9f6aa0688 3 i.val)
def autoDst68 (i : Fin 14) : Nat := autoPacked 0x21249859288 3 i.val
def autoNext68 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0x8888888d888a888a8a888a888888888a8888888988888888888a888dc6c636368a888d88c6b43614888a8889767632328a88898876543210 4 (8*i.val+j.val))
theorem autoOk68 : autoGood autoExpr68 autoDfa68 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa51 autoDfa9 Bool.and) autoDfa68 autoSrc68 autoDst68 autoNext68
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk51 autoOk9)
  · rfl

def autoExpr69 : AutoF := (.ge ⟨0,-1,0,1⟩)
def autoDfa69 : AutoM Nat := autoPackedTab 0x2aaa8a5a555555 2
def autoSrc69 (i : Fin 3) : AutoLit := (#[(.ge ⟨0,-1,0,1⟩),(.ge ⟨0,-1,0,0⟩),(.ge ⟨0,-1,0,-1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst69 (i : Fin 3) : Nat := autoPacked 0x24 2 i.val
def autoNext69 (i : Fin 3) (j : Fin 8) : Fin 3 := Fin.ofNat 3 (autoPacked 0xaaaaa5a55555 2 (8*i.val+j.val))
theorem autoOk69 : autoGood autoExpr69 autoDfa69 0 := by
  apply autoTransfer (N := 2) autoAtom autoDfa69 autoSrc69 autoDst69 autoNext69
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨0,-1,0,1⟩))
  · rfl

def autoExpr70 : AutoF := .con autoExpr6 autoExpr69
def autoDfa70 : AutoM Nat := autoPackedTab 0x124926124c24c24b44b40924924344b448 3
def autoSrc70 (i : Fin 11) : Nat × Nat := (autoPacked 0x1658d3440 3 i.val, autoPacked 0x1a6954 2 i.val)
def autoDst70 (i : Fin 11) : Nat := autoPacked 0x10924b448 3 i.val
def autoNext70 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x9977997a9999999999999998997799779998999865656565997a997a65436543987798776521652143214321 4 (8*i.val+j.val))
theorem autoOk70 : autoGood autoExpr70 autoDfa70 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa6 autoDfa69 Bool.and) autoDfa70 autoSrc70 autoDst70 autoNext70
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk69)
  · rfl

def autoExpr71 : AutoF := .con autoExpr6 autoExpr1
def autoDfa71 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc71 (i : Fin 7) : Nat × Nat := (autoPacked 0x12c688 3 i.val, autoPacked 0x6c 1 i.val)
def autoDst71 (i : Fin 7) : Nat := autoPacked 0x12c688 3 i.val
def autoNext71 (i : Fin 7) (j : Fin 8) : Fin 7 := Fin.ofNat 7 (autoPacked 0xdb6db6db6db5da4da4db5db569a69ad64d64688688 3 (8*i.val+j.val))
theorem autoOk71 : autoGood autoExpr71 autoDfa71 0 := by
  apply autoTransfer (N := 6) (autoCombine autoDfa6 autoDfa1 Bool.and) autoDfa71 autoSrc71 autoDst71 autoNext71
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk1)
  · rfl
