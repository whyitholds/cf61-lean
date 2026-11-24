import AutoCert0
import AutoCert1
import AutoCert18

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr273 : AutoF := .con autoExpr6 autoExpr272
def autoDfa273 : AutoM Nat := autoPackedTab 0x653832380777777770777777761353535350777776770777677761656832320767776770654032100 4
def autoSrc273 (i : Fin 11) : Nat × Nat := (autoPacked 0x1558d1688 3 i.val, autoPacked 0x1a930b288 3 i.val)
def autoDst273 (i : Fin 11) : Nat := autoPacked 0x78676543210 4 i.val
def autoNext273 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x7777777a653932397777777877777777777a7778353535357a77787777787778656932327877787765403210 4 (8*i.val+j.val))
theorem autoOk273 : autoGood autoExpr273 autoDfa273 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa6 autoDfa272 Bool.and) autoDfa273 autoSrc273 autoDst273 autoNext273
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk272)
  · rfl

def autoExpr274 : AutoF := .disj autoExpr273 autoExpr23
def autoDfa274 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc274 (i : Fin 11) : Nat × Nat := (autoPacked 0x78676543210 4 i.val, autoPacked 0x1a930b288 3 i.val)
def autoDst274 (i : Fin 11) : Nat := autoPacked 0x1558d1688 3 i.val
def autoNext274 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x7777777a653932397777777877777777777a7778353535357a77787777787778656932327877787765403210 4 (8*i.val+j.val))
theorem autoOk274 : autoGood autoExpr274 autoDfa274 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa273 autoDfa23 Bool.or) autoDfa274 autoSrc274 autoDst274 autoNext274
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk273 autoOk23)
  · rfl

def autoExpr275 : AutoF := .con autoExpr271 autoExpr274
def autoDfa275 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc275 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x2c688 3 i.val)
def autoDst275 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext275 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk275 : autoGood autoExpr275 autoDfa275 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa271 autoDfa274 Bool.and) autoDfa275 autoSrc275 autoDst275 autoNext275
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk271 autoOk274)
  · rfl

def autoExpr276 : AutoF := .disj autoExpr7 autoExpr275
def autoDfa276 : AutoM Nat := autoAlways
def autoSrc276 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x2c688 3 i.val)
def autoDst276 (i : Fin 6) : Nat := autoPacked 0x0 1 i.val
def autoNext276 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk276 : autoGood autoExpr276 autoDfa276 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa7 autoDfa275 Bool.or) autoDfa276 autoSrc276 autoDst276 autoNext276
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk7 autoOk275)
  · rfl

def autoExpr277 : AutoF := (.ge ⟨0,-1,1,1⟩)
def autoDfa277 : AutoM Nat := autoPackedTab 0x296a855a554155 2
def autoSrc277 (i : Fin 3) : AutoLit := (#[(.ge ⟨0,-1,1,1⟩),(.ge ⟨0,-1,1,0⟩),(.ge ⟨0,-1,1,-1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst277 (i : Fin 3) : Nat := autoPacked 0x24 2 i.val
def autoNext277 (i : Fin 3) (j : Fin 8) : Fin 3 := Fin.ofNat 3 (autoPacked 0xa5aa55a55055 2 (8*i.val+j.val))
theorem autoOk277 : autoGood autoExpr277 autoDfa277 0 := by
  apply autoTransfer (N := 2) autoAtom autoDfa277 autoSrc277 autoDst277 autoNext277
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨0,-1,1,1⟩))
  · rfl

def autoExpr278 : AutoF := .con autoExpr6 autoExpr277
def autoDfa278 : AutoM Nat := autoPackedTab 0x888888891888888880888988880764376760898889880888988891434376430898888880432176210435043210 4
def autoSrc278 (i : Fin 13) : Nat × Nat := (autoPacked 0x4b2c68b440 3 i.val, autoPacked 0x69a154 2 i.val)
def autoDst278 (i : Fin 13) : Nat := autoPacked 0x8988876543210 4 i.val
def autoNext278 (i : Fin 13) (j : Fin 8) : Fin 13 := Fin.ofNat 13 (autoPacked 0x88cc88888888aa8baa88aaaaaa88aaa98888aa88aa8baaa9764376768bcc8b88888baa8b434376438b88a9884321762143504321 4 (8*i.val+j.val))
theorem autoOk278 : autoGood autoExpr278 autoDfa278 0 := by
  apply autoTransfer (N := 12) (autoCombine autoDfa6 autoDfa277 Bool.and) autoDfa278 autoSrc278 autoDst278 autoNext278
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk277)
  · rfl

def autoExpr279 : AutoF := (.ge ⟨2,0,-1,-2⟩)
def autoDfa279 : AutoM Nat := autoPackedTab 0xeeee667b9999911264 2
def autoSrc279 (i : Fin 4) : AutoLit := (#[(.ge ⟨2,0,-1,-2⟩),(.ge ⟨2,0,-1,-1⟩),(.ge ⟨2,0,-1,0⟩),(.ge ⟨2,0,-1,1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst279 (i : Fin 4) : Nat := autoPacked 0xe4 2 i.val
def autoNext279 (i : Fin 4) (j : Fin 8) : Fin 4 := Fin.ofNat 4 (autoPacked 0xeeee99ee99994499 2 (8*i.val+j.val))
theorem autoOk279 : autoGood autoExpr279 autoDfa279 0 := by
  apply autoTransfer (N := 3) autoAtom autoDfa279 autoSrc279 autoDst279 autoNext279
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨2,0,-1,-2⟩))
  · rfl

def autoExpr280 : AutoF := .con autoExpr6 autoExpr279
def autoDfa280 : AutoM Nat := autoPackedTab 0x175d1c62db6db45b6db618e38e316db65a23463445d44688 3
def autoSrc280 (i : Fin 13) : Nat × Nat := (autoPacked 0x596468b440 3 i.val, autoPacked 0x16e4664 2 i.val)
def autoDst280 (i : Fin 13) : Nat := autoPacked 0x5b2dbac688 3 i.val
def autoNext280 (i : Fin 13) (j : Fin 8) : Fin 13 := Fin.ofNat 13 (autoPacked 0x8b8b8b8c8b8b8b8b8b8b989a989898988b8b98988b8c8b8c767643438c8b8c8b8b8c989a434343438c8b9a984321432176504321 4 (8*i.val+j.val))
theorem autoOk280 : autoGood autoExpr280 autoDfa280 0 := by
  apply autoTransfer (N := 12) (autoCombine autoDfa6 autoDfa279 Bool.and) autoDfa280 autoSrc280 autoDst280 autoNext280
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk279)
  · rfl

def autoExpr281 : AutoF := (.dis ⟨0,0,1,1⟩ ⟨0,1,0,-1⟩)
def autoDfa281 : AutoM Nat := autoPackedTab 0xff5a56aa955553c294 2
def autoSrc281 (i : Fin 4) : AutoLit := (#[(.dis ⟨0,0,1,1⟩ ⟨0,1,0,-1⟩),(.no),(.dis ⟨0,0,1,0⟩ ⟨0,1,0,0⟩),(.dis ⟨0,0,1,1⟩ ⟨0,1,0,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst281 (i : Fin 4) : Nat := autoPacked 0xe4 2 i.val
def autoNext281 (i : Fin 4) (j : Fin 8) : Fin 4 := Fin.ofNat 4 (autoPacked 0xff5a5aaa5555f0a5 2 (8*i.val+j.val))
theorem autoOk281 : autoGood autoExpr281 autoDfa281 0 := by
  apply autoTransfer (N := 3) autoAtom autoDfa281 autoSrc281 autoDst281 autoNext281
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.dis ⟨0,0,1,1⟩ ⟨0,1,0,-1⟩))
  · rfl

def autoExpr282 : AutoF := .con autoExpr6 autoExpr281
def autoDfa282 : AutoM Nat := autoPackedTab 0x49249c5d749681c49c4824e24e24b4d3409249243b03448 3
def autoSrc282 (i : Fin 17) : Nat × Nat := (autoPacked 0x4b25b1a68b440 3 i.val, autoPacked 0x3ca55f294 2 i.val)
def autoDst282 (i : Fin 17) : Nat := autoPacked 0x1c4e249763448 3 i.val
def autoNext282 (i : Fin 17) (j : Fin 8) : Fin 17 := Fin.ofNat 17 (autoPacked 0x84210529ad84210529ac841ce6b54a529ad6b5ad529ad6b5ac5294a5294b5294a5294a5294b5294b4a1284a1288420f529ac398e64a08383dce6b14a529ac6b5ac4a08320c8352d4a52d4a4a0414a041398a020c41 5 (8*i.val+j.val))
theorem autoOk282 : autoGood autoExpr282 autoDfa282 0 := by
  apply autoTransfer (N := 16) (autoCombine autoDfa6 autoDfa281 Bool.and) autoDfa282 autoSrc282 autoDst282 autoNext282
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk281)
  · rfl

def autoExpr283 : AutoF := .con autoExpr280 autoExpr282
def autoDfa283 : AutoM Nat := autoPackedTab 0x18612d024924b24b4d3409249241843448 3
def autoSrc283 (i : Fin 13) : Nat × Nat := (autoPacked 0x5963bac688 3 i.val, autoPacked 0x6c49763448 3 i.val)
def autoDst283 (i : Fin 13) : Nat := autoPacked 0x164930b448 3 i.val
def autoNext283 (i : Fin 13) (j : Fin 8) : Fin 13 := Fin.ofNat 13 (autoPacked 0xaaaaaaacaaaaaaabaaaaaaaaaaaaaaa998989898aaacaaac76769843acaaacaaaaacaaab98434343aaaaa9aa9821982176504321 4 (8*i.val+j.val))
theorem autoOk283 : autoGood autoExpr283 autoDfa283 0 := by
  apply autoTransfer (N := 12) (autoCombine autoDfa280 autoDfa282 Bool.and) autoDfa283 autoSrc283 autoDst283 autoNext283
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk280 autoOk282)
  · rfl

def autoExpr284 : AutoF := .con autoExpr278 autoExpr283
def autoDfa284 : AutoM Nat := autoPackedTab 0x968d3418612d024924b24b46b409249241843448 3
def autoSrc284 (i : Fin 17) : Nat × Nat := (autoPacked 0x89769837643543210 4 i.val, autoPacked 0x36d124930b448 3 i.val)
def autoDst284 (i : Fin 17) : Nat := autoPacked 0x166924930b448 3 i.val
def autoNext284 (i : Fin 17) (j : Fin 8) : Fin 17 := Fin.ofNat 17 (autoPacked 0x5ad6b5ad705ad6b5ad6f5ad6c5ad704a083735cd5ad6b5ad6c5ad6b5ad6b3a8ea4a0ea5ad6c5ad6b4a0ea4a1285ad6c5ad6c398e64a0835b16b5b16b5ad6c5ad6f3a883734835b16b5ad6b3a8414a041398a020c41 5 (8*i.val+j.val))
theorem autoOk284 : autoGood autoExpr284 autoDfa284 0 := by
  apply autoTransfer (N := 16) (autoCombine autoDfa278 autoDfa283 Bool.and) autoDfa284 autoSrc284 autoDst284 autoNext284
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk278 autoOk283)
  · rfl

def autoExpr285 : AutoF := (.ge ⟨-2,-1,1,1⟩)
def autoDfa285 : AutoM Nat := autoPackedTab 0x46d471869a8da0d22d341145a44a242289 3
def autoSrc285 (i : Fin 5) : AutoLit := (#[(.ge ⟨-2,-1,1,1⟩),(.ge ⟨-2,-1,1,0⟩),(.ge ⟨-2,-1,1,-1⟩),(.ge ⟨-2,-1,1,-2⟩),(.ge ⟨-2,-1,1,-3⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst285 (i : Fin 5) : Nat := autoPacked 0x4688 3 i.val
def autoNext285 (i : Fin 5) (j : Fin 8) : Fin 5 := Fin.ofNat 5 (autoPacked 0x8da8e369a8da69169a451691448451 3 (8*i.val+j.val))
theorem autoOk285 : autoGood autoExpr285 autoDfa285 0 := by
  apply autoTransfer (N := 4) autoAtom autoDfa285 autoSrc285 autoDst285 autoNext285
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨-2,-1,1,1⟩))
  · rfl

def autoExpr286 : AutoF := .con autoExpr6 autoExpr285
def autoDfa286 : AutoM Nat := autoPackedTab 0x4924972b46b2c174924824ba4908e35a3092492423456444744688 3
def autoSrc286 (i : Fin 14) : Nat × Nat := (autoPacked 0x2596468b440 3 i.val, autoPacked 0x2129a68a288 3 i.val)
def autoDst286 (i : Fin 14) : Nat := autoPacked 0x174925ac688 3 i.val
def autoNext286 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0xd998d9d98b8b988c8b8b988b988b989a9898d998988b9898989ad99a764376768c8b9a8b988c989a434376439a8b9a984321762143504321 4 (8*i.val+j.val))
theorem autoOk286 : autoGood autoExpr286 autoDfa286 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa6 autoDfa285 Bool.and) autoDfa286 autoSrc286 autoDst286 autoNext286
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk285)
  · rfl

def autoExpr287 : AutoF := (.ge ⟨4,0,-1,-2⟩)
def autoDfa287 : AutoM Nat := autoPackedTab 0x2aaaaa8c71d5514518e331c71c6514514430c2288 3
def autoSrc287 (i : Fin 6) : AutoLit := (#[(.ge ⟨4,0,-1,-2⟩),(.ge ⟨4,0,-1,-1⟩),(.ge ⟨4,0,-1,1⟩),(.ge ⟨4,0,-1,0⟩),(.ge ⟨4,0,-1,2⟩),(.ge ⟨4,0,-1,3⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst287 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext287 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0xaaaaaa8e3aaa4518e38e38e3451451618451 3 (8*i.val+j.val))
theorem autoOk287 : autoGood autoExpr287 autoDfa287 0 := by
  apply autoTransfer (N := 5) autoAtom autoDfa287 autoSrc287 autoDst287 autoNext287
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨4,0,-1,-2⟩))
  · rfl
