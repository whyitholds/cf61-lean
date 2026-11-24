import AutoCert0
import AutoCert6
import AutoCert11
import AutoCert12
import AutoCert19

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr288 : AutoF := .con autoExpr6 autoExpr287
def autoDfa288 : AutoM Nat := autoPackedTab 0x888888880888888871767643430888887880888788871434343430878887880432143210765043210 4
def autoSrc288 (i : Fin 15) : Nat × Nat := (autoPacked 0x12c96468b440 3 i.val, autoPacked 0x14a2e361a288 3 i.val)
def autoDst288 (i : Fin 15) : Nat := autoPacked 0x888878876543210 4 i.val
def autoNext288 (i : Fin 15) (j : Fin 8) : Fin 15 := Fin.ofNat 15 (autoPacked 0xececececcbcbcbcd98989898cbcbcbcbcbcb989a9898ececcbcb9898cbcd989a76764343cdcb9a98989a989a434343439a989a984321432176504321 4 (8*i.val+j.val))
theorem autoOk288 : autoGood autoExpr288 autoDfa288 0 := by
  apply autoTransfer (N := 14) (autoCombine autoDfa6 autoDfa287 Bool.and) autoDfa288 autoSrc288 autoDst288 autoNext288
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk287)
  · rfl

def autoExpr289 : AutoF := (.dis ⟨-2,0,1,1⟩ ⟨0,1,0,-1⟩)
def autoDfa289 : AutoM Nat := autoPackedTab 0x6bccc904e79e61554968b44b5e069a27304b4d3449249242b03448 3
def autoSrc289 (i : Fin 8) : AutoLit := (#[(.dis ⟨-2,0,1,1⟩ ⟨0,1,0,-1⟩),(.no),(.dis ⟨-2,0,1,0⟩ ⟨0,1,0,0⟩),(.dis ⟨-2,0,1,-1⟩ ⟨0,1,0,0⟩),(.dis ⟨-2,0,1,0⟩ ⟨0,1,0,-1⟩),(.dis ⟨-2,0,1,1⟩ ⟨0,1,0,0⟩),(.dis ⟨-2,0,1,-2⟩ ⟨0,1,0,0⟩),(.dis ⟨-2,0,1,-1⟩ ⟨0,1,0,-1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst289 (i : Fin 8) : Nat := autoPacked 0xfac688 3 i.val
def autoNext289 (i : Fin 8) (j : Fin 8) : Fin 8 := Fin.ofNat 8 (autoPacked 0x6bccc9273cf355525a6896bc69a27325a69a249249560689 3 (8*i.val+j.val))
theorem autoOk289 : autoGood autoExpr289 autoDfa289 0 := by
  apply autoTransfer (N := 7) autoAtom autoDfa289 autoSrc289 autoDst289 autoNext289
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.dis ⟨-2,0,1,1⟩ ⟨0,1,0,-1⟩))
  · rfl

def autoExpr290 : AutoF := .con autoExpr6 autoExpr289
def autoDfa290 : AutoM Nat := autoPackedTab 0x24924f249e49e75d49681e49e4824f24904b4d3409249246b03448 3
def autoSrc290 (i : Fin 19) : Nat × Nat := (autoPacked 0x124965b1a68b440 3 i.val, autoPacked 0x1e26b3249563448 3 i.val)
def autoDst290 (i : Fin 19) : Nat := autoPacked 0x493c9249d63448 3 i.val
def autoNext290 (i : Fin 19) (j : Fin 8) : Fin 19 := Fin.ofNat 19 (autoPacked 0x7c2516bd4a7c14a7c251529f07c1f07c1f0529af529f07c1ee529af6bdaf7c1f0529ac5294a5294b5294a5294a5294b5294b4a1284a128529ee7c1ee398e64a0837b94a7ba517c1ee529ac4a08320c8352d4a52d4a4a0414a041398a020c41 5 (8*i.val+j.val))
theorem autoOk290 : autoGood autoExpr290 autoDfa290 0 := by
  apply autoTransfer (N := 18) (autoCombine autoDfa6 autoDfa289 Bool.and) autoDfa290 autoSrc290 autoDst290 autoNext290
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk289)
  · rfl

def autoExpr291 : AutoF := .con autoExpr288 autoExpr290
def autoDfa291 : AutoM Nat := autoPackedTab 0x49249c75d49681249c4824e24904b4d3409249246b03448 3
def autoSrc291 (i : Fin 14) : Nat × Nat := (autoPacked 0x87784376543210 4 i.val, autoPacked 0x3f249d63448 3 i.val)
def autoDst291 (i : Fin 14) : Nat := autoPacked 0xe249d63448 3 i.val
def autoNext291 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0xaaaaaaadaaaaaaacaaaaaaabaaaaaaaaaaabaaab98989898aaadaaac76769843adaaacaaaaacaaab98434343abaaabaa9821982176504321 4 (8*i.val+j.val))
theorem autoOk291 : autoGood autoExpr291 autoDfa291 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa288 autoDfa290 Bool.and) autoDfa291 autoSrc291 autoDst291 autoNext291
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk288 autoOk290)
  · rfl

def autoExpr292 : AutoF := .con autoExpr286 autoExpr291
def autoDfa292 : AutoM Nat := autoPackedTab 0x49249c4968d3418612d024e24904b46b409249241843448 3
def autoSrc292 (i : Fin 16) : Nat × Nat := (autoPacked 0xebad1e8ec688 3 i.val, autoPacked 0x3b3449d63448 3 i.val)
def autoDst292 (i : Fin 16) : Nat := autoPacked 0x271a4930b448 3 i.val
def autoNext292 (i : Fin 16) (j : Fin 8) : Fin 16 := Fin.ofNat 16 (autoPacked 0x2222222f2222222e2222222d222e22222843cbcb222f2222a9a928a928a92828222f222e767628432f222e22222d2222a943cb4322222222a921282176504321 4 (8*i.val+j.val))
theorem autoOk292 : autoGood autoExpr292 autoDfa292 0 := by
  apply autoTransfer (N := 15) (autoCombine autoDfa286 autoDfa291 Bool.and) autoDfa292 autoSrc292 autoDst292 autoNext292
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk286 autoOk291)
  · rfl

def autoExpr293 : AutoF := (.ge ⟨-4,0,1,1⟩)
def autoDfa293 : AutoM Nat := autoPackedTab 0x2aaaaa8471d5504518e311c71c61145144b0c2289 3
def autoSrc293 (i : Fin 6) : AutoLit := (#[(.ge ⟨-4,0,1,1⟩),(.ge ⟨-4,0,1,0⟩),(.ge ⟨-4,0,1,-2⟩),(.ge ⟨-4,0,1,-1⟩),(.ge ⟨-4,0,1,-3⟩),(.ge ⟨-4,0,1,-4⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst293 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext293 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0xaaaaaa8e3aaa4518e38e38e3451451618451 3 (8*i.val+j.val))
theorem autoOk293 : autoGood autoExpr293 autoDfa293 0 := by
  apply autoTransfer (N := 5) autoAtom autoDfa293 autoSrc293 autoDst293 autoNext293
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨-4,0,1,1⟩))
  · rfl

def autoExpr294 : AutoF := .con autoExpr6 autoExpr293
def autoDfa294 : AutoM Nat := autoPackedTab 0x92493492692488e3249069249209249244681248 3
def autoSrc294 (i : Fin 15) : Nat × Nat := (autoPacked 0x12c96468b440 3 i.val, autoPacked 0x14a2e361a288 3 i.val)
def autoDst294 (i : Fin 15) : Nat := autoPacked 0x692498d1248 3 i.val
def autoNext294 (i : Fin 15) (j : Fin 8) : Fin 15 := Fin.ofNat 15 (autoPacked 0xececececcbcbcbcd98989898cbcbcbcbcbcb989a9898ececcbcb9898cbcd989a76764343cdcb9a98989a989a434343439a989a984321432176504321 4 (8*i.val+j.val))
theorem autoOk294 : autoGood autoExpr294 autoDfa294 0 := by
  apply autoTransfer (N := 14) (autoCombine autoDfa6 autoDfa293 Bool.and) autoDfa294 autoSrc294 autoDst294 autoNext294
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk293)
  · rfl

def autoExpr295 : AutoF := .con autoExpr181 autoExpr294
def autoDfa295 : AutoM Nat := autoPackedTab 0x92493492692488e3249069249209249244681248 3
def autoSrc295 (i : Fin 11) : Nat × Nat := (autoPacked 0x16c68b440 3 i.val, autoPacked 0x1498d1248 3 i.val)
def autoDst295 (i : Fin 11) : Nat := autoPacked 0x1498d1248 3 i.val
def autoNext295 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x8888888a8888888988888888888a8889767643438a8889888889888943434343898889884321432176504321 4 (8*i.val+j.val))
theorem autoOk295 : autoGood autoExpr295 autoDfa295 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa181 autoDfa294 Bool.and) autoDfa295 autoSrc295 autoDst295 autoNext295
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk181 autoOk294)
  · rfl

def autoExpr296 : AutoF := .con autoExpr295 autoExpr99
def autoDfa296 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc296 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst296 (i : Fin 6) : Nat := autoPacked 0x0 1 i.val
def autoNext296 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x24924d24d2498e32493492492492498d0249 3 (8*i.val+j.val))
theorem autoOk296 : autoGood autoExpr296 autoDfa296 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa295 autoDfa99 Bool.and) autoDfa296 autoSrc296 autoDst296 autoNext296
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk295 autoOk99)
  · rfl

def autoExpr297 : AutoF := .disj autoExpr292 autoExpr296
def autoDfa297 : AutoM Nat := autoPackedTab 0x49249c4968d3418612d024e24904b46b409249241843448 3
def autoSrc297 (i : Fin 7) : Nat × Nat := (autoPacked 0x1ac688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst297 (i : Fin 7) : Nat := autoPacked 0x1ac688 3 i.val
def autoNext297 (i : Fin 7) (j : Fin 8) : Fin 7 := Fin.ofNat 7 (autoPacked 0x24924e25a34d30c25a24e24925a35a249249308689 3 (8*i.val+j.val))
theorem autoOk297 : autoGood autoExpr297 autoDfa297 0 := by
  apply autoTransfer (N := 6) (autoCombine autoDfa292 autoDfa296 Bool.or) autoDfa297 autoSrc297 autoDst297 autoNext297
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk292 autoOk296)
  · rfl

def autoExpr298 : AutoF := .disj autoExpr284 autoExpr297
def autoDfa298 : AutoM Nat := autoPackedTab 0x49249c4968d3418612d024e24e24b46b409249241843448 3
def autoSrc298 (i : Fin 8) : Nat × Nat := (autoPacked 0x2ec688 3 i.val, autoPacked 0xc6c688 3 i.val)
def autoDst298 (i : Fin 8) : Nat := autoPacked 0xdac688 3 i.val
def autoNext298 (i : Fin 8) (j : Fin 8) : Fin 8 := Fin.ofNat 8 (autoPacked 0x24924f24924e25a34d30c25a24f24e25a35a249249308689 3 (8*i.val+j.val))
theorem autoOk298 : autoGood autoExpr298 autoDfa298 0 := by
  apply autoTransfer (N := 7) (autoCombine autoDfa284 autoDfa297 Bool.or) autoDfa298 autoSrc298 autoDst298 autoNext298
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk284 autoOk297)
  · rfl

def autoExpr299 : AutoF := .neg autoExpr298
def autoDfa299 : AutoM Nat := autoFlip autoDfa298
theorem autoOk299 : autoGood autoExpr299 autoDfa299 0 := (autoGoodNeg _ autoOk298)

def autoExpr300 : AutoF := .con autoExpr6 autoExpr299
def autoDfa300 : AutoM Nat := autoPackedTab 0x674369690444444481676767670444844481656567430444444440674369430484448440672167210652043210 4
def autoSrc300 (i : Fin 12) : Nat × Nat := (autoPacked 0xaac4d3440 3 i.val, autoPacked 0xd49263448 3 i.val)
def autoDst300 (i : Fin 12) : Nat := autoPacked 0x498476543210 4 i.val
def autoNext300 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0x8888888b67436a6a8888888988888888676767678889888965656743888b888b67436a43898889886721672165204321 4 (8*i.val+j.val))
theorem autoOk300 : autoGood autoExpr300 autoDfa300 0 := by
  apply autoTransfer (N := 11) (autoCombine autoDfa6 autoDfa299 Bool.and) autoDfa300 autoSrc300 autoDst300 autoNext300
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk299)
  · rfl

def autoExpr301 : AutoF := .con autoExpr164 autoExpr159
def autoDfa301 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc301 (i : Fin 1) : Nat × Nat := (autoPacked 0x0 1 i.val, autoPacked 0x0 1 i.val)
def autoDst301 (i : Fin 1) : Nat := autoPacked 0x0 1 i.val
def autoNext301 (i : Fin 1) (j : Fin 8) : Fin 1 := Fin.ofNat 1 (autoPacked 0x0 1 (8*i.val+j.val))
theorem autoOk301 : autoGood autoExpr301 autoDfa301 0 := by
  apply autoTransfer (N := 0) (autoCombine autoDfa164 autoDfa159 Bool.and) autoDfa301 autoSrc301 autoDst301 autoNext301
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk164 autoOk159)
  · rfl
