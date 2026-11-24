import AutoCert0
import AutoCert20
import AutoCert25

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr359 : AutoF := .disj autoExpr351 autoExpr358
def autoDfa359 : AutoM Nat := autoPackedTab 0x49249c4968d3418612d024e24e24b46b409249241843448 3
def autoSrc359 (i : Fin 13) : Nat × Nat := (autoPacked 0x1249761688 3 i.val, autoPacked 0xba98716543210 4 i.val)
def autoDst359 (i : Fin 13) : Nat := autoPacked 0x58d6d60688 3 i.val
def autoNext359 (i : Fin 13) (j : Fin 8) : Fin 13 := Fin.ofNat 13 (autoPacked 0x11a91c1c1b1b11a91118111811a91ca91111111811111117113216161b1511321b14a91111181117113216321111111115143211 4 (8*i.val+j.val))
theorem autoOk359 : autoGood autoExpr359 autoDfa359 0 := by
  apply autoTransfer (N := 12) (autoCombine autoDfa351 autoDfa358 Bool.or) autoDfa359 autoSrc359 autoDst359 autoNext359
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk351 autoOk358)
  · rfl

def autoExpr360 : AutoF := .disj autoExpr300 autoExpr359
def autoDfa360 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc360 (i : Fin 12) : Nat × Nat := (autoPacked 0x498476543210 4 i.val, autoPacked 0xd49263448 3 i.val)
def autoDst360 (i : Fin 12) : Nat := autoPacked 0xaac4d3440 3 i.val
def autoNext360 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0x8888888b67436a6a8888888988888888676767678889888965656743888b888b67436a43898889886721672165204321 4 (8*i.val+j.val))
theorem autoOk360 : autoGood autoExpr360 autoDfa360 0 := by
  apply autoTransfer (N := 11) (autoCombine autoDfa300 autoDfa359 Bool.or) autoDfa360 autoSrc360 autoDst360 autoNext360
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk300 autoOk359)
  · rfl

def autoExpr361 : AutoF := .neg autoExpr359
def autoDfa361 : AutoM Nat := autoFlip autoDfa359
theorem autoOk361 : autoGood autoExpr361 autoDfa361 0 := (autoGoodNeg _ autoOk359)

def autoExpr362 : AutoF := .con autoExpr6 autoExpr361
def autoDfa362 : AutoM Nat := autoPackedTab 0x674369690444444481676767670444844481656567430444444440674369430484448440672167210652043210 4
def autoSrc362 (i : Fin 12) : Nat × Nat := (autoPacked 0xaac4d3440 3 i.val, autoPacked 0xd49263448 3 i.val)
def autoDst362 (i : Fin 12) : Nat := autoPacked 0x498476543210 4 i.val
def autoNext362 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0x8888888b67436a6a8888888988888888676767678889888965656743888b888b67436a43898889886721672165204321 4 (8*i.val+j.val))
theorem autoOk362 : autoGood autoExpr362 autoDfa362 0 := by
  apply autoTransfer (N := 11) (autoCombine autoDfa6 autoDfa361 Bool.and) autoDfa362 autoSrc362 autoDst362 autoNext362
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk361)
  · rfl

def autoExpr363 : AutoF := .disj autoExpr362 autoExpr298
def autoDfa363 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc363 (i : Fin 12) : Nat × Nat := (autoPacked 0x498476543210 4 i.val, autoPacked 0xd49263448 3 i.val)
def autoDst363 (i : Fin 12) : Nat := autoPacked 0xaac4d3440 3 i.val
def autoNext363 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0x8888888b67436a6a8888888988888888676767678889888965656743888b888b67436a43898889886721672165204321 4 (8*i.val+j.val))
theorem autoOk363 : autoGood autoExpr363 autoDfa363 0 := by
  apply autoTransfer (N := 11) (autoCombine autoDfa362 autoDfa298 Bool.or) autoDfa363 autoSrc363 autoDst363 autoNext363
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk362 autoOk298)
  · rfl

def autoExpr364 : AutoF := .con autoExpr360 autoExpr363
def autoDfa364 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc364 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x2c688 3 i.val)
def autoDst364 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext364 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk364 : autoGood autoExpr364 autoDfa364 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa360 autoDfa363 Bool.and) autoDfa364 autoSrc364 autoDst364 autoNext364
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk360 autoOk363)
  · rfl

def autoExpr365 : AutoF := .disj autoExpr7 autoExpr364
def autoDfa365 : AutoM Nat := autoAlways
def autoSrc365 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x2c688 3 i.val)
def autoDst365 (i : Fin 6) : Nat := autoPacked 0x0 1 i.val
def autoNext365 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk365 : autoGood autoExpr365 autoDfa365 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa7 autoDfa364 Bool.or) autoDfa365 autoSrc365 autoDst365 autoNext365
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk7 autoOk364)
  · rfl
