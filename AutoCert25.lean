import AutoCert0
import AutoCert21
import AutoCert24

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr351 : AutoF := .con autoExpr303 autoExpr350
def autoDfa351 : AutoM Nat := autoPackedTab 0x968d3412612d024924b24b46b40924924184b448 3
def autoSrc351 (i : Fin 20) : Nat × Nat := (autoPacked 0x9248a3913523440 3 i.val, autoPacked 0x8c1ee6b08b5a928398a418820 5 i.val)
def autoDst351 (i : Fin 20) : Nat := autoPacked 0x24934924984b448 3 i.val
def autoNext351 (i : Fin 20) (j : Fin 8) : Fin 20 := Fin.ofNat 20 (autoPacked 0x83d7184e1384a1283d7183d7184d715ad6d5ad6d83e0f83e0f83c834390e5ad6b5ad6d5ad6b5ad6c5ad6b5ad6b83cca83cca83d09425095ad6d5ad6c84907424835b56b5b56b848c55c4ca5ad6b5ad6483c83438835b56b5b16b424ca4244141cc520c41 5 (8*i.val+j.val))
theorem autoOk351 : autoGood autoExpr351 autoDfa351 0 := by
  apply autoTransfer (N := 19) (autoCombine autoDfa303 autoDfa350 Bool.and) autoDfa351 autoSrc351 autoDst351 autoNext351
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk303 autoOk350)
  · rfl

def autoExpr352 : AutoF := .neg autoExpr303
def autoDfa352 : AutoM Nat := autoFlip autoDfa303
theorem autoOk352 : autoGood autoExpr352 autoDfa352 0 := (autoGoodNeg _ autoOk303)

def autoExpr353 : AutoF := .con autoExpr6 autoExpr352
def autoDfa353 : AutoM Nat := autoPackedTab 0x666766671989898980666666671666666660676667660985498540666766660983232320676666660325432100 4
def autoSrc353 (i : Fin 11) : Nat × Nat := (autoPacked 0xd5b08688 3 i.val, autoPacked 0x124724688 3 i.val)
def autoDst353 (i : Fin 11) : Nat := autoPacked 0x98766543210 4 i.val
def autoNext353 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x66686668a9a9a9a966666668666666676666666668666866a954a95466686667a93232326866676632543210 4 (8*i.val+j.val))
theorem autoOk353 : autoGood autoExpr353 autoDfa353 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa6 autoDfa352 Bool.and) autoDfa353 autoSrc353 autoDst353 autoNext353
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk352)
  · rfl

def autoExpr354 : AutoF := .con autoExpr306 autoExpr349
def autoDfa354 : AutoM Nat := autoPackedTab 0x222222281222387870222228220232287650222423230222387230222222220232223650242223210 4
def autoSrc354 (i : Fin 26) : Nat × Nat := (autoPacked 0x26b249ae8e6a8c724688 3 i.val, autoPacked 0x2649460e7b9ac6296851928398a418820 5 i.val)
def autoDst354 (i : Fin 26) : Nat := autoPacked 0x28722228722322365242223210 4 i.val
def autoNext354 (i : Fin 26) (j : Fin 8) : Fin 26 := Fin.ofNat 26 (autoPacked 0xa4df5a66997bdef7bdf8a4d0e95e57a5a96a4df5a4df5a65f57bde47bde4a4e93a4e937bde47bdf8a4c83946517bdef7bdf07bdef7bdefa4d0e95d0ea4ccda4ccd7bde47bdf0a4d0e95d8b791ef7e1ef438cd95d497bde47bdefa590762c83791ef791efa58c57d4cd7bdef7bde4a4c8394483791ef7c1ef438cd62d4941cc520c41 5 (8*i.val+j.val))
theorem autoOk354 : autoGood autoExpr354 autoDfa354 0 := by
  apply autoTransfer (N := 25) (autoCombine autoDfa306 autoDfa349 Bool.and) autoDfa354 autoSrc354 autoDst354 autoNext354
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk306 autoOk349)
  · rfl

def autoExpr355 : AutoF := .con autoExpr353 autoExpr354
def autoDfa355 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc355 (i : Fin 17) : Nat × Nat := (autoPacked 0x69832761025432100 4 i.val, autoPacked 0x82287226542223210 4 i.val)
def autoDst355 (i : Fin 17) : Nat := autoPacked 0x0 1 i.val
def autoNext355 (i : Fin 17) (j : Fin 8) : Fin 17 := Fin.ofNat 17 (autoPacked 0x5294a529505294b5294b7b9ee7b9ee5294b529507b8836b1ac5294a5294b5294a5294a52d4a5414a20cc56b1287b88720c8352d4a52d4a7b8c57b8c55294b5294a7b8836b08352d4a5294a20cc520d2821cc520c41 5 (8*i.val+j.val))
theorem autoOk355 : autoGood autoExpr355 autoDfa355 0 := by
  apply autoTransfer (N := 16) (autoCombine autoDfa353 autoDfa354 Bool.and) autoDfa355 autoSrc355 autoDst355 autoNext355
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk353 autoOk354)
  · rfl

def autoExpr356 : AutoF := .con autoExpr308 autoExpr347
def autoDfa356 : AutoM Nat := autoPackedTab 0x22cb2e2e02d2d22cb022272227122cb2ecb022432a2a02279287902279282802222222712d76284302d25cb22022272222022432a430222222220792228210762543210 4
def autoSrc356 (i : Fin 28) : Nat × Nat := (autoPacked 0xb7b4ba4b87a99358721436543210 4 i.val, autoPacked 0x83dcd620c632cc8328c851928398a418820 5 i.val)
def autoDst356 (i : Fin 28) : Nat := autoPacked 0xe8dcb7222a222922821762543210 4 i.val
def autoNext356 (i : Fin 28) (j : Fin 8) : Fin 28 := Fin.ofNat 28 (autoPacked 0xad317aeebbad10e9ea7aae6b9ad3177bdf67bdf6ad317aef177bdef7bdf67bdf17bdf1ad2b4ad2b47bdf17bdefad0839ca727bdef7bdf17bdef7bdf07bdef7bdefad10e9e90ead0cdad0cd7bdf17bdf0ad10e9e98b7c5ef7bdef438cd9e9497bdf17bdf6ae50762c837c5ef7c5efae4c5c5ccd7bdf67bdf1ad0839c8837c5ef7c1ef438cd62d4941cc520c41 5 (8*i.val+j.val))
theorem autoOk356 : autoGood autoExpr356 autoDfa356 0 := by
  apply autoTransfer (N := 27) (autoCombine autoDfa308 autoDfa347 Bool.and) autoDfa356 autoSrc356 autoDst356 autoNext356
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk308 autoOk347)
  · rfl

def autoExpr357 : AutoF := .con autoExpr353 autoExpr356
def autoDfa357 : AutoM Nat := autoPackedTab 0x11981b1b01a1a1198011171117111981b9801111111711132161601a15113201a1498110111711110113216320111111110151432110 4
def autoSrc357 (i : Fin 24) : Nat × Nat := (autoPacked 0x868987982762432325432100 4 i.val, autoPacked 0xe7dcb722a229228762543210 4 i.val)
def autoDst357 (i : Fin 24) : Nat := autoPacked 0xb1a987116111111151432110 4 i.val
def autoNext357 (i : Fin 24) (j : Fin 8) : Fin 24 := Fin.ofNat 24 (autoPacked 0x8c2938de376b5ad6b5b68d6358c2936b5b26b5b28c2938de936b5ad6b5b26b5ae6b5ae8c2308c2308c08353d4f6b5ad6b5ae6b5ad6b5ad8c10c5250c8c0cb8c0cb6b5ae6b5ad8c10c525496b5ae6b5b68d507524836b9ad6b9ad8d4c5a4ccb6b5b26b5ad8c08353c836b9ad6b5ad430cb5244141cc520c41 5 (8*i.val+j.val))
theorem autoOk357 : autoGood autoExpr357 autoDfa357 0 := by
  apply autoTransfer (N := 23) (autoCombine autoDfa353 autoDfa356 Bool.and) autoDfa357 autoSrc357 autoDst357 autoNext357
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk353 autoOk356)
  · rfl

def autoExpr358 : AutoF := .disj autoExpr355 autoExpr357
def autoDfa358 : AutoM Nat := autoPackedTab 0x11981b1b01a1a1198011171117111981b9801111111711132161601a15113201a1498110111711110113216320111111110151432110 4
def autoSrc358 (i : Fin 12) : Nat × Nat := (autoPacked 0x0 1 i.val, autoPacked 0xba9876543210 4 i.val)
def autoDst358 (i : Fin 12) : Nat := autoPacked 0xba9876543210 4 i.val
def autoNext358 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0x11981b1b1a1a11981117111711981b9811111117113216161a1511321a14981111171111113216321111111115143211 4 (8*i.val+j.val))
theorem autoOk358 : autoGood autoExpr358 autoDfa358 0 := by
  apply autoTransfer (N := 11) (autoCombine autoDfa355 autoDfa357 Bool.or) autoDfa358 autoSrc358 autoDst358 autoNext358
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk355 autoOk357)
  · rfl
