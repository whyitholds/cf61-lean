import AutoCert0
import AutoCert16
import AutoCert17

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr262 : AutoF := .con autoExpr251 autoExpr261
def autoDfa262 : AutoM Nat := autoPackedTab 0x49249c6134a34127124838924910ca514092492442c1440 3
def autoSrc262 (i : Fin 20) : Nat × Nat := (autoPacked 0xc993ba91811176543210 4 i.val, autoPacked 0x96381979283762543210 4 i.val)
def autoDst262 (i : Fin 20) : Nat := autoPacked 0xa74689a49858288 3 i.val
def autoNext262 (i : Fin 20) (j : Fin 8) : Fin 20 := Fin.ofNat 20 (autoPacked 0x8315353953421094210d421084211142111421094450842508832135394e421084210d5314c5314c3b24b5086b421094210942108421094210842108421114210d93246518664450843508831e4538244210d421093b0eb508624250842508398a418820 5 (8*i.val+j.val))
theorem autoOk262 : autoGood autoExpr262 autoDfa262 0 := by
  apply autoTransfer (N := 19) (autoCombine autoDfa251 autoDfa261 Bool.and) autoDfa262 autoSrc262 autoDst262 autoNext262
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk251 autoOk261)
  · rfl

def autoExpr263 : AutoF := .neg autoExpr251
def autoDfa263 : AutoM Nat := autoFlip autoDfa251
theorem autoOk263 : autoGood autoExpr263 autoDfa263 0 := (autoGoodNeg _ autoOk251)

def autoExpr264 : AutoF := .con autoExpr6 autoExpr263
def autoDfa264 : AutoM Nat := autoPackedTab 0x397d7a7d0555355550555553550393d7a7a079797979059c872380555355531c9c67636055555555039b47a140555555531595872320535553550565432100 4
def autoSrc264 (i : Fin 18) : Nat × Nat := (autoPacked 0x132aa4ec688688 3 i.val, autoPacked 0xc9ba91811176543210 4 i.val)
def autoDst264 (i : Fin 18) : Nat := autoPacked 0xdcba59873556543210 4 i.val
def autoNext264 (i : Fin 18) (j : Fin 8) : Fin 18 := Fin.ofNat 18 (autoPacked 0x1b15153951421094210d43508425081b0715394e421084210d5314c5314c3b20b5086b4210942109421084210942108421084210d4210d832065186643508435081b1e4538244210d421093b0eb508624250842508398a418820 5 (8*i.val+j.val))
theorem autoOk264 : autoGood autoExpr264 autoDfa264 0 := by
  apply autoTransfer (N := 17) (autoCombine autoDfa6 autoDfa263 Bool.and) autoDfa264 autoSrc264 autoDst264 autoNext264
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk263)
  · rfl

def autoExpr265 : AutoF := .con autoExpr253 autoExpr260
def autoDfa265 : AutoM Nat := autoPackedTab 0x926b4c1249254a4aa4904ab5a30924924134a6445694688 3
def autoSrc265 (i : Fin 16) : Nat × Nat := (autoPacked 0xb4926ab0b440 3 i.val, autoPacked 0x9ab4a98746543210 4 i.val)
def autoDst265 (i : Fin 16) : Nat := autoPacked 0x552496a94688 3 i.val
def autoNext265 (i : Fin 16) (j : Fin 8) : Fin 16 := Fin.ofNat 16 (autoPacked 0xaaaaaaafaaaaaaaecdcdcdcdaaabaaabaaaaaaabaaaaaaaaaaabaaaf9d93c848aaabaaaeabaaafaacd25cd25aaaeaaab9d73c843abaaabaa9365482173654321 4 (8*i.val+j.val))
theorem autoOk265 : autoGood autoExpr265 autoDfa265 0 := by
  apply autoTransfer (N := 15) (autoCombine autoDfa253 autoDfa260 Bool.and) autoDfa265 autoSrc265 autoDst265 autoNext265
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk253 autoOk260)
  · rfl

def autoExpr266 : AutoF := .con autoExpr264 autoExpr265
def autoDfa266 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc266 (i : Fin 20) : Nat × Nat := (autoPacked 0xdcc6ba98732565432100 4 i.val, autoPacked 0x4ae4934b5694688 3 i.val)
def autoDst266 (i : Fin 20) : Nat := autoPacked 0x0 1 i.val
def autoNext266 (i : Fin 20) (j : Fin 8) : Fin 20 := Fin.ofNat 20 (autoPacked 0x535735b973318ca318c6318ca318c8936475c090318c6328c6535535b96e5b56d5b56d3362c5a48c318ca318ca318c6318ca334cc5a489318c6318c8936275c087318c6318c6535e55b845318c8318ca3350c5a483328c6328c631cc52244141cc520c41 5 (8*i.val+j.val))
theorem autoOk266 : autoGood autoExpr266 autoDfa266 0 := by
  apply autoTransfer (N := 19) (autoCombine autoDfa264 autoDfa265 Bool.and) autoDfa266 autoSrc266 autoDst266 autoNext266
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk264 autoOk265)
  · rfl

def autoExpr267 : AutoF := .con autoExpr255 autoExpr258
def autoDfa267 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc267 (i : Fin 14) : Nat × Nat := (autoPacked 0x79876265432100 4 i.val, autoPacked 0x324b5512688 3 i.val)
def autoDst267 (i : Fin 14) : Nat := autoPacked 0x0 1 i.val
def autoNext267 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0xaaaaaaadbcbcbcbcaaa4aaa4aaaaaaaaaaa4aaad9c93b848aaa4aaaaa4aaadaabc25bc25aaaaaaa49c73b843a4aaa4aa9365482173654321 4 (8*i.val+j.val))
theorem autoOk267 : autoGood autoExpr267 autoDfa267 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa255 autoDfa258 Bool.and) autoDfa267 autoSrc267 autoDst267 autoNext267
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk255 autoOk258)
  · rfl

def autoExpr268 : AutoF := .con autoExpr264 autoExpr267
def autoDfa268 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc268 (i : Fin 14) : Nat × Nat := (autoPacked 0xdcba9876543210 4 i.val, autoPacked 0x0 1 i.val)
def autoDst268 (i : Fin 14) : Nat := autoPacked 0x0 1 i.val
def autoNext268 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0x397d7a7d5553555555555355393d7a7a7979797959c8723855535553c9c676365555555539b47a1455555553595872325355535556543210 4 (8*i.val+j.val))
theorem autoOk268 : autoGood autoExpr268 autoDfa268 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa264 autoDfa267 Bool.and) autoDfa268 autoSrc268 autoDst268 autoNext268
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk264 autoOk267)
  · rfl

def autoExpr269 : AutoF := .disj autoExpr266 autoExpr268
def autoDfa269 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc269 (i : Fin 1) : Nat × Nat := (autoPacked 0x0 1 i.val, autoPacked 0x0 1 i.val)
def autoDst269 (i : Fin 1) : Nat := autoPacked 0x0 1 i.val
def autoNext269 (i : Fin 1) (j : Fin 8) : Fin 1 := Fin.ofNat 1 (autoPacked 0x0 1 (8*i.val+j.val))
theorem autoOk269 : autoGood autoExpr269 autoDfa269 0 := by
  apply autoTransfer (N := 0) (autoCombine autoDfa266 autoDfa268 Bool.or) autoDfa269 autoSrc269 autoDst269 autoNext269
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk266 autoOk268)
  · rfl

def autoExpr270 : AutoF := .disj autoExpr262 autoExpr269
def autoDfa270 : AutoM Nat := autoPackedTab 0x49249c6134a34127124838924910ca514092492442c1440 3
def autoSrc270 (i : Fin 7) : Nat × Nat := (autoPacked 0x1ac688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst270 (i : Fin 7) : Nat := autoPacked 0x1ac688 3 i.val
def autoNext270 (i : Fin 7) (j : Fin 8) : Fin 7 := Fin.ofNat 7 (autoPacked 0x24924e84d28d24e24938924986528a249249858288 3 (8*i.val+j.val))
theorem autoOk270 : autoGood autoExpr270 autoDfa270 0 := by
  apply autoTransfer (N := 6) (autoCombine autoDfa262 autoDfa269 Bool.or) autoDfa270 autoSrc270 autoDst270 autoNext270
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk262 autoOk269)
  · rfl

def autoExpr271 : AutoF := .disj autoExpr238 autoExpr270
def autoDfa271 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc271 (i : Fin 11) : Nat × Nat := (autoPacked 0x78676543210 4 i.val, autoPacked 0x1a930b288 3 i.val)
def autoDst271 (i : Fin 11) : Nat := autoPacked 0x1558d1688 3 i.val
def autoNext271 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x7777777a653932397777777877777777777a7778353535357a77787777787778656932327877787765403210 4 (8*i.val+j.val))
theorem autoOk271 : autoGood autoExpr271 autoDfa271 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa238 autoDfa270 Bool.or) autoDfa271 autoSrc271 autoDst271 autoNext271
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk238 autoOk270)
  · rfl

def autoExpr272 : AutoF := .neg autoExpr270
def autoDfa272 : AutoM Nat := autoFlip autoDfa270
theorem autoOk272 : autoGood autoExpr272 autoDfa272 0 := (autoGoodNeg _ autoOk270)
