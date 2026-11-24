import AutoCert0
import AutoCert1
import AutoCert4
import AutoCert11
import AutoCert15

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr228 : AutoF := .con autoExpr224 autoExpr227
def autoDfa228 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc228 (i : Fin 12) : Nat × Nat := (autoPacked 0xba9876543210 4 i.val, autoPacked 0x0 1 i.val)
def autoDst228 (i : Fin 12) : Nat := autoPacked 0x0 1 i.val
def autoNext228 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0x9b9b9b9b7777777a777a777a9b769898777777779b7698769b259b25777a77779b7698437a777a777625982176254321 4 (8*i.val+j.val))
theorem autoOk228 : autoGood autoExpr228 autoDfa228 0 := by
  apply autoTransfer (N := 11) (autoCombine autoDfa224 autoDfa227 Bool.and) autoDfa228 autoSrc228 autoDst228 autoNext228
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk224 autoOk227)
  · rfl

def autoExpr229 : AutoF := .disj autoExpr226 autoExpr228
def autoDfa229 : AutoM Nat := autoPackedTab 0x124924c648f5d44924920923d63124934823935444724688 3
def autoSrc229 (i : Fin 7) : Nat × Nat := (autoPacked 0x1ac688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst229 (i : Fin 7) : Nat := autoPacked 0x1ac688 3 i.val
def autoNext229 (i : Fin 7) (j : Fin 8) : Fin 7 := Fin.ofNat 7 (autoPacked 0x924926923d75924924923d639249a48e4d518e48d1 3 (8*i.val+j.val))
theorem autoOk229 : autoGood autoExpr229 autoDfa229 0 := by
  apply autoTransfer (N := 6) (autoCombine autoDfa226 autoDfa228 Bool.or) autoDfa229 autoSrc229 autoDst229 autoNext229
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk226 autoOk228)
  · rfl

def autoExpr230 : AutoF := .disj autoExpr222 autoExpr229
def autoDfa230 : AutoM Nat := autoPackedTab 0x49249209249233234d3424923903523440 3
def autoSrc230 (i : Fin 8) : Nat × Nat := (autoPacked 0x554688 3 i.val, autoPacked 0xd64688 3 i.val)
def autoDst230 (i : Fin 8) : Nat := autoPacked 0x6a3440 3 i.val
def autoNext230 (i : Fin 8) (j : Fin 8) : Fin 8 := Fin.ofNat 8 (autoPacked 0xb6db6fb63fbeb6db6db6db6cb63fa3b6dbed8edf918ed8d1 3 (8*i.val+j.val))
theorem autoOk230 : autoGood autoExpr230 autoDfa230 0 := by
  apply autoTransfer (N := 7) (autoCombine autoDfa222 autoDfa229 Bool.or) autoDfa230 autoSrc230 autoDst230 autoNext230
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk222 autoOk229)
  · rfl

def autoExpr231 : AutoF := .disj autoExpr152 autoExpr230
def autoDfa231 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc231 (i : Fin 11) : Nat × Nat := (autoPacked 0x98766543210 4 i.val, autoPacked 0x124724688 3 i.val)
def autoDst231 (i : Fin 11) : Nat := autoPacked 0xd5b08688 3 i.val
def autoNext231 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x66686668a9a9a9a966666668666666676666666668666866a954a95466686667a93232326866676632543210 4 (8*i.val+j.val))
theorem autoOk231 : autoGood autoExpr231 autoDfa231 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa152 autoDfa230 Bool.or) autoDfa231 autoSrc231 autoDst231 autoNext231
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk152 autoOk230)
  · rfl

def autoExpr232 : AutoF := .neg autoExpr230
def autoDfa232 : AutoM Nat := autoFlip autoDfa230
theorem autoOk232 : autoGood autoExpr232 autoDfa232 0 := (autoGoodNeg _ autoOk230)

def autoExpr233 : AutoF := .con autoExpr6 autoExpr232
def autoDfa233 : AutoM Nat := autoPackedTab 0x666766671989898980666666671666666660676667660985498540666766660983232320676666660325432100 4
def autoSrc233 (i : Fin 11) : Nat × Nat := (autoPacked 0xd5b08688 3 i.val, autoPacked 0x124724688 3 i.val)
def autoDst233 (i : Fin 11) : Nat := autoPacked 0x98766543210 4 i.val
def autoNext233 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x66686668a9a9a9a966666668666666676666666668666866a954a95466686667a93232326866676632543210 4 (8*i.val+j.val))
theorem autoOk233 : autoGood autoExpr233 autoDfa233 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa6 autoDfa232 Bool.and) autoDfa233 autoSrc233 autoDst233 autoNext233
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk232)
  · rfl

def autoExpr234 : AutoF := .disj autoExpr233 autoExpr150
def autoDfa234 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc234 (i : Fin 11) : Nat × Nat := (autoPacked 0x98766543210 4 i.val, autoPacked 0x124724688 3 i.val)
def autoDst234 (i : Fin 11) : Nat := autoPacked 0xd5b08688 3 i.val
def autoNext234 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x66686668a9a9a9a966666668666666676666666668666866a954a95466686667a93232326866676632543210 4 (8*i.val+j.val))
theorem autoOk234 : autoGood autoExpr234 autoDfa234 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa233 autoDfa150 Bool.or) autoDfa234 autoSrc234 autoDst234 autoNext234
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk233 autoOk150)
  · rfl

def autoExpr235 : AutoF := .con autoExpr231 autoExpr234
def autoDfa235 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc235 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x2c688 3 i.val)
def autoDst235 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext235 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk235 : autoGood autoExpr235 autoDfa235 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa231 autoDfa234 Bool.and) autoDfa235 autoSrc235 autoDst235 autoNext235
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk231 autoOk234)
  · rfl

def autoExpr236 : AutoF := .disj autoExpr7 autoExpr235
def autoDfa236 : AutoM Nat := autoAlways
def autoSrc236 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x2c688 3 i.val)
def autoDst236 (i : Fin 6) : Nat := autoPacked 0x0 1 i.val
def autoNext236 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk236 : autoGood autoExpr236 autoDfa236 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa7 autoDfa235 Bool.or) autoDfa236 autoSrc236 autoDst236 autoNext236
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk7 autoOk235)
  · rfl

def autoExpr237 : AutoF := .neg autoExpr23
def autoDfa237 : AutoM Nat := autoFlip autoDfa23
theorem autoOk237 : autoGood autoExpr237 autoDfa237 0 := (autoGoodNeg _ autoOk23)

def autoExpr238 : AutoF := .con autoExpr6 autoExpr237
def autoDfa238 : AutoM Nat := autoPackedTab 0x653832380777777770777777761353535350777776770777677761656832320767776770654032100 4
def autoSrc238 (i : Fin 11) : Nat × Nat := (autoPacked 0x1558d1688 3 i.val, autoPacked 0x1a930b288 3 i.val)
def autoDst238 (i : Fin 11) : Nat := autoPacked 0x78676543210 4 i.val
def autoNext238 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x7777777a653932397777777877777777777a7778353535357a77787777787778656932327877787765403210 4 (8*i.val+j.val))
theorem autoOk238 : autoGood autoExpr238 autoDfa238 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa6 autoDfa237 Bool.and) autoDfa238 autoSrc238 autoDst238 autoNext238
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk237)
  · rfl

def autoExpr239 : AutoF := (.ge ⟨3,0,1,0⟩)
def autoDfa239 : AutoM Nat := autoAlways
def autoSrc239 (i : Fin 4) : AutoLit := (#[(.ge ⟨3,0,1,0⟩),(.ge ⟨3,0,1,1⟩),(.ge ⟨3,0,1,2⟩),(.ge ⟨3,0,1,3⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst239 (i : Fin 4) : Nat := autoPacked 0x0 1 i.val
def autoNext239 (i : Fin 4) (j : Fin 8) : Fin 4 := Fin.ofNat 4 (autoPacked 0xeedddd9999888844 2 (8*i.val+j.val))
theorem autoOk239 : autoGood autoExpr239 autoDfa239 0 := by
  apply autoTransfer (N := 3) autoAtom autoDfa239 autoSrc239 autoDst239 autoNext239
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨3,0,1,0⟩))
  · rfl

def autoExpr240 : AutoF := .con autoExpr6 autoExpr239
def autoDfa240 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc240 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst240 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext240 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk240 : autoGood autoExpr240 autoDfa240 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa6 autoDfa239 Bool.and) autoDfa240 autoSrc240 autoDst240 autoNext240
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk239)
  · rfl

def autoExpr241 : AutoF := .con autoExpr240 autoExpr58
def autoDfa241 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc241 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst241 (i : Fin 6) : Nat := autoPacked 0x0 1 i.val
def autoNext241 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk241 : autoGood autoExpr241 autoDfa241 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa240 autoDfa58 Bool.and) autoDfa241 autoSrc241 autoDst241 autoNext241
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk240 autoOk58)
  · rfl

def autoExpr242 : AutoF := (.ge ⟨-1,1,-1,-2⟩)
def autoDfa242 : AutoM Nat := autoPackedTab 0x19699516504144 2
def autoSrc242 (i : Fin 3) : AutoLit := (#[(.ge ⟨-1,1,-1,-2⟩),(.ge ⟨-1,1,-1,-1⟩),(.ge ⟨-1,1,-1,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst242 (i : Fin 3) : Nat := autoPacked 0x24 2 i.val
def autoNext242 (i : Fin 3) (j : Fin 8) : Fin 3 := Fin.ofNat 3 (autoPacked 0x65a651651051 2 (8*i.val+j.val))
theorem autoOk242 : autoGood autoExpr242 autoDfa242 0 := by
  apply autoTransfer (N := 2) autoAtom autoDfa242 autoSrc242 autoDst242 autoNext242
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨-1,1,-1,-2⟩))
  · rfl

def autoExpr243 : AutoF := .con autoExpr6 autoExpr242
def autoDfa243 : AutoM Nat := autoPackedTab 0x92492c554f5542492c904d3553092492413455842682688 3
def autoSrc243 (i : Fin 15) : Nat × Nat := (autoPacked 0xed96445b440 3 i.val, autoPacked 0x28919144 2 i.val)
def autoDst243 (i : Fin 15) : Nat := autoPacked 0x1b2492b12688 3 i.val
def autoNext243 (i : Fin 15) (j : Fin 8) : Fin 15 := Fin.ofNat 15 (autoPacked 0x8b8abb8d8b88bb8d9899889a8b88bb8b88988b8a9899889888988b884743e7478a988d88989c889a889a8b8a435347439a998a984321476153204321 4 (8*i.val+j.val))
theorem autoOk243 : autoGood autoExpr243 autoDfa243 0 := by
  apply autoTransfer (N := 14) (autoCombine autoDfa6 autoDfa242 Bool.and) autoDfa243 autoSrc243 autoDst243 autoNext243
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk242)
  · rfl

def autoExpr244 : AutoF := (.dis ⟨1,0,1,0⟩ ⟨0,1,0,-1⟩)
def autoDfa244 : AutoM Nat := autoPackedTab 0x192431190b89910c4524492492444ca440 3
def autoSrc244 (i : Fin 5) : AutoLit := (#[(.dis ⟨1,0,1,0⟩ ⟨0,1,0,-1⟩),(.no),(.dis ⟨1,0,1,0⟩ ⟨0,1,0,0⟩),(.dis ⟨1,0,1,1⟩ ⟨0,1,0,-1⟩),(.dis ⟨1,0,1,1⟩ ⟨0,1,0,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst244 (i : Fin 5) : Nat := autoPacked 0x4688 3 i.val
def autoNext244 (i : Fin 5) (j : Fin 8) : Fin 5 := Fin.ofNat 5 (autoPacked 0x32486290b899862292249249899488 3 (8*i.val+j.val))
theorem autoOk244 : autoGood autoExpr244 autoDfa244 0 := by
  apply autoTransfer (N := 4) autoAtom autoDfa244 autoSrc244 autoDst244 autoNext244
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.dis ⟨1,0,1,0⟩ ⟨0,1,0,-1⟩))
  · rfl

def autoExpr245 : AutoF := .con autoExpr6 autoExpr244
def autoDfa245 : AutoM Nat := autoPackedTab 0x9249349a49a4824d24d2cb45340924924350b440 3
def autoSrc245 (i : Fin 16) : Nat × Nat := (autoPacked 0xb24a9d8c8688 3 i.val, autoPacked 0x8e2449319488 3 i.val)
def autoDst245 (i : Fin 16) : Nat := autoPacked 0xa49a492e1688 3 i.val
def autoNext245 (i : Fin 16) (j : Fin 8) : Fin 16 := Fin.ofNat 16 (autoPacked 0x7dddd7dbdd7edce77dddd7dcd7dc7cccd7dc7ccb9a9a9a9a7778777877777778777777777ddfd7dbdf7edbe79a149a14d7db7ccb6a6292327877787762543210 4 (8*i.val+j.val))
theorem autoOk245 : autoGood autoExpr245 autoDfa245 0 := by
  apply autoTransfer (N := 15) (autoCombine autoDfa6 autoDfa244 Bool.and) autoDfa245 autoSrc245 autoDst245 autoNext245
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk244)
  · rfl
