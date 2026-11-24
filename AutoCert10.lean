import AutoCert0
import AutoCert1
import AutoCert7
import AutoCert8
import AutoCert9

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr138 : AutoF := .con autoExpr106 autoExpr129
def autoDfa138 : AutoM Nat := autoPackedTab 0x222222291222922291828527270222922220822527250292229220826527230222222220854227210654223210 4
def autoSrc138 (i : Fin 23) : Nat × Nat := (autoPacked 0x414f235c85358b524c8398a418820 5 i.val, autoPacked 0x48ea4da4cb4a94876543210 4 i.val)
def autoDst138 (i : Fin 23) : Nat := autoPacked 0x22792222852272654223210 4 i.val
def autoNext138 (i : Fin 23) (j : Fin 8) : Fin 23 := Fin.ofNat 23 (autoPacked 0x95a5695a567bdeb7bdef759c7950947bdef7bdf37bde47bde495a51946117bde47bdeb7bdef7bdef7bdf37bdf375aad9296d9592c9592c7bdef7bdeb759cd9296a791ef791ef7bdf37bdef75aa7950877cdef7cdef9452c845257bdef7bde47450782883791ef7adef734cc5a92141cc520c41 5 (8*i.val+j.val))
theorem autoOk138 : autoGood autoExpr138 autoDfa138 0 := by
  apply autoTransfer (N := 22) (autoCombine autoDfa106 autoDfa129 Bool.and) autoDfa138 autoSrc138 autoDst138 autoNext138
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk106 autoOk129)
  · rfl

def autoExpr139 : AutoF := .con autoExpr135 autoExpr138
def autoDfa139 : AutoM Nat := autoPackedTab 0xa2a52b2b02222222a1822927290222a222a1828927270222a22220a2252b2502a222a220826927230222222220854227210654223210 4
def autoSrc139 (i : Fin 25) : Nat × Nat := (autoPacked 0x9dad7ac788ba9486476543210 4 i.val, autoPacked 0x9285792225222872654223210 4 i.val)
def autoDst139 (i : Fin 25) : Nat := autoPacked 0x22a5ba2229222872654223210 4 i.val
def autoNext139 (i : Fin 25) (j : Fin 8) : Fin 25 := Fin.ofNat 25 (autoPacked 0x6318c631986c097244976319863193b409525095b42d5250946318c631936318c6358c6c1b72449124090240905c08f2288f6318d6318c6318c6318d6318c6318c63193631935c16f2288a6358c6358c631936318db41b52508764d8c64d8c6c245245256318d6318d5c10f728836358c6318c59cc52292141cc520c41 5 (8*i.val+j.val))
theorem autoOk139 : autoGood autoExpr139 autoDfa139 0 := by
  apply autoTransfer (N := 24) (autoCombine autoDfa135 autoDfa138 Bool.and) autoDfa139 autoSrc139 autoDst139 autoNext139
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk135 autoOk138)
  · rfl

def autoExpr140 : AutoF := .disj autoExpr137 autoExpr139
def autoDfa140 : AutoM Nat := autoPackedTab 0x111111181618712370111811181818515350181118110111811110616712320111111110654132100 4
def autoSrc140 (i : Fin 14) : Nat × Nat := (autoPacked 0x32ad6ad4688 3 i.val, autoPacked 0xba298765423210 4 i.val)
def autoDst140 (i : Fin 14) : Nat := autoPacked 0x58876265432100 4 i.val
def autoNext140 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0xc2c62d4d2222222c2222222b92ba284a222c222c929a2848222c222bc2b62d462c222c22222b2222927a2843222222229652482176524321 4 (8*i.val+j.val))
theorem autoOk140 : autoGood autoExpr140 autoDfa140 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa137 autoDfa139 Bool.or) autoDfa140 autoSrc140 autoDst140 autoNext140
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk137 autoOk139)
  · rfl

def autoExpr141 : AutoF := .disj autoExpr133 autoExpr140
def autoDfa141 : AutoM Nat := autoPackedTab 0x311c1a1c0191111110313c1a1a011111119171981238011191119191961636019111911031b41a140111911110717812320111111110765432100 4
def autoSrc141 (i : Fin 15) : Nat × Nat := (autoPacked 0x1f58c924a248 3 i.val, autoPacked 0x111118765413210 4 i.val)
def autoDst141 (i : Fin 15) : Nat := autoPacked 0x9c3ba9876543210 4 i.val
def autoNext141 (i : Fin 15) (j : Fin 8) : Fin 15 := Fin.ofNat 15 (autoPacked 0x1111111ec11d1a1d111e11111e111111c1cd1a1a1111111971981238111911199196163619111911c1b41a1411191111717812321111111176543210 4 (8*i.val+j.val))
theorem autoOk141 : autoGood autoExpr141 autoDfa141 0 := by
  apply autoTransfer (N := 14) (autoCombine autoDfa133 autoDfa140 Bool.or) autoDfa141 autoSrc141 autoDst141 autoNext141
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk133 autoOk140)
  · rfl

def autoExpr142 : AutoF := .disj autoExpr26 autoExpr141
def autoDfa142 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc142 (i : Fin 18) : Nat × Nat := (autoPacked 0xdcba59873556543210 4 i.val, autoPacked 0xc9ba91811176543210 4 i.val)
def autoDst142 (i : Fin 18) : Nat := autoPacked 0x132aa4ec688688 3 i.val
def autoNext142 (i : Fin 18) (j : Fin 8) : Fin 18 := Fin.ofNat 18 (autoPacked 0x1b15153951421094210d43508425081b0715394e421084210d5314c5314c3b20b5086b4210942109421084210942108421084210d4210d832065186643508435081b1e4538244210d421093b0eb508624250842508398a418820 5 (8*i.val+j.val))
theorem autoOk142 : autoGood autoExpr142 autoDfa142 0 := by
  apply autoTransfer (N := 17) (autoCombine autoDfa26 autoDfa141 Bool.or) autoDfa142 autoSrc142 autoDst142 autoNext142
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk26 autoOk141)
  · rfl

def autoExpr143 : AutoF := .neg autoExpr141
def autoDfa143 : AutoM Nat := autoFlip autoDfa141
theorem autoOk143 : autoGood autoExpr143 autoDfa143 0 := (autoGoodNeg _ autoOk141)

def autoExpr144 : AutoF := .con autoExpr6 autoExpr143
def autoDfa144 : AutoM Nat := autoPackedTab 0x397d7a7d0555355550555553550393d7a7a079797979059c872380555355531c9c67636055555555039b47a140555555531595872320535553550565432100 4
def autoSrc144 (i : Fin 18) : Nat × Nat := (autoPacked 0x132aa4ec688688 3 i.val, autoPacked 0xc9ba91811176543210 4 i.val)
def autoDst144 (i : Fin 18) : Nat := autoPacked 0xdcba59873556543210 4 i.val
def autoNext144 (i : Fin 18) (j : Fin 8) : Fin 18 := Fin.ofNat 18 (autoPacked 0x1b15153951421094210d43508425081b0715394e421084210d5314c5314c3b20b5086b4210942109421084210942108421084210d4210d832065186643508435081b1e4538244210d421093b0eb508624250842508398a418820 5 (8*i.val+j.val))
theorem autoOk144 : autoGood autoExpr144 autoDfa144 0 := by
  apply autoTransfer (N := 17) (autoCombine autoDfa6 autoDfa143 Bool.and) autoDfa144 autoSrc144 autoDst144 autoNext144
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk143)
  · rfl

def autoExpr145 : AutoF := .disj autoExpr144 autoExpr24
def autoDfa145 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc145 (i : Fin 18) : Nat × Nat := (autoPacked 0xdcba59873556543210 4 i.val, autoPacked 0xc9ba91811176543210 4 i.val)
def autoDst145 (i : Fin 18) : Nat := autoPacked 0x132aa4ec688688 3 i.val
def autoNext145 (i : Fin 18) (j : Fin 8) : Fin 18 := Fin.ofNat 18 (autoPacked 0x1b15153951421094210d43508425081b0715394e421084210d5314c5314c3b20b5086b4210942109421084210942108421084210d4210d832065186643508435081b1e4538244210d421093b0eb508624250842508398a418820 5 (8*i.val+j.val))
theorem autoOk145 : autoGood autoExpr145 autoDfa145 0 := by
  apply autoTransfer (N := 17) (autoCombine autoDfa144 autoDfa24 Bool.or) autoDfa145 autoSrc145 autoDst145 autoNext145
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk144 autoOk24)
  · rfl

def autoExpr146 : AutoF := .con autoExpr142 autoExpr145
def autoDfa146 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc146 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x2c688 3 i.val)
def autoDst146 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext146 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk146 : autoGood autoExpr146 autoDfa146 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa142 autoDfa145 Bool.and) autoDfa146 autoSrc146 autoDst146 autoNext146
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk142 autoOk145)
  · rfl
