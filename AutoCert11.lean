import AutoCert0
import AutoCert7
import AutoCert10

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr147 : AutoF := .disj autoExpr7 autoExpr146
def autoDfa147 : AutoM Nat := autoAlways
def autoSrc147 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x2c688 3 i.val)
def autoDst147 (i : Fin 6) : Nat := autoPacked 0x0 1 i.val
def autoNext147 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk147 : autoGood autoExpr147 autoDfa147 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa7 autoDfa146 Bool.or) autoDfa147 autoSrc147 autoDst147 autoNext147
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk7 autoOk146)
  · rfl

def autoExpr148 : AutoF := (.dis ⟨0,0,1,0⟩ ⟨0,1,0,-1⟩)
def autoDfa148 : AutoM Nat := autoPackedTab 0x2aaa8a55556940 2
def autoSrc148 (i : Fin 3) : AutoLit := (#[(.dis ⟨0,0,1,0⟩ ⟨0,1,0,-1⟩),(.dis ⟨0,0,1,0⟩ ⟨0,1,0,0⟩),(.no)] : Array AutoLit)[i.val]?.getD default
def autoDst148 (i : Fin 3) : Nat := autoPacked 0x24 2 i.val
def autoNext148 (i : Fin 3) (j : Fin 8) : Fin 3 := Fin.ofNat 3 (autoPacked 0xaaaaa5555a50 2 (8*i.val+j.val))
theorem autoOk148 : autoGood autoExpr148 autoDfa148 0 := by
  apply autoTransfer (N := 2) autoAtom autoDfa148 autoSrc148 autoDst148 autoNext148
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.dis ⟨0,0,1,0⟩ ⟨0,1,0,-1⟩))
  · rfl

def autoExpr149 : AutoF := .con autoExpr6 autoExpr148
def autoDfa149 : AutoM Nat := autoPackedTab 0x2492494c9249209259253234d3425925903523440 3
def autoSrc149 (i : Fin 13) : Nat × Nat := (autoPacked 0x56a4b08688 3 i.val, autoPacked 0x2a94a50 2 i.val)
def autoDst149 (i : Fin 13) : Nat := autoPacked 0x4924b24688 3 i.val
def autoNext149 (i : Fin 13) (j : Fin 8) : Fin 13 := Fin.ofNat 13 (autoPacked 0x9999999c999c999cbabababa999999999988888899888887889988669c999c99ba54ba5499878887ba3232328799876632543210 4 (8*i.val+j.val))
theorem autoOk149 : autoGood autoExpr149 autoDfa149 0 := by
  apply autoTransfer (N := 12) (autoCombine autoDfa6 autoDfa148 Bool.and) autoDfa149 autoSrc149 autoDst149 autoNext149
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk148)
  · rfl

def autoExpr150 : AutoF := .con autoExpr108 autoExpr149
def autoDfa150 : AutoM Nat := autoPackedTab 0x49249209249233234d3424923903523440 3
def autoSrc150 (i : Fin 11) : Nat × Nat := (autoPacked 0xd4708688 3 i.val, autoPacked 0x125b24688 3 i.val)
def autoDst150 (i : Fin 11) : Nat := autoPacked 0x124724688 3 i.val
def autoNext150 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x6666666aa9a9a9a966666668666666676666666666666a66a954a95466686667a93232326866676632543210 4 (8*i.val+j.val))
theorem autoOk150 : autoGood autoExpr150 autoDfa150 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa108 autoDfa149 Bool.and) autoDfa150 autoSrc150 autoDst150 autoNext150
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk108 autoOk149)
  · rfl

def autoExpr151 : AutoF := .neg autoExpr150
def autoDfa151 : AutoM Nat := autoFlip autoDfa150
theorem autoOk151 : autoGood autoExpr151 autoDfa151 0 := (autoGoodNeg _ autoOk150)

def autoExpr152 : AutoF := .con autoExpr6 autoExpr151
def autoDfa152 : AutoM Nat := autoPackedTab 0x666766671989898980666666671666666660676667660985498540666766660983232320676666660325432100 4
def autoSrc152 (i : Fin 11) : Nat × Nat := (autoPacked 0xd5b08688 3 i.val, autoPacked 0x124724688 3 i.val)
def autoDst152 (i : Fin 11) : Nat := autoPacked 0x98766543210 4 i.val
def autoNext152 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x66686668a9a9a9a966666668666666676666666668666866a954a95466686667a93232326866676632543210 4 (8*i.val+j.val))
theorem autoOk152 : autoGood autoExpr152 autoDfa152 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa6 autoDfa151 Bool.and) autoDfa152 autoSrc152 autoDst152 autoNext152
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk151)
  · rfl

def autoExpr153 : AutoF := (.ge ⟨4,-1,1,1⟩)
def autoDfa153 : AutoM Nat := autoPackedTab 0x2aa98a8888882062a6182c308b05144444a2c2289 3
def autoSrc153 (i : Fin 6) : AutoLit := (#[(.ge ⟨4,-1,1,1⟩),(.ge ⟨4,-1,1,0⟩),(.ge ⟨4,-1,1,2⟩),(.ge ⟨4,-1,1,3⟩),(.ge ⟨4,-1,1,-1⟩),(.ge ⟨4,-1,1,4⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst153 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext153 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0xaaa62a11110462a618618458451111458451 3 (8*i.val+j.val))
theorem autoOk153 : autoGood autoExpr153 autoDfa153 0 := by
  apply autoTransfer (N := 5) autoAtom autoDfa153 autoSrc153 autoDst153 autoNext153
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨4,-1,1,1⟩))
  · rfl

def autoExpr154 : AutoF := .con autoExpr6 autoExpr153
def autoDfa154 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc154 (i : Fin 16) : Nat × Nat := (autoPacked 0x92596468b440 3 i.val, autoPacked 0x94845811a288 3 i.val)
def autoDst154 (i : Fin 16) : Nat := autoPacked 0x92596468b440 3 i.val
def autoNext154 (i : Fin 16) (j : Fin 8) : Fin 16 := Fin.ofNat 16 (autoPacked 0x8fbd8f8febeb98ebbdbd8fbdbd98bdba9898bd98bdbd8fba98eb9898bd98bdbdbd9cbdba764376769ceb9c98989cbd9c434376439c98ba984321762143504321 4 (8*i.val+j.val))
theorem autoOk154 : autoGood autoExpr154 autoDfa154 0 := by
  apply autoTransfer (N := 15) (autoCombine autoDfa6 autoDfa153 Bool.and) autoDfa154 autoSrc154 autoDst154 autoNext154
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk153)
  · rfl

def autoExpr155 : AutoF := (.ge ⟨-2,0,-1,-1⟩)
def autoDfa155 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc155 (i : Fin 3) : AutoLit := (#[(.ge ⟨-2,0,-1,-1⟩),(.ge ⟨-2,0,-1,-2⟩),(.ge ⟨-2,0,-1,-3⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst155 (i : Fin 3) : Nat := autoPacked 0x0 1 i.val
def autoNext155 (i : Fin 3) (j : Fin 8) : Fin 3 := Fin.ofNat 3 (autoPacked 0x999999444444 2 (8*i.val+j.val))
theorem autoOk155 : autoGood autoExpr155 autoDfa155 0 := by
  apply autoTransfer (N := 2) autoAtom autoDfa155 autoSrc155 autoDst155 autoNext155
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨-2,0,-1,-1⟩))
  · rfl

def autoExpr156 : AutoF := .con autoExpr6 autoExpr155
def autoDfa156 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc156 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst156 (i : Fin 6) : Nat := autoPacked 0x0 1 i.val
def autoNext156 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk156 : autoGood autoExpr156 autoDfa156 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa6 autoDfa155 Bool.and) autoDfa156 autoSrc156 autoDst156 autoNext156
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk155)
  · rfl

def autoExpr157 : AutoF := (.dis ⟨4,0,1,0⟩ ⟨0,1,0,-2⟩)
def autoDfa157 : AutoM Nat := autoPackedTab 0x33b5b5b51b533b5a20b5b533981989833541b5a298330987654330339898981335454541333333330983398760543354210332121210 4
def autoSrc157 (i : Fin 12) : AutoLit := (#[(.dis ⟨4,0,1,0⟩ ⟨0,1,0,-2⟩),(.dis ⟨4,0,1,0⟩ ⟨0,1,0,-1⟩),(.dis ⟨4,0,1,2⟩ ⟨0,1,0,-1⟩),(.no),(.dis ⟨4,0,1,0⟩ ⟨0,1,0,0⟩),(.dis ⟨4,0,1,2⟩ ⟨0,1,0,0⟩),(.dis ⟨4,0,1,1⟩ ⟨0,1,0,-1⟩),(.dis ⟨4,0,1,3⟩ ⟨0,1,0,-1⟩),(.dis ⟨4,0,1,1⟩ ⟨0,1,0,0⟩),(.dis ⟨4,0,1,3⟩ ⟨0,1,0,0⟩),(.dis ⟨4,0,1,4⟩ ⟨0,1,0,-1⟩),(.dis ⟨4,0,1,4⟩ ⟨0,1,0,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst157 (i : Fin 12) : Nat := autoPacked 0xba9876543210 4 i.val
def autoNext157 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0x33b5b5b5b533b5a2b5b5339898983354b5a2983398765433339898983354545433333333983398765433542133212121 4 (8*i.val+j.val))
theorem autoOk157 : autoGood autoExpr157 autoDfa157 0 := by
  apply autoTransfer (N := 11) autoAtom autoDfa157 autoSrc157 autoDst157 autoNext157
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.dis ⟨4,0,1,0⟩ ⟨0,1,0,-2⟩))
  · rfl

def autoExpr158 : AutoF := .con autoExpr6 autoExpr157
def autoDfa158 : AutoM Nat := autoPackedTab 0x924927324f24e64d75d44924920d64d6313c93c83593544488c688 3
def autoSrc158 (i : Fin 25) : Nat × Nat := (autoPacked 0x592496592c8434d3440 3 i.val, autoPacked 0x4ba2543863987633543321210 4 i.val)
def autoDst158 (i : Fin 25) : Nat := autoPacked 0x792492493c926b24688 3 i.val
def autoNext158 (i : Fin 25) (j : Fin 8) : Fin 25 := Fin.ofNat 25 (autoPacked 0x7be93a4e987bef4bd2f4bd1efbd2d5745ef7458b7bdd1745d17be93a4e937bdef7bdf2745d17be937458ba4df27bdef7bdefbd2f47bdd1745d17be98bd2d5745ef7458ba4def7c9ef7c9ef31549315497bdcd745cd3150741d077bdf27bdf2314c5314c5745f27459041cc541c83735ef7358b41d4941c413144120c41 5 (8*i.val+j.val))
theorem autoOk158 : autoGood autoExpr158 autoDfa158 0 := by
  apply autoTransfer (N := 24) (autoCombine autoDfa6 autoDfa157 Bool.and) autoDfa158 autoSrc158 autoDst158 autoNext158
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk157)
  · rfl

def autoExpr159 : AutoF := .con autoExpr156 autoExpr158
def autoDfa159 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc159 (i : Fin 8) : Nat × Nat := (autoPacked 0x0 1 i.val, autoPacked 0xfac688 3 i.val)
def autoDst159 (i : Fin 8) : Nat := autoPacked 0x0 1 i.val
def autoNext159 (i : Fin 8) (j : Fin 8) : Fin 8 := Fin.ofNat 8 (autoPacked 0x924927927927935d75924924d64d639e49e4d64d519118d1 3 (8*i.val+j.val))
theorem autoOk159 : autoGood autoExpr159 autoDfa159 0 := by
  apply autoTransfer (N := 7) (autoCombine autoDfa156 autoDfa158 Bool.and) autoDfa159 autoSrc159 autoDst159 autoNext159
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk156 autoOk158)
  · rfl

def autoExpr160 : AutoF := .con autoExpr154 autoExpr159
def autoDfa160 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc160 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst160 (i : Fin 6) : Nat := autoPacked 0x0 1 i.val
def autoNext160 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk160 : autoGood autoExpr160 autoDfa160 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa154 autoDfa159 Bool.and) autoDfa160 autoSrc160 autoDst160 autoNext160
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk154 autoOk159)
  · rfl

def autoExpr161 : AutoF := (.ge ⟨2,-1,1,1⟩)
def autoDfa161 : AutoM Nat := autoPackedTab 0x717722061117146045 2
def autoSrc161 (i : Fin 4) : AutoLit := (#[(.ge ⟨2,-1,1,1⟩),(.ge ⟨2,-1,1,0⟩),(.ge ⟨2,-1,1,2⟩),(.ge ⟨2,-1,1,-1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst161 (i : Fin 4) : Nat := autoPacked 0xe4 2 i.val
def autoNext161 (i : Fin 4) (j : Fin 8) : Fin 4 := Fin.ofNat 4 (autoPacked 0x7177881811711811 2 (8*i.val+j.val))
theorem autoOk161 : autoGood autoExpr161 autoDfa161 0 := by
  apply autoTransfer (N := 3) autoAtom autoDfa161 autoSrc161 autoDst161 autoNext161
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨2,-1,1,1⟩))
  · rfl

def autoExpr162 : AutoF := .con autoExpr6 autoExpr161
def autoDfa162 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc162 (i : Fin 14) : Nat × Nat := (autoPacked 0x2596468b440 3 i.val, autoPacked 0xc917844 2 i.val)
def autoDst162 (i : Fin 14) : Nat := autoPacked 0x2596468b440 3 i.val
def autoNext162 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0x8d988d8d98b9989ab9b998b998988d9a98b9989898988d98989a8d9a76437676bcb99ab998bc989a434376439ab99a984321762143504321 4 (8*i.val+j.val))
theorem autoOk162 : autoGood autoExpr162 autoDfa162 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa6 autoDfa161 Bool.and) autoDfa162 autoSrc162 autoDst162 autoNext162
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk161)
  · rfl

def autoExpr163 : AutoF := (.ge ⟨0,0,-1,-1⟩)
def autoDfa163 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc163 (i : Fin 1) : AutoLit := (#[(.ge ⟨0,0,-1,-1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst163 (i : Fin 1) : Nat := autoPacked 0x0 1 i.val
def autoNext163 (i : Fin 1) (j : Fin 8) : Fin 1 := Fin.ofNat 1 (autoPacked 0x0 1 (8*i.val+j.val))
theorem autoOk163 : autoGood autoExpr163 autoDfa163 0 := by
  apply autoTransfer (N := 0) autoAtom autoDfa163 autoSrc163 autoDst163 autoNext163
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨0,0,-1,-1⟩))
  · rfl
