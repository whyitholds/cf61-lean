import AutoCert0

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr16 : AutoF := (.ge ⟨-3,0,1,0⟩)
def autoDfa16 : AutoM Nat := autoPackedTab 0xeedd1119866ee22111 2
def autoSrc16 (i : Fin 4) : AutoLit := (#[(.ge ⟨-3,0,1,0⟩),(.ge ⟨-3,0,1,-2⟩),(.ge ⟨-3,0,1,-1⟩),(.ge ⟨-3,0,1,-3⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst16 (i : Fin 4) : Nat := autoPacked 0xe4 2 i.val
def autoNext16 (i : Fin 4) (j : Fin 8) : Fin 4 := Fin.ofNat 4 (autoPacked 0xeedd446666ee8844 2 (8*i.val+j.val))
theorem autoOk16 : autoGood autoExpr16 autoDfa16 0 := by
  apply autoTransfer (N := 3) autoAtom autoDfa16 autoSrc16 autoDst16 autoNext16
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨-3,0,1,0⟩))
  · rfl

def autoExpr17 : AutoF := .con autoExpr6 autoExpr16
def autoDfa17 : AutoM Nat := autoPackedTab 0x92493492692483492491144514092492444c1440 3
def autoSrc17 (i : Fin 12) : Nat × Nat := (autoPacked 0xb25919688 3 i.val, autoPacked 0x6ea44 2 i.val)
def autoDst17 (i : Fin 12) : Nat := autoPacked 0xa49263288 3 i.val
def autoNext17 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0x6a6a9a9b6a6a9a9a969676769a9a9698767679799a9a96969a9b96989b9a989696987678525232329896787652403210 4 (8*i.val+j.val))
theorem autoOk17 : autoGood autoExpr17 autoDfa17 0 := by
  apply autoTransfer (N := 11) (autoCombine autoDfa6 autoDfa16 Bool.and) autoDfa17 autoSrc17 autoDst17 autoNext17
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk16)
  · rfl

def autoExpr18 : AutoF := (.ge ⟨3,1,-1,-1⟩)
def autoDfa18 : AutoM Nat := autoPackedTab 0x42cc70965a8592510d145a299689081440 3
def autoSrc18 (i : Fin 5) : AutoLit := (#[(.ge ⟨3,1,-1,-1⟩),(.ge ⟨3,1,-1,1⟩),(.ge ⟨3,1,-1,0⟩),(.ge ⟨3,1,-1,2⟩),(.ge ⟨3,1,-1,3⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst18 (i : Fin 5) : Nat := autoPacked 0x4688 3 i.val
def autoNext18 (i : Fin 5) (j : Fin 8) : Fin 5 := Fin.ofNat 5 (autoPacked 0x8598e165a85928868a68a65a210288 3 (8*i.val+j.val))
theorem autoOk18 : autoGood autoExpr18 autoDfa18 0 := by
  apply autoTransfer (N := 4) autoAtom autoDfa18 autoSrc18 autoDst18 autoNext18
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨3,1,-1,-1⟩))
  · rfl

def autoExpr19 : AutoF := .con autoExpr6 autoExpr18
def autoDfa19 : AutoM Nat := autoPackedTab 0x16db6dc6db6db439a34e0b6eb6e2d38d342eb6eb43843440 3
def autoSrc19 (i : Fin 16) : Nat × Nat := (autoPacked 0xb1c765911688 3 i.val, autoPacked 0x110689682288 3 i.val)
def autoDst19 (i : Fin 16) : Nat := autoPacked 0xb757aeb61688 3 i.val
def autoNext19 (i : Fin 16) (j : Fin 8) : Fin 16 := Fin.ofNat 16 (autoPacked 0x9c6c969fe979e7e9969f769a9c6c969c797ae978969c769a769679767696797a7976e979969c769635d532359a9c7a96769a797a3235b2327a96787635403210 4 (8*i.val+j.val))
theorem autoOk19 : autoGood autoExpr19 autoDfa19 0 := by
  apply autoTransfer (N := 15) (autoCombine autoDfa6 autoDfa18 Bool.and) autoDfa19 autoSrc19 autoDst19 autoNext19
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk18)
  · rfl

def autoExpr20 : AutoF := (.dis ⟨-3,0,1,0⟩ ⟨0,1,0,0⟩)
def autoDfa20 : AutoM Nat := autoPackedTab 0x271c50840828b09249240a2d38c34c2041 3
def autoSrc20 (i : Fin 5) : AutoLit := (#[(.dis ⟨-3,0,1,0⟩ ⟨0,1,0,0⟩),(.dis ⟨-3,0,1,-2⟩ ⟨0,1,0,0⟩),(.no),(.dis ⟨-3,0,1,-1⟩ ⟨0,1,0,0⟩),(.dis ⟨-3,0,1,-3⟩ ⟨0,1,0,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst20 (i : Fin 5) : Nat := autoPacked 0x4688 3 i.val
def autoNext20 (i : Fin 5) (j : Fin 8) : Fin 5 := Fin.ofNat 5 (autoPacked 0x4e38a140828b49249228b4e3698408 3 (8*i.val+j.val))
theorem autoOk20 : autoGood autoExpr20 autoDfa20 0 := by
  apply autoTransfer (N := 4) autoAtom autoDfa20 autoSrc20 autoDst20 autoNext20
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.dis ⟨-3,0,1,0⟩ ⟨0,1,0,0⟩))
  · rfl

def autoExpr21 : AutoF := .con autoExpr6 autoExpr20
def autoDfa21 : AutoM Nat := autoPackedTab 0x924934926924834924910c4514092492442c1440 3
def autoSrc21 (i : Fin 16) : Nat × Nat := (autoPacked 0xb1d92c8d1688 3 i.val, autoPacked 0xa29c6d3408 3 i.val)
def autoDst21 (i : Fin 16) : Nat := autoPacked 0xa4924930b288 3 i.val
def autoNext21 (i : Fin 16) (j : Fin 8) : Fin 16 := Fin.ofNat 16 (autoPacked 0x7a7eaebf7a7eaebebab9a789aaaaaaacbab7a787aaaaaaaaaebebab9a7878a8baebebab7aebfbab935353535afbebcb7aaacaaac656232d2bcb7a98765403210 4 (8*i.val+j.val))
theorem autoOk21 : autoGood autoExpr21 autoDfa21 0 := by
  apply autoTransfer (N := 15) (autoCombine autoDfa6 autoDfa20 Bool.and) autoDfa21 autoSrc21 autoDst21 autoNext21
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk20)
  · rfl

def autoExpr22 : AutoF := .con autoExpr19 autoExpr21
def autoDfa22 : AutoM Nat := autoPackedTab 0x49249c6134a34127124838924910ca514092492442c1440 3
def autoSrc22 (i : Fin 14) : Nat × Nat := (autoPacked 0x2eca6ae1688 3 i.val, autoPacked 0x2ca5130b288 3 i.val)
def autoDst22 (i : Fin 14) : Nat := autoPacked 0x9c6930b288 3 i.val
def autoNext22 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0x7777777d777d77787777777b3a353a3a65c932397777777877777777777b777835853a357b777877777877786a6932327877787765403210 4 (8*i.val+j.val))
theorem autoOk22 : autoGood autoExpr22 autoDfa22 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa19 autoDfa21 Bool.and) autoDfa22 autoSrc22 autoDst22 autoNext22
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk19 autoOk21)
  · rfl

def autoExpr23 : AutoF := .con autoExpr17 autoExpr22
def autoDfa23 : AutoM Nat := autoPackedTab 0x49249c6134a34127124838924910ca514092492442c1440 3
def autoSrc23 (i : Fin 10) : Nat × Nat := (autoPacked 0x2caa2688 3 i.val, autoPacked 0x9d61688 3 i.val)
def autoDst23 (i : Fin 10) : Nat := autoPacked 0x9d61688 3 i.val
def autoNext23 (i : Fin 10) (j : Fin 8) : Fin 10 := Fin.ofNat 10 (autoPacked 0x11111119111911111111111754861216111711118484141417111111545612121111111154301210 4 (8*i.val+j.val))
theorem autoOk23 : autoGood autoExpr23 autoDfa23 0 := by
  apply autoTransfer (N := 9) (autoCombine autoDfa17 autoDfa22 Bool.and) autoDfa23 autoSrc23 autoDst23 autoNext23
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk17 autoOk22)
  · rfl

def autoExpr24 : AutoF := .disj autoExpr15 autoExpr23
def autoDfa24 : AutoM Nat := autoPackedTab 0x311c1a1c0191111110313c1a1a011111119171981238011191119191961636019111911031b41a140111911110717812320111111110765432100 4
def autoSrc24 (i : Fin 15) : Nat × Nat := (autoPacked 0x4926aaa1688 3 i.val, autoPacked 0x17468d858288 3 i.val)
def autoDst24 (i : Fin 15) : Nat := autoPacked 0xc93ba9876543210 4 i.val
def autoNext24 (i : Fin 15) (j : Fin 8) : Fin 15 := Fin.ofNat 15 (autoPacked 0xc11e1a1e1111111d111d11111d111111c1ce1a1a1111111971981238111d1119919616361d111911c1b41a1411191111717812321111111176543210 4 (8*i.val+j.val))
theorem autoOk24 : autoGood autoExpr24 autoDfa24 0 := by
  apply autoTransfer (N := 14) (autoCombine autoDfa15 autoDfa23 Bool.or) autoDfa24 autoSrc24 autoDst24 autoNext24
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk15 autoOk23)
  · rfl

def autoExpr25 : AutoF := .neg autoExpr24
def autoDfa25 : AutoM Nat := autoFlip autoDfa24
theorem autoOk25 : autoGood autoExpr25 autoDfa25 0 := (autoGoodNeg _ autoOk24)

def autoExpr26 : AutoF := .con autoExpr6 autoExpr25
def autoDfa26 : AutoM Nat := autoPackedTab 0x397d7a7d0555355550555553550393d7a7a079797979059c872380555355531c9c67636055555555039b47a140555555531595872320535553550565432100 4
def autoSrc26 (i : Fin 18) : Nat × Nat := (autoPacked 0x132aa4ec688688 3 i.val, autoPacked 0xc9ba91811176543210 4 i.val)
def autoDst26 (i : Fin 18) : Nat := autoPacked 0xdcba59873556543210 4 i.val
def autoNext26 (i : Fin 18) (j : Fin 8) : Fin 18 := Fin.ofNat 18 (autoPacked 0x1b15153951421094210d43508425081b0715394e421084210d5314c5314c3b20b5086b4210942109421084210942108421084210d4210d832065186643508435081b1e4538244210d421093b0eb508624250842508398a418820 5 (8*i.val+j.val))
theorem autoOk26 : autoGood autoExpr26 autoDfa26 0 := by
  apply autoTransfer (N := 17) (autoCombine autoDfa6 autoDfa25 Bool.and) autoDfa26 autoSrc26 autoDst26 autoNext26
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk25)
  · rfl

def autoExpr27 : AutoF := (.ge ⟨0,0,-1,0⟩)
def autoDfa27 : AutoM Nat := autoPackedTab 0x3fde1 1
def autoSrc27 (i : Fin 2) : AutoLit := (#[(.ge ⟨0,0,-1,0⟩),(.ge ⟨0,0,-1,-1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst27 (i : Fin 2) : Nat := autoPacked 0x2 1 i.val
def autoNext27 (i : Fin 2) (j : Fin 8) : Fin 2 := Fin.ofNat 2 (autoPacked 0xfff0 1 (8*i.val+j.val))
theorem autoOk27 : autoGood autoExpr27 autoDfa27 0 := by
  apply autoTransfer (N := 1) autoAtom autoDfa27 autoSrc27 autoDst27 autoNext27
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨0,0,-1,0⟩))
  · rfl

def autoExpr28 : AutoF := .con autoExpr6 autoExpr27
def autoDfa28 : AutoM Nat := autoPackedTab 0x49249209249233248d3424923904923440 3
def autoSrc28 (i : Fin 12) : Nat × Nat := (autoPacked 0xb2c688688 3 i.val, autoPacked 0xcf0 1 i.val)
def autoDst28 (i : Fin 12) : Nat := autoPacked 0x91c924688 3 i.val
def autoNext28 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0xaaaaaaabaaaaaaaaaaaa8889aaaa8888aaabaaab76767676abaaabaa76547654aaab888976763232abaa898876543210 4 (8*i.val+j.val))
theorem autoOk28 : autoGood autoExpr28 autoDfa28 0 := by
  apply autoTransfer (N := 11) (autoCombine autoDfa6 autoDfa27 Bool.and) autoDfa28 autoSrc28 autoDst28 autoNext28
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk27)
  · rfl

def autoExpr29 : AutoF := (.ge ⟨1,0,1,-1⟩)
def autoDfa29 : AutoM Nat := autoPackedTab 0x3fff4 1
def autoSrc29 (i : Fin 3) : AutoLit := (#[(.ge ⟨1,0,1,-1⟩),(.ge ⟨1,0,1,0⟩),(.ge ⟨1,0,1,1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst29 (i : Fin 3) : Nat := autoPacked 0x6 1 i.val
def autoNext29 (i : Fin 3) (j : Fin 8) : Fin 3 := Fin.ofNat 3 (autoPacked 0xaa9999555544 2 (8*i.val+j.val))
theorem autoOk29 : autoGood autoExpr29 autoDfa29 0 := by
  apply autoTransfer (N := 2) autoAtom autoDfa29 autoSrc29 autoDst29 autoNext29
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨1,0,1,-1⟩))
  · rfl
