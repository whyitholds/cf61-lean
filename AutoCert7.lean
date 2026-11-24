import AutoCert0
import AutoCert4
import AutoCert5
import AutoCert6

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr104 : AutoF := .disj autoExpr76 autoExpr103
def autoDfa104 : AutoM Nat := autoPackedTab 0x66676d4d0666c6c8c066ab69ab0666866681666b69a9066666668166a76d4706666666606c668c6506668666606c87894306666686606b66a9610876543210 4
def autoSrc104 (i : Fin 16) : Nat × Nat := (autoPacked 0x926d7590c688 3 i.val, autoPacked 0xca98d184b440 3 i.val)
def autoDst104 (i : Fin 16) : Nat := autoPacked 0xad8cba9876543210 4 i.val
def autoNext104 (i : Fin 16) (j : Fin 8) : Fin 16 := Fin.ofNat 16 (autoPacked 0x666d666d66676e4e6666666d666c6c8c66fb69ab666d6668666b69a96666666866f76e47666666666c668c65666d66666c878943666668666b66a96187654321 4 (8*i.val+j.val))
theorem autoOk104 : autoGood autoExpr104 autoDfa104 0 := by
  apply autoTransfer (N := 15) (autoCombine autoDfa76 autoDfa103 Bool.or) autoDfa104 autoSrc104 autoDst104 autoNext104
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk76 autoOk103)
  · rfl

def autoExpr105 : AutoF := .neg autoExpr104
def autoDfa105 : AutoM Nat := autoFlip autoDfa104
theorem autoOk105 : autoGood autoExpr105 autoDfa105 0 := (autoGoodNeg _ autoOk104)

def autoExpr106 : AutoF := .con autoExpr6 autoExpr105
def autoDfa106 : AutoM Nat := autoPackedTab 0xd8360d836006c1a76bc8f0360d735c87014a5114a5102d8298d4a9806c0cb6c0cb0294a5294a501b06b1a95240a5288a529406c1476bc870288a5288a501ae32d0e3140a5294a528816b907424830288a5294a501ac32d4930408398a418820 5
def autoSrc106 (i : Fin 20) : Nat × Nat := (autoPacked 0x495b1a0d3443440 3 i.val, autoPacked 0x6dc6866b6a9876543210 4 i.val)
def autoDst106 (i : Fin 20) : Nat := autoPacked 0x83dc4529ac5a928398a418820 5 i.val
def autoNext106 (i : Fin 20) (j : Fin 8) : Fin 20 := Fin.ofNat 20 (autoPacked 0x6cdb36cdb36cda76c8926cdb16c511739ce739d0739ce739cf739ce739ce739d0739d06cd4c6a54c6cccb6cccb739cf739cf6cdac6a549739d0739cf6cd476c887741ce741ce6c4cb444c5739cf739d06c50742483741ce73dce6b0cb524c141cc520c41 5 (8*i.val+j.val))
theorem autoOk106 : autoGood autoExpr106 autoDfa106 0 := by
  apply autoTransfer (N := 19) (autoCombine autoDfa6 autoDfa105 Bool.and) autoDfa106 autoSrc106 autoDst106 autoNext106
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk105)
  · rfl

def autoExpr107 : AutoF := (.ge ⟨2,0,-1,-1⟩)
def autoDfa107 : AutoM Nat := autoPackedTab 0x26665449951110 2
def autoSrc107 (i : Fin 3) : AutoLit := (#[(.ge ⟨2,0,-1,-1⟩),(.ge ⟨2,0,-1,0⟩),(.ge ⟨2,0,-1,1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst107 (i : Fin 3) : Nat := autoPacked 0x24 2 i.val
def autoNext107 (i : Fin 3) (j : Fin 8) : Fin 3 := Fin.ofNat 3 (autoPacked 0x999944994444 2 (8*i.val+j.val))
theorem autoOk107 : autoGood autoExpr107 autoDfa107 0 := by
  apply autoTransfer (N := 2) autoAtom autoDfa107 autoSrc107 autoDst107 autoNext107
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨2,0,-1,-1⟩))
  · rfl

def autoExpr108 : AutoF := .con autoExpr6 autoExpr107
def autoDfa108 : AutoM Nat := autoPackedTab 0x49249209249232d34d3424923903443440 3
def autoSrc108 (i : Fin 9) : Nat × Nat := (autoPacked 0x5964688 3 i.val, autoPacked 0x1944 2 i.val)
def autoDst108 (i : Fin 9) : Nat := autoPacked 0x48e4688 3 i.val
def autoNext108 (i : Fin 9) (j : Fin 8) : Fin 9 := Fin.ofNat 9 (autoPacked 0x474747484747474747475456545454544747545447485456323232324847565432103210 4 (8*i.val+j.val))
theorem autoOk108 : autoGood autoExpr108 autoDfa108 0 := by
  apply autoTransfer (N := 8) (autoCombine autoDfa6 autoDfa107 Bool.and) autoDfa108 autoSrc108 autoDst108 autoNext108
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk107)
  · rfl

def autoExpr109 : AutoF := (.ge ⟨1,0,1,0⟩)
def autoDfa109 : AutoM Nat := autoAlways
def autoSrc109 (i : Fin 2) : AutoLit := (#[(.ge ⟨1,0,1,0⟩),(.ge ⟨1,0,1,1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst109 (i : Fin 2) : Nat := autoPacked 0x0 1 i.val
def autoNext109 (i : Fin 2) (j : Fin 8) : Fin 2 := Fin.ofNat 2 (autoPacked 0xfaa0 1 (8*i.val+j.val))
theorem autoOk109 : autoGood autoExpr109 autoDfa109 0 := by
  apply autoTransfer (N := 1) autoAtom autoDfa109 autoSrc109 autoDst109 autoNext109
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨1,0,1,0⟩))
  · rfl

def autoExpr110 : AutoF := .con autoExpr6 autoExpr109
def autoDfa110 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc110 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst110 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext110 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk110 : autoGood autoExpr110 autoDfa110 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa6 autoDfa109 Bool.and) autoDfa110 autoSrc110 autoDst110 autoNext110
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk109)
  · rfl

def autoExpr111 : AutoF := .con autoExpr110 autoExpr66
def autoDfa111 : AutoM Nat := autoPackedTab 0x1b6db74b6e39606db6db0db6eb61c6ec6436cb288 3
def autoSrc111 (i : Fin 13) : Nat × Nat := (autoPacked 0x5b0348b440 3 i.val, autoPacked 0x3add8db288 3 i.val)
def autoDst111 (i : Fin 13) : Nat := autoPacked 0x3add8db288 3 i.val
def autoNext111 (i : Fin 13) (j : Fin 8) : Fin 13 := Fin.ofNat 13 (autoPacked 0xaaaaaaacaaaaaaabaaaaaaaa46594659aaacaaab4647478746464646acaaacaaaaacaaac47468743acaaabaa4759875146514321 4 (8*i.val+j.val))
theorem autoOk111 : autoGood autoExpr111 autoDfa111 0 := by
  apply autoTransfer (N := 12) (autoCombine autoDfa110 autoDfa66 Bool.and) autoDfa111 autoSrc111 autoDst111 autoNext111
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk110 autoOk66)
  · rfl

def autoExpr112 : AutoF := (.ge ⟨1,1,-1,-2⟩)
def autoDfa112 : AutoM Nat := autoPackedTab 0xeafe6a7a995a915254 2
def autoSrc112 (i : Fin 4) : AutoLit := (#[(.ge ⟨1,1,-1,-2⟩),(.ge ⟨1,1,-1,-1⟩),(.ge ⟨1,1,-1,0⟩),(.ge ⟨1,1,-1,1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst112 (i : Fin 4) : Nat := autoPacked 0xe4 2 i.val
def autoNext112 (i : Fin 4) (j : Fin 8) : Fin 4 := Fin.ofNat 4 (autoPacked 0xeafea9ea95a95495 2 (8*i.val+j.val))
theorem autoOk112 : autoGood autoExpr112 autoDfa112 0 := by
  apply autoTransfer (N := 3) autoAtom autoDfa112 autoSrc112 autoDst112 autoNext112
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨1,1,-1,-2⟩))
  · rfl

def autoExpr113 : AutoF := .con autoExpr6 autoExpr112
def autoDfa113 : AutoM Nat := autoPackedTab 0x555455541474387470545554550555555550555555541435347430555554550432147610532043210 4
def autoSrc113 (i : Fin 14) : Nat × Nat := (autoPacked 0x1cb6445b440 3 i.val, autoPacked 0xf69a654 2 i.val)
def autoDst113 (i : Fin 14) : Nat := autoPacked 0x85545576543210 4 i.val
def autoNext113 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0xc99acccac999ccc99888999b9998c99a9998c999988899984743d7479a98ca99988b999b999bc99a435347439b889a984321476153204321 4 (8*i.val+j.val))
theorem autoOk113 : autoGood autoExpr113 autoDfa113 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa6 autoDfa112 Bool.and) autoDfa113 autoSrc113 autoDst113 autoNext113
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk112)
  · rfl

def autoExpr114 : AutoF := .con autoExpr113 autoExpr13
def autoDfa114 : AutoM Nat := autoPackedTab 0x92492c72cd5542492c90c93553092492433895442712688 3
def autoSrc114 (i : Fin 19) : Nat × Nat := (autoPacked 0x7845345417652043210 4 i.val, autoPacked 0x4ec49a51b0b440 3 i.val)
def autoDst114 (i : Fin 19) : Nat := autoPacked 0x96492caa512688 3 i.val
def autoNext114 (i : Fin 19) (j : Fin 8) : Fin 19 := Fin.ofNat 19 (autoPacked 0x6c9ae8c9b26318d6318d6318c631906318c6318f6b98e6c9ae6318c6318d6318c6318c6318f631906b84a6c90a5c9638a4896358c6358c6318f6318f63d8c6418c638456b84a6318f6318d5b8e36a4836318c6358c58cca2250138cc520c41 5 (8*i.val+j.val))
theorem autoOk114 : autoGood autoExpr114 autoDfa114 0 := by
  apply autoTransfer (N := 18) (autoCombine autoDfa113 autoDfa13 Bool.and) autoDfa114 autoSrc114 autoDst114 autoNext114
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk113 autoOk13)
  · rfl

def autoExpr115 : AutoF := .con autoExpr9 autoExpr114
def autoDfa115 : AutoM Nat := autoPackedTab 0x92492c72cd5542492c90c93553092492433895442712688 3
def autoSrc115 (i : Fin 15) : Nat × Nat := (autoPacked 0x1e2faab03440 3 i.val, autoPacked 0x1924b5512688 3 i.val)
def autoDst115 (i : Fin 15) : Nat := autoPacked 0x1924b5512688 3 i.val
def autoNext115 (i : Fin 15) (j : Fin 8) : Fin 15 := Fin.ofNat 15 (autoPacked 0xaaaaaaaeabaaabaa7c7c4c4caaaaaaabaaaaaaaaaaabaaae9c934848aaabaaababaaaeaa7cd54c25aaabaaaa9c734843abaaaaaa9365482173654321 4 (8*i.val+j.val))
theorem autoOk115 : autoGood autoExpr115 autoDfa115 0 := by
  apply autoTransfer (N := 14) (autoCombine autoDfa9 autoDfa114 Bool.and) autoDfa115 autoSrc115 autoDst115 autoNext115
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk9 autoOk114)
  · rfl

def autoExpr116 : AutoF := .disj autoExpr111 autoExpr115
def autoDfa116 : AutoM Nat := autoPackedTab 0x84864b4b0444a4a8a084494789044444448184894787084464b4604a448a4504444444408a4687430444448440892487410462543210 4
def autoSrc116 (i : Fin 14) : Nat × Nat := (autoPacked 0x1c72c6cb288 3 i.val, autoPacked 0x2acd5712688 3 i.val)
def autoDst116 (i : Fin 14) : Nat := autoPacked 0xba898762543210 4 i.val
def autoNext116 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0xb4b74d4d444c4c9c4444444bb44a489a44444449b4ba4898b4474d4744444b444c449c4544444444bc47984344444944ba64984147654321 4 (8*i.val+j.val))
theorem autoOk116 : autoGood autoExpr116 autoDfa116 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa111 autoDfa115 Bool.or) autoDfa116 autoSrc116 autoDst116 autoNext116
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk111 autoOk115)
  · rfl
