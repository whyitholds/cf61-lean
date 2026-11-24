import AutoCert0
import AutoCert4
import AutoCert8
import AutoCert11
import AutoCert12
import AutoCert13

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr200 : AutoF := .con autoExpr6 autoExpr199
def autoDfa200 : AutoM Nat := autoPackedTab 0x124924c758f5d449249208e3d63124934823475444704688 3
def autoSrc200 (i : Fin 13) : Nat × Nat := (autoPacked 0x4b2c68b440 3 i.val, autoPacked 0x69a154 2 i.val)
def autoDst200 (i : Fin 13) : Nat := autoPacked 0x4934d64688 3 i.val
def autoNext200 (i : Fin 13) (j : Fin 8) : Fin 13 := Fin.ofNat 13 (autoPacked 0x88cc88888888aa8baa88aaaaaa88aaa98888aa88aa8baaa9764376768bcc8b88888baa8b434376438b88a9884321762143504321 4 (8*i.val+j.val))
theorem autoOk200 : autoGood autoExpr200 autoDfa200 0 := by
  apply autoTransfer (N := 12) (autoCombine autoDfa6 autoDfa199 Bool.and) autoDfa200 autoSrc200 autoDst200 autoNext200
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk199)
  · rfl

def autoExpr201 : AutoF := .con autoExpr200 autoExpr149
def autoDfa201 : AutoM Nat := autoPackedTab 0x124924c648f5d44924920923d63124934823935444724688 3
def autoSrc201 (i : Fin 16) : Nat × Nat := (autoPacked 0xd5cc8eb04688 3 i.val, autoPacked 0x925b23523440 3 i.val)
def autoDst201 (i : Fin 16) : Nat := autoPacked 0x924d26b24688 3 i.val
def autoNext201 (i : Fin 16) (j : Fin 8) : Fin 16 := Fin.ofNat 16 (autoPacked 0x6666666ffe6dfefe6d6dfe6d6666666c6666666b66666f666da9fea9666c666bfe438787666666666d656da9666c666c6d4387436c666b6643a9872143654321 4 (8*i.val+j.val))
theorem autoOk201 : autoGood autoExpr201 autoDfa201 0 := by
  apply autoTransfer (N := 15) (autoCombine autoDfa200 autoDfa149 Bool.and) autoDfa201 autoSrc201 autoDst201 autoNext201
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk200 autoOk149)
  · rfl

def autoExpr202 : AutoF := .con autoExpr170 autoExpr201
def autoDfa202 : AutoM Nat := autoPackedTab 0x124924c648f5d44924920923d63124934823935444724688 3
def autoSrc202 (i : Fin 13) : Nat × Nat := (autoPacked 0x2b63443440 3 i.val, autoPacked 0x49a6b24688 3 i.val)
def autoDst202 (i : Fin 13) : Nat := autoPacked 0x49a6b24688 3 i.val
def autoNext202 (i : Fin 13) (j : Fin 8) : Fin 13 := Fin.ofNat 13 (autoPacked 0x4c4c4c4c9999999b9999999a99999999999b999a4c4387879b999b994c654c65999b999b4c4387439b999a994365872143654321 4 (8*i.val+j.val))
theorem autoOk202 : autoGood autoExpr202 autoDfa202 0 := by
  apply autoTransfer (N := 12) (autoCombine autoDfa170 autoDfa201 Bool.and) autoDfa202 autoSrc202 autoDst202 autoNext202
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk170 autoOk201)
  · rfl

def autoExpr203 : AutoF := .disj autoExpr198 autoExpr202
def autoDfa203 : AutoM Nat := autoPackedTab 0x124924c648f5d44924920923d63124934823935444724688 3
def autoSrc203 (i : Fin 7) : Nat × Nat := (autoPacked 0x0 1 i.val, autoPacked 0x1ac688 3 i.val)
def autoDst203 (i : Fin 7) : Nat := autoPacked 0x1ac688 3 i.val
def autoNext203 (i : Fin 7) (j : Fin 8) : Fin 7 := Fin.ofNat 7 (autoPacked 0x924926923d75924924923d639249a48e4d518e48d1 3 (8*i.val+j.val))
theorem autoOk203 : autoGood autoExpr203 autoDfa203 0 := by
  apply autoTransfer (N := 6) (autoCombine autoDfa198 autoDfa202 Bool.or) autoDfa203 autoSrc203 autoDst203 autoNext203
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk198 autoOk202)
  · rfl

def autoExpr204 : AutoF := .con autoExpr63 autoExpr203
def autoDfa204 : AutoM Nat := autoPackedTab 0x124924c648f5d44924920923d63124934823935444724688 3
def autoSrc204 (i : Fin 11) : Nat × Nat := (autoPacked 0x53503440 3 i.val, autoPacked 0x126b24688 3 i.val)
def autoDst204 (i : Fin 11) : Nat := autoPacked 0x126b24688 3 i.val
def autoNext204 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x6666646669694949666666686963878766666666696549a56666666469638743666668666365872163654321 4 (8*i.val+j.val))
theorem autoOk204 : autoGood autoExpr204 autoDfa204 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa63 autoDfa203 Bool.and) autoDfa204 autoSrc204 autoDst204 autoNext204
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk63 autoOk203)
  · rfl

def autoExpr205 : AutoF := .con autoExpr119 autoExpr184
def autoDfa205 : AutoM Nat := autoPackedTab 0x2492494c9249209259241234d3425924903523440 3
def autoSrc205 (i : Fin 11) : Nat × Nat := (autoPacked 0x15ab08688 3 i.val, autoPacked 0x124b24688 3 i.val)
def autoDst205 (i : Fin 11) : Nat := autoPacked 0x124b24688 3 i.val
def autoNext205 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x6666666a666a66669898989866666667666666666a6666669854985466676666983232326766666632543210 4 (8*i.val+j.val))
theorem autoOk205 : autoGood autoExpr205 autoDfa205 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa119 autoDfa184 Bool.and) autoDfa205 autoSrc205 autoDst205 autoNext205
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk119 autoOk184)
  · rfl

def autoExpr206 : AutoF := (.ge ⟨4,1,-1,-1⟩)
def autoDfa206 : AutoM Nat := autoPackedTab 0x2b86bacc30d70985a8612d10d345a6a1689043440 3
def autoSrc206 (i : Fin 6) : AutoLit := (#[(.ge ⟨4,1,-1,-1⟩),(.ge ⟨4,1,-1,1⟩),(.ge ⟨4,1,-1,0⟩),(.ge ⟨4,1,-1,2⟩),(.ge ⟨4,1,-1,3⟩),(.ge ⟨4,1,-1,4⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst206 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext206 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0xae1aeb861ae185a86168869a69a85a208688 3 (8*i.val+j.val))
theorem autoOk206 : autoGood autoExpr206 autoDfa206 0 := by
  apply autoTransfer (N := 5) autoAtom autoDfa206 autoSrc206 autoDst206 autoNext206
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨4,1,-1,-1⟩))
  · rfl

def autoExpr207 : AutoF := .con autoExpr6 autoExpr206
def autoDfa207 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc207 (i : Fin 14) : Nat × Nat := (autoPacked 0x2496591a688 3 i.val, autoPacked 0x282a1688688 3 i.val)
def autoDst207 (i : Fin 14) : Nat := autoPacked 0x2496591a688 3 i.val
def autoNext207 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0xd79bd7d7bcbc76bc76769b7676bc767a9b9bd79b76769b7a9b769b9b76bc7676767a9b7a545432549b7a9b98325432327a76987654103210 4 (8*i.val+j.val))
theorem autoOk207 : autoGood autoExpr207 autoDfa207 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa6 autoDfa206 Bool.and) autoDfa207 autoSrc207 autoDst207 autoNext207
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk206)
  · rfl

def autoExpr208 : AutoF := (.dis ⟨-4,0,1,0⟩ ⟨0,1,0,0⟩)
def autoDfa208 : AutoM Nat := autoPackedTab 0x12a69a4471a5482084a30924924128e38c2441041 3
def autoSrc208 (i : Fin 6) : AutoLit := (#[(.dis ⟨-4,0,1,0⟩ ⟨0,1,0,0⟩),(.dis ⟨-4,0,1,-2⟩ ⟨0,1,0,0⟩),(.no),(.dis ⟨-4,0,1,-1⟩ ⟨0,1,0,0⟩),(.dis ⟨-4,0,1,-3⟩ ⟨0,1,0,0⟩),(.dis ⟨-4,0,1,-4⟩ ⟨0,1,0,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst208 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext208 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x4a9a698e34a92084a34924924a38e3488208 3 (8*i.val+j.val))
theorem autoOk208 : autoGood autoExpr208 autoDfa208 0 := by
  apply autoTransfer (N := 5) autoAtom autoDfa208 autoSrc208 autoDst208 autoNext208
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.dis ⟨-4,0,1,0⟩ ⟨0,1,0,0⟩))
  · rfl

def autoExpr209 : AutoF := .con autoExpr6 autoExpr208
def autoDfa209 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc209 (i : Fin 14) : Nat × Nat := (autoPacked 0x2492d91a688 3 i.val, autoPacked 0x290938d2208 3 i.val)
def autoDst209 (i : Fin 14) : Nat := autoPacked 0x0 1 i.val
def autoNext209 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0xaadcdcdcaa767676aacbcbcbaaaaaaaaaaaaaaa9cbcbaa787676aadccbcbaa76aaa9aaa954545454aa78767854323232a976787654103210 4 (8*i.val+j.val))
theorem autoOk209 : autoGood autoExpr209 autoDfa209 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa6 autoDfa208 Bool.and) autoDfa209 autoSrc209 autoDst209 autoNext209
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk208)
  · rfl

def autoExpr210 : AutoF := .con autoExpr207 autoExpr209
def autoDfa210 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc210 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst210 (i : Fin 6) : Nat := autoPacked 0x0 1 i.val
def autoNext210 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk210 : autoGood autoExpr210 autoDfa210 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa207 autoDfa209 Bool.and) autoDfa210 autoSrc210 autoDst210 autoNext210
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk207 autoOk209)
  · rfl

def autoExpr211 : AutoF := .con autoExpr189 autoExpr210
def autoDfa211 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc211 (i : Fin 1) : Nat × Nat := (autoPacked 0x0 1 i.val, autoPacked 0x0 1 i.val)
def autoDst211 (i : Fin 1) : Nat := autoPacked 0x0 1 i.val
def autoNext211 (i : Fin 1) (j : Fin 8) : Fin 1 := Fin.ofNat 1 (autoPacked 0x0 1 (8*i.val+j.val))
theorem autoOk211 : autoGood autoExpr211 autoDfa211 0 := by
  apply autoTransfer (N := 0) (autoCombine autoDfa189 autoDfa210 Bool.and) autoDfa211 autoSrc211 autoDst211 autoNext211
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk189 autoOk210)
  · rfl

def autoExpr212 : AutoF := .disj autoExpr205 autoExpr211
def autoDfa212 : AutoM Nat := autoPackedTab 0x2492494c9249209259241234d3425924903523440 3
def autoSrc212 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst212 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext212 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592491a69a9649246a4688 3 (8*i.val+j.val))
theorem autoOk212 : autoGood autoExpr212 autoDfa212 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa205 autoDfa211 Bool.or) autoDfa212 autoSrc212 autoDst212 autoNext212
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk205 autoOk211)
  · rfl

def autoExpr213 : AutoF := .con autoExpr9 autoExpr212
def autoDfa213 : AutoM Nat := autoPackedTab 0x2492494c9249209259241234d3425924903523440 3
def autoSrc213 (i : Fin 14) : Nat × Nat := (autoPacked 0x3b357d60688 3 i.val, autoPacked 0x249258e4688 3 i.val)
def autoDst213 (i : Fin 14) : Nat := autoPacked 0x249258e4688 3 i.val
def autoNext213 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0x7777777d777d77777d777777777d777da9a9c9c977777778777777777778777d7d777d77a954c9b477787777a96232327877777762543210 4 (8*i.val+j.val))
theorem autoOk213 : autoGood autoExpr213 autoDfa213 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa9 autoDfa212 Bool.and) autoDfa213 autoSrc213 autoDst213 autoNext213
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk9 autoOk212)
  · rfl

def autoExpr214 : AutoF := .disj autoExpr204 autoExpr213
def autoDfa214 : AutoM Nat := autoPackedTab 0x555555581555855581554376760555555550555855550554376430585558550435576210435543210 4
def autoSrc214 (i : Fin 10) : Nat × Nat := (autoPacked 0x26d64688 3 i.val, autoPacked 0x2c6a3440 3 i.val)
def autoDst214 (i : Fin 10) : Nat := autoPacked 0x8876543210 4 i.val
def autoNext214 (i : Fin 10) (j : Fin 8) : Fin 10 := Fin.ofNat 10 (autoPacked 0x55555559555555585559555855437676555555555559555555437643595558554355762143554321 4 (8*i.val+j.val))
theorem autoOk214 : autoGood autoExpr214 autoDfa214 0 := by
  apply autoTransfer (N := 9) (autoCombine autoDfa204 autoDfa213 Bool.or) autoDfa214 autoSrc214 autoDst214 autoNext214
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk204 autoOk213)
  · rfl
