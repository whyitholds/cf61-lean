import AutoCert0
import AutoCert2
import AutoCert6
import AutoCert12

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr182 : AutoF := (.dis ⟨-2,0,1,0⟩ ⟨0,1,0,-1⟩)
def autoDfa182 : AutoM Nat := autoPackedTab 0x24aebac492492069a92b1234d345a22b903523440 3
def autoSrc182 (i : Fin 6) : AutoLit := (#[(.dis ⟨-2,0,1,0⟩ ⟨0,1,0,-1⟩),(.dis ⟨-2,0,1,-1⟩ ⟨0,1,0,-1⟩),(.dis ⟨-2,0,1,0⟩ ⟨0,1,0,0⟩),(.dis ⟨-2,0,1,-1⟩ ⟨0,1,0,0⟩),(.no),(.dis ⟨-2,0,1,-2⟩ ⟨0,1,0,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst182 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext182 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92baeb92492469a92b91a69a688ae46a4688 3 (8*i.val+j.val))
theorem autoOk182 : autoGood autoExpr182 autoDfa182 0 := by
  apply autoTransfer (N := 5) autoAtom autoDfa182 autoSrc182 autoDst182 autoNext182
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.dis ⟨-2,0,1,0⟩ ⟨0,1,0,-1⟩))
  · rfl

def autoExpr183 : AutoF := .con autoExpr6 autoExpr182
def autoDfa183 : AutoM Nat := autoPackedTab 0x2492494c9249209259241234d3425924903523440 3
def autoSrc183 (i : Fin 17) : Nat × Nat := (autoPacked 0x58d4b24b08688 3 i.val, autoPacked 0x4523445724688 3 i.val)
def autoDst183 (i : Fin 17) : Nat := autoPacked 0x4924b24924688 3 i.val
def autoNext183 (i : Fin 17) (j : Fin 8) : Fin 17 := Fin.ofNat 17 (autoPacked 0x318c6318d03198f63d8f318d0318d0735cd735cd63d8f3190c3198f63d8b63d49430c663cc663d493190c4310c63d8f31907318c6318c6340c6340c6734a4734a463d8b31907734621886262d4941cc6188a418820 5 (8*i.val+j.val))
theorem autoOk183 : autoGood autoExpr183 autoDfa183 0 := by
  apply autoTransfer (N := 16) (autoCombine autoDfa6 autoDfa182 Bool.and) autoDfa183 autoSrc183 autoDst183 autoNext183
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk182)
  · rfl

def autoExpr184 : AutoF := .con autoExpr181 autoExpr183
def autoDfa184 : AutoM Nat := autoPackedTab 0x2492494c9249209259241234d3425924903523440 3
def autoSrc184 (i : Fin 11) : Nat × Nat := (autoPacked 0xd5b08688 3 i.val, autoPacked 0x125924688 3 i.val)
def autoDst184 (i : Fin 11) : Nat := autoPacked 0x125924688 3 i.val
def autoNext184 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x66676667a9a9a9a966666668666666676666666667666766a954a95466686667a93232326866676632543210 4 (8*i.val+j.val))
theorem autoOk184 : autoGood autoExpr184 autoDfa184 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa181 autoDfa183 Bool.and) autoDfa184 autoSrc184 autoDst184 autoNext184
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk181 autoOk183)
  · rfl

def autoExpr185 : AutoF := .con autoExpr180 autoExpr184
def autoDfa185 : AutoM Nat := autoPackedTab 0x92493492692482632a304c651409249244649440 3
def autoSrc185 (i : Fin 14) : Nat × Nat := (autoPacked 0x2d8d18c8288 3 i.val, autoPacked 0x259256a4688 3 i.val)
def autoDst185 (i : Fin 14) : Nat := autoPacked 0xd2498c9288 3 i.val
def autoNext185 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0x5555555d5555555c555d5555baba59ba59ba595955555558555c5555ba76327655555555ba54595455585555597632325855555576543210 4 (8*i.val+j.val))
theorem autoOk185 : autoGood autoExpr185 autoDfa185 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa180 autoDfa184 Bool.and) autoDfa185 autoSrc185 autoDst185 autoNext185
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk180 autoOk184)
  · rfl

def autoExpr186 : AutoF := (.ge ⟨4,0,-1,0⟩)
def autoDfa186 : AutoM Nat := autoPackedTab 0x471c7192082082d34d34082238cb4d1041 3
def autoSrc186 (i : Fin 5) : AutoLit := (#[(.ge ⟨4,0,-1,0⟩),(.ge ⟨4,0,-1,2⟩),(.ge ⟨4,0,-1,-1⟩),(.ge ⟨4,0,-1,1⟩),(.ge ⟨4,0,-1,3⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst186 (i : Fin 5) : Nat := autoPacked 0x4688 3 i.val
def autoNext186 (i : Fin 5) (j : Fin 8) : Fin 5 := Fin.ofNat 5 (autoPacked 0x8e38e320820869a69a2088e369a208 3 (8*i.val+j.val))
theorem autoOk186 : autoGood autoExpr186 autoDfa186 0 := by
  apply autoTransfer (N := 4) autoAtom autoDfa186 autoSrc186 autoDst186 autoNext186
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨4,0,-1,0⟩))
  · rfl

def autoExpr187 : AutoF := .con autoExpr6 autoExpr186
def autoDfa187 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc187 (i : Fin 15) : Nat × Nat := (autoPacked 0x12c964688688 3 i.val, autoPacked 0x810e369a208 3 i.val)
def autoDst187 (i : Fin 15) : Nat := autoPacked 0x12c964688688 3 i.val
def autoNext187 (i : Fin 15) (j : Fin 8) : Fin 15 := Fin.ofNat 15 (autoPacked 0x8e8e8e8e8e8ecbcdcbcb98988e8ecbcbcbcbcbcd98989898cbcbcbcbcbcdcbcd76767676cdcbcdcb76547654cbcd989a76763232cdcb9a9876543210 4 (8*i.val+j.val))
theorem autoOk187 : autoGood autoExpr187 autoDfa187 0 := by
  apply autoTransfer (N := 14) (autoCombine autoDfa6 autoDfa186 Bool.and) autoDfa187 autoSrc187 autoDst187 autoNext187
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk186)
  · rfl

def autoExpr188 : AutoF := (.ge ⟨-4,0,1,0⟩)
def autoDfa188 : AutoM Nat := autoPackedTab 0x430c30869a8610410d341a69a681041041 3
def autoSrc188 (i : Fin 5) : AutoLit := (#[(.ge ⟨-4,0,1,0⟩),(.ge ⟨-4,0,1,-2⟩),(.ge ⟨-4,0,1,-1⟩),(.ge ⟨-4,0,1,-3⟩),(.ge ⟨-4,0,1,-4⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst188 (i : Fin 5) : Nat := autoPacked 0x4688 3 i.val
def autoNext188 (i : Fin 5) (j : Fin 8) : Fin 5 := Fin.ofNat 5 (autoPacked 0x86186169a86120869a69a69a208208 3 (8*i.val+j.val))
theorem autoOk188 : autoGood autoExpr188 autoDfa188 0 := by
  apply autoTransfer (N := 4) autoAtom autoDfa188 autoSrc188 autoDst188 autoNext188
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨-4,0,1,0⟩))
  · rfl

def autoExpr189 : AutoF := .con autoExpr6 autoExpr188
def autoDfa189 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc189 (i : Fin 10) : Nat × Nat := (autoPacked 0x24964688 3 i.val, autoPacked 0x2109a208 3 i.val)
def autoDst189 (i : Fin 10) : Nat := autoPacked 0x0 1 i.val
def autoNext189 (i : Fin 10) (j : Fin 8) : Fin 10 := Fin.ofNat 10 (autoPacked 0x98989898545454548787878787875456545498988787545454565456323232325654565432103210 4 (8*i.val+j.val))
theorem autoOk189 : autoGood autoExpr189 autoDfa189 0 := by
  apply autoTransfer (N := 9) (autoCombine autoDfa6 autoDfa188 Bool.and) autoDfa189 autoSrc189 autoDst189 autoNext189
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk188)
  · rfl

def autoExpr190 : AutoF := .con autoExpr187 autoExpr189
def autoDfa190 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc190 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst190 (i : Fin 6) : Nat := autoPacked 0x0 1 i.val
def autoNext190 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk190 : autoGood autoExpr190 autoDfa190 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa187 autoDfa189 Bool.and) autoDfa190 autoSrc190 autoDst190 autoNext190
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk187 autoOk189)
  · rfl

def autoExpr191 : AutoF := .con autoExpr190 autoExpr99
def autoDfa191 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc191 (i : Fin 1) : Nat × Nat := (autoPacked 0x0 1 i.val, autoPacked 0x0 1 i.val)
def autoDst191 (i : Fin 1) : Nat := autoPacked 0x0 1 i.val
def autoNext191 (i : Fin 1) (j : Fin 8) : Fin 1 := Fin.ofNat 1 (autoPacked 0x0 1 (8*i.val+j.val))
theorem autoOk191 : autoGood autoExpr191 autoDfa191 0 := by
  apply autoTransfer (N := 0) (autoCombine autoDfa190 autoDfa99 Bool.and) autoDfa191 autoSrc191 autoDst191 autoNext191
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk190 autoOk99)
  · rfl

def autoExpr192 : AutoF := .disj autoExpr185 autoExpr191
def autoDfa192 : AutoM Nat := autoPackedTab 0x92493492692482632a304c651409249244649440 3
def autoSrc192 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst192 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext192 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x24924d24d2492632a326328a2492498c9288 3 (8*i.val+j.val))
theorem autoOk192 : autoGood autoExpr192 autoDfa192 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa185 autoDfa191 Bool.or) autoDfa192 autoSrc192 autoDst192 autoNext192
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk185 autoOk191)
  · rfl

def autoExpr193 : AutoF := .disj autoExpr178 autoExpr192
def autoDfa193 : AutoM Nat := autoPackedTab 0x92493492692692632a304c651409249244649440 3
def autoSrc193 (i : Fin 7) : Nat × Nat := (autoPacked 0x64688 3 i.val, autoPacked 0x14c688 3 i.val)
def autoDst193 (i : Fin 7) : Nat := autoPacked 0x16c688 3 i.val
def autoNext193 (i : Fin 7) (j : Fin 8) : Fin 7 := Fin.ofNat 7 (autoPacked 0x24924e24924d24e24d2632a326328a2492498c9288 3 (8*i.val+j.val))
theorem autoOk193 : autoGood autoExpr193 autoDfa193 0 := by
  apply autoTransfer (N := 6) (autoCombine autoDfa178 autoDfa192 Bool.or) autoDfa193 autoSrc193 autoDst193 autoNext193
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk178 autoOk192)
  · rfl

def autoExpr194 : AutoF := .con autoExpr39 autoExpr193
def autoDfa194 : AutoM Nat := autoPackedTab 0x92493492692692632a304c651409249244649440 3
def autoSrc194 (i : Fin 14) : Nat × Nat := (autoPacked 0x96769876543210 4 i.val, autoPacked 0x2a2498c9288 3 i.val)
def autoDst194 (i : Fin 14) : Nat := autoPacked 0x2a2498c9288 3 i.val
def autoNext194 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0x8888888dba76bcbc88898889babababa8888888988888888888d888dba76bc7689888988ba54ba5488898888ba7632328988888876543210 4 (8*i.val+j.val))
theorem autoOk194 : autoGood autoExpr194 autoDfa194 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa39 autoDfa193 Bool.and) autoDfa194 autoSrc194 autoDst194 autoNext194
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk39 autoOk193)
  · rfl

def autoExpr195 : AutoF := .disj autoExpr175 autoExpr194
def autoDfa195 : AutoM Nat := autoPackedTab 0x4b55d7092892852d57d424924a14b55e3092492435497446a94688 3
def autoSrc195 (i : Fin 9) : Nat × Nat := (autoPacked 0x15794 2 i.val, autoPacked 0x5519440 3 i.val)
def autoDst195 (i : Fin 9) : Nat := autoPacked 0x4fac688 3 i.val
def autoNext195 (i : Fin 9) (j : Fin 8) : Fin 9 := Fin.ofNat 9 (autoPacked 0x222222282265272722282228226527652222222422652743222222226522272165224321 4 (8*i.val+j.val))
theorem autoOk195 : autoGood autoExpr195 autoDfa195 0 := by
  apply autoTransfer (N := 8) (autoCombine autoDfa175 autoDfa194 Bool.or) autoDfa195 autoSrc195 autoDst195 autoNext195
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk175 autoOk194)
  · rfl

def autoExpr196 : AutoF := (.ge ⟨2,0,1,0⟩)
def autoDfa196 : AutoM Nat := autoAlways
def autoSrc196 (i : Fin 3) : AutoLit := (#[(.ge ⟨2,0,1,0⟩),(.ge ⟨2,0,1,1⟩),(.ge ⟨2,0,1,2⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst196 (i : Fin 3) : Nat := autoPacked 0x0 1 i.val
def autoNext196 (i : Fin 3) (j : Fin 8) : Fin 3 := Fin.ofNat 3 (autoPacked 0x999999444444 2 (8*i.val+j.val))
theorem autoOk196 : autoGood autoExpr196 autoDfa196 0 := by
  apply autoTransfer (N := 2) autoAtom autoDfa196 autoSrc196 autoDst196 autoNext196
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨2,0,1,0⟩))
  · rfl

def autoExpr197 : AutoF := .con autoExpr6 autoExpr196
def autoDfa197 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc197 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst197 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext197 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk197 : autoGood autoExpr197 autoDfa197 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa6 autoDfa196 Bool.and) autoDfa197 autoSrc197 autoDst197 autoNext197
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk196)
  · rfl

def autoExpr198 : AutoF := .con autoExpr197 autoExpr167
def autoDfa198 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc198 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst198 (i : Fin 6) : Nat := autoPacked 0x0 1 i.val
def autoNext198 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk198 : autoGood autoExpr198 autoDfa198 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa197 autoDfa167 Bool.and) autoDfa198 autoSrc198 autoDst198 autoNext198
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk197 autoOk167)
  · rfl

def autoExpr199 : AutoF := (.ge ⟨0,1,-1,-2⟩)
def autoDfa199 : AutoM Nat := autoPackedTab 0x296a955a514154 2
def autoSrc199 (i : Fin 3) : AutoLit := (#[(.ge ⟨0,1,-1,-2⟩),(.ge ⟨0,1,-1,-1⟩),(.ge ⟨0,1,-1,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst199 (i : Fin 3) : Nat := autoPacked 0x24 2 i.val
def autoNext199 (i : Fin 3) (j : Fin 8) : Fin 3 := Fin.ofNat 3 (autoPacked 0xa5aa55a55055 2 (8*i.val+j.val))
theorem autoOk199 : autoGood autoExpr199 autoDfa199 0 := by
  apply autoTransfer (N := 2) autoAtom autoDfa199 autoSrc199 autoDst199 autoNext199
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨0,1,-1,-2⟩))
  · rfl
