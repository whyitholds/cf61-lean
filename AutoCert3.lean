import AutoCert0
import AutoCert2

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr45 : AutoF := .con autoExpr6 autoExpr44
def autoDfa45 : AutoM Nat := autoPackedTab 0x49249c49389241c49248a6b2cb14c459409249241651240 3
def autoSrc45 (i : Fin 17) : Nat × Nat := (autoPacked 0x58cd92c8d0688 3 i.val, autoPacked 0x360228409b288 3 i.val)
def autoDst45 (i : Fin 17) : Nat := autoPacked 0x636124925a248 3 i.val
def autoNext45 (i : Fin 17) (j : Fin 8) : Fin 17 := Fin.ofNat 17 (autoPacked 0x3a8ef53d703a8ef53d6f53d705a9695416f5b1675294a5294c5a96751d075294a5294a53d6f5a96951d074290b53d6f5a9675294c5294c709c531465709a4314245a96951d09308c2308c25b167525073142418820 5 (8*i.val+j.val))
theorem autoOk45 : autoGood autoExpr45 autoDfa45 0 := by
  apply autoTransfer (N := 16) (autoCombine autoDfa6 autoDfa44 Bool.and) autoDfa45 autoSrc45 autoDst45 autoNext45
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk44)
  · rfl

def autoExpr46 : AutoF := .con autoExpr43 autoExpr45
def autoDfa46 : AutoM Nat := autoPackedTab 0x24924f349c59c093c9241e49248a6e2cb14c459409249241651240 3
def autoSrc46 (i : Fin 15) : Nat × Nat := (autoPacked 0x176ecfd54688 3 i.val, autoPacked 0x1ae76125a248 3 i.val)
def autoDst46 (i : Fin 15) : Nat := autoPacked 0x4fd6125a248 3 i.val
def autoNext46 (i : Fin 15) (j : Fin 8) : Fin 15 := Fin.ofNat 15 (autoPacked 0x6666666e666e66676666666ca8db353b666c66676c666766387832386666666766666666a2ab3535a894351466676667323832326766676635143210 4 (8*i.val+j.val))
theorem autoOk46 : autoGood autoExpr46 autoDfa46 0 := by
  apply autoTransfer (N := 14) (autoCombine autoDfa43 autoDfa45 Bool.and) autoDfa46 autoSrc46 autoDst46 autoNext46
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk43 autoOk45)
  · rfl

def autoExpr47 : AutoF := .con autoExpr41 autoExpr46
def autoDfa47 : AutoM Nat := autoPackedTab 0x24924f349c59c093c9241e49248a6e2cb14c459409249241651240 3
def autoSrc47 (i : Fin 12) : Nat × Nat := (autoPacked 0xff4d64688 3 i.val, autoPacked 0x3ceb0b448 3 i.val)
def autoDst47 (i : Fin 12) : Nat := autoPacked 0x3ceb0b448 3 i.val
def autoNext47 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0x1111111b1111111a111b111175981418111a11111a111111959515157578141475631413151512121111111114131210 4 (8*i.val+j.val))
theorem autoOk47 : autoGood autoExpr47 autoDfa47 0 := by
  apply autoTransfer (N := 11) (autoCombine autoDfa41 autoDfa46 Bool.and) autoDfa47 autoSrc47 autoDst47 autoNext47
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk41 autoOk46)
  · rfl

def autoExpr48 : AutoF := .con autoExpr39 autoExpr47
def autoDfa48 : AutoM Nat := autoPackedTab 0x24924f349c59c093c9241e49248a6e2cb14c459409249241651240 3
def autoSrc48 (i : Fin 15) : Nat × Nat := (autoPacked 0x967569876543210 4 i.val, autoPacked 0x1f58492ca248 3 i.val)
def autoDst48 (i : Fin 15) : Nat := autoPacked 0x1f58492ca248 3 i.val
def autoNext48 (i : Fin 15) (j : Fin 8) : Fin 15 := Fin.ofNat 15 (autoPacked 0x8888888eca7d767d888e88898e8889887a7a7a7a888888898888888888898889cacd767689888988cab47654888988887a7a32328988888876543210 4 (8*i.val+j.val))
theorem autoOk48 : autoGood autoExpr48 autoDfa48 0 := by
  apply autoTransfer (N := 14) (autoCombine autoDfa39 autoDfa47 Bool.and) autoDfa48 autoSrc48 autoDst48 autoNext48
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk39 autoOk47)
  · rfl

def autoExpr49 : AutoF := .disj autoExpr37 autoExpr48
def autoDfa49 : AutoM Nat := autoPackedTab 0x944a464a0444744440474444440444444471949a46460948546450444444440444474430444447440464544410464543210 4
def autoSrc49 (i : Fin 12) : Nat × Nat := (autoPacked 0x249849688 3 i.val, autoPacked 0xfac2d1240 3 i.val)
def autoDst49 (i : Fin 12) : Nat := autoPacked 0x7a9876543210 4 i.val
def autoNext49 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0x4444444b944a464a444b44444b44444444444447949a4646948546454444444444447443444447444645444146454321 4 (8*i.val+j.val))
theorem autoOk49 : autoGood autoExpr49 autoDfa49 0 := by
  apply autoTransfer (N := 11) (autoCombine autoDfa37 autoDfa48 Bool.or) autoDfa49 autoSrc49 autoDst49 autoNext49
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk37 autoOk48)
  · rfl

def autoExpr50 : AutoF := (.ge ⟨1,0,-1,0⟩)
def autoDfa50 : AutoM Nat := autoPackedTab 0x3d4a1 1
def autoSrc50 (i : Fin 2) : AutoLit := (#[(.ge ⟨1,0,-1,0⟩),(.ge ⟨1,0,-1,-1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst50 (i : Fin 2) : Nat := autoPacked 0x2 1 i.val
def autoNext50 (i : Fin 2) (j : Fin 8) : Fin 2 := Fin.ofNat 2 (autoPacked 0xf550 1 (8*i.val+j.val))
theorem autoOk50 : autoGood autoExpr50 autoDfa50 0 := by
  apply autoTransfer (N := 1) autoAtom autoDfa50 autoSrc50 autoDst50 autoNext50
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨1,0,-1,0⟩))
  · rfl

def autoExpr51 : AutoF := .con autoExpr6 autoExpr50
def autoDfa51 : AutoM Nat := autoPackedTab 0x1b6db6c35d5d746ba3a60db6db32ebad3436db3d83a63440 3
def autoSrc51 (i : Fin 12) : Nat × Nat := (autoPacked 0x66cb10688 3 i.val, autoPacked 0xf30 1 i.val)
def autoDst51 (i : Fin 12) : Nat := autoPacked 0xdb67ac688 3 i.val
def autoNext51 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0x888968698988696888886869888868686868666768686666b5b53535b5a4351468696667353532326968676635143210 4 (8*i.val+j.val))
theorem autoOk51 : autoGood autoExpr51 autoDfa51 0 := by
  apply autoTransfer (N := 11) (autoCombine autoDfa6 autoDfa50 Bool.and) autoDfa51 autoSrc51 autoDst51 autoNext51
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk50)
  · rfl

def autoExpr52 : AutoF := (.ge ⟨3,-1,1,1⟩)
def autoDfa52 : AutoM Nat := autoPackedTab 0x41121010c12c308408a04144304a280289 3
def autoSrc52 (i : Fin 5) : AutoLit := (#[(.ge ⟨3,-1,1,1⟩),(.ge ⟨3,-1,1,0⟩),(.ge ⟨3,-1,1,2⟩),(.ge ⟨3,-1,1,-1⟩),(.ge ⟨3,-1,1,3⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst52 (i : Fin 5) : Nat := autoPacked 0x4688 3 i.val
def autoNext52 (i : Fin 5) (j : Fin 8) : Fin 5 := Fin.ofNat 5 (autoPacked 0x8224200c12c34204500510c1450051 3 (8*i.val+j.val))
theorem autoOk52 : autoGood autoExpr52 autoDfa52 0 := by
  apply autoTransfer (N := 4) autoAtom autoDfa52 autoSrc52 autoDst52 autoNext52
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨3,-1,1,1⟩))
  · rfl

def autoExpr53 : AutoF := .con autoExpr6 autoExpr52
def autoDfa53 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc53 (i : Fin 16) : Nat × Nat := (autoPacked 0x8e596445b440 3 i.val, autoPacked 0x648850610288 3 i.val)
def autoDst53 (i : Fin 16) : Nat := autoPacked 0x8e596445b440 3 i.val
def autoNext53 (i : Fin 16) (j : Fin 8) : Fin 16 := Fin.ofNat 16 (autoPacked 0x8f8ddf8f8d9a8f8a8d9d8f8d9d988d9ab8b998b88d9d8f8a98b89d989d988d9d4743e7479a988a9d98bc9d9c9d9c8d9a435347439cb89a984321476153204321 4 (8*i.val+j.val))
theorem autoOk53 : autoGood autoExpr53 autoDfa53 0 := by
  apply autoTransfer (N := 15) (autoCombine autoDfa6 autoDfa52 Bool.and) autoDfa53 autoSrc53 autoDst53 autoNext53
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk52)
  · rfl

def autoExpr54 : AutoF := (.ge ⟨-1,0,-1,-1⟩)
def autoDfa54 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc54 (i : Fin 2) : AutoLit := (#[(.ge ⟨-1,0,-1,-1⟩),(.ge ⟨-1,0,-1,-2⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst54 (i : Fin 2) : Nat := autoPacked 0x0 1 i.val
def autoNext54 (i : Fin 2) (j : Fin 8) : Fin 2 := Fin.ofNat 2 (autoPacked 0xfaa0 1 (8*i.val+j.val))
theorem autoOk54 : autoGood autoExpr54 autoDfa54 0 := by
  apply autoTransfer (N := 1) autoAtom autoDfa54 autoSrc54 autoDst54 autoNext54
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨-1,0,-1,-1⟩))
  · rfl

def autoExpr55 : AutoF := .con autoExpr6 autoExpr54
def autoDfa55 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc55 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst55 (i : Fin 6) : Nat := autoPacked 0x0 1 i.val
def autoNext55 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk55 : autoGood autoExpr55 autoDfa55 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa6 autoDfa54 Bool.and) autoDfa55 autoSrc55 autoDst55 autoNext55
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk54)
  · rfl

def autoExpr56 : AutoF := (.dis ⟨3,0,1,0⟩ ⟨0,1,0,-2⟩)
def autoDfa56 : AutoM Nat := autoPackedTab 0x379793961973496830939636761367673751737535651968376320333333330763275430754365310434131210 4
def autoSrc56 (i : Fin 10) : AutoLit := (#[(.dis ⟨3,0,1,0⟩ ⟨0,1,0,-2⟩),(.dis ⟨3,0,1,0⟩ ⟨0,1,0,-1⟩),(.dis ⟨3,0,1,1⟩ ⟨0,1,0,-1⟩),(.no),(.dis ⟨3,0,1,2⟩ ⟨0,1,0,-1⟩),(.dis ⟨3,0,1,0⟩ ⟨0,1,0,0⟩),(.dis ⟨3,0,1,1⟩ ⟨0,1,0,0⟩),(.dis ⟨3,0,1,2⟩ ⟨0,1,0,0⟩),(.dis ⟨3,0,1,3⟩ ⟨0,1,0,-1⟩),(.dis ⟨3,0,1,3⟩ ⟨0,1,0,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst56 (i : Fin 10) : Nat := autoPacked 0x9876543210 4 i.val
def autoNext56 (i : Fin 10) (j : Fin 8) : Fin 10 := Fin.ofNat 10 (autoPacked 0x37979396973496839396367636767375737535659683763233333333763275437543653143413121 4 (8*i.val+j.val))
theorem autoOk56 : autoGood autoExpr56 autoDfa56 0 := by
  apply autoTransfer (N := 9) autoAtom autoDfa56 autoSrc56 autoDst56 autoNext56
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.dis ⟨3,0,1,0⟩ ⟨0,1,0,-2⟩))
  · rfl

def autoExpr57 : AutoF := .con autoExpr6 autoExpr56
def autoDfa57 : AutoM Nat := autoPackedTab 0x924927324f24e74d65d44924920d64d6313c93c83553584488c688 3
def autoSrc57 (i : Fin 25) : Nat × Nat := (autoPacked 0x4964b64b230d168b440 3 i.val, autoPacked 0x5629836275437365343431210 4 i.val)
def autoDst57 (i : Fin 25) : Nat := autoPacked 0x49249e4f269ac914688 3 i.val
def autoNext57 (i : Fin 25) (j : Fin 8) : Fin 25 := Fin.ofNat 25 (autoPacked 0x836186e2f86de178361885db1861d36c2b0ab6b7ac1aeade8d6b5ad6b5b36de178360f85db1861cdab6b76de17836186e2efade8d85db16b5ad6b5adab6b26de122190b2190b6de128360f61989225496cdad6cdadade9385db62188621886aca8d849b16b5b36b5b3624e652483849b183dcd624ab52501398a120c41 5 (8*i.val+j.val))
theorem autoOk57 : autoGood autoExpr57 autoDfa57 0 := by
  apply autoTransfer (N := 24) (autoCombine autoDfa6 autoDfa56 Bool.and) autoDfa57 autoSrc57 autoDst57 autoNext57
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk56)
  · rfl
