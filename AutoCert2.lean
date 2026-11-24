import AutoCert0
import AutoCert1

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr30 : AutoF := .con autoExpr6 autoExpr29
def autoDfa30 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc30 (i : Fin 8) : Nat × Nat := (autoPacked 0xb10688 3 i.val, autoPacked 0xfa 1 i.val)
def autoDst30 (i : Fin 8) : Nat := autoPacked 0xb10688 3 i.val
def autoNext30 (i : Fin 8) (j : Fin 8) : Fin 8 := Fin.ofNat 8 (autoPacked 0xdb6db7db6db675d75d74c74cdb7db775d69adf6df674c688 3 (8*i.val+j.val))
theorem autoOk30 : autoGood autoExpr30 autoDfa30 0 := by
  apply autoTransfer (N := 7) (autoCombine autoDfa6 autoDfa29 Bool.and) autoDfa30 autoSrc30 autoDst30 autoNext30
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk29)
  · rfl

def autoExpr31 : AutoF := (.ge ⟨-1,1,-1,-1⟩)
def autoDfa31 : AutoM Nat := autoPackedTab 0x22820105142040 2
def autoSrc31 (i : Fin 3) : AutoLit := (#[(.ge ⟨-1,1,-1,-1⟩),(.ge ⟨-1,1,-1,0⟩),(.ge ⟨-1,1,-1,-2⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst31 (i : Fin 3) : Nat := autoPacked 0x24 2 i.val
def autoNext31 (i : Fin 3) (j : Fin 8) : Fin 3 := Fin.ofNat 3 (autoPacked 0x8a0810510810 2 (8*i.val+j.val))
theorem autoOk31 : autoGood autoExpr31 autoDfa31 0 := by
  apply autoTransfer (N := 2) autoAtom autoDfa31 autoSrc31 autoDst31 autoNext31
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨-1,1,-1,-1⟩))
  · rfl

def autoExpr32 : AutoF := .con autoExpr6 autoExpr31
def autoDfa32 : AutoM Nat := autoPackedTab 0x1b6db74b8e34e06db6db0d395341b6dd6c38c3440 3
def autoSrc32 (i : Fin 14) : Nat × Nat := (autoPacked 0x2b8ecb11688 3 i.val, autoPacked 0xa524210 2 i.val)
def autoDst32 (i : Fin 14) : Nat := autoPacked 0x1b75bae3688 3 i.val
def autoNext32 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0x86886689868d66896b66bb6b6b69bb6766866b69868866866b66bb6766866b6635c532358988698666896b693235a2326986676635403210 4 (8*i.val+j.val))
theorem autoOk32 : autoGood autoExpr32 autoDfa32 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa6 autoDfa31 Bool.and) autoDfa32 autoSrc32 autoDst32 autoNext32
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk31)
  · rfl

def autoExpr33 : AutoF := (.dis ⟨1,0,1,-1⟩ ⟨0,1,0,-1⟩)
def autoDfa33 : AutoM Nat := autoPackedTab 0x76d8e876374a463a19213248631a5321409249244854688 3
def autoSrc33 (i : Fin 7) : AutoLit := (#[(.dis ⟨1,0,1,-1⟩ ⟨0,1,0,-1⟩),(.no),(.dis ⟨1,0,1,0⟩ ⟨0,1,0,-1⟩),(.dis ⟨1,0,1,-1⟩ ⟨0,1,0,0⟩),(.dis ⟨1,0,1,0⟩ ⟨0,1,0,0⟩),(.dis ⟨1,0,1,1⟩ ⟨0,1,0,-1⟩),(.dis ⟨1,0,1,1⟩ ⟨0,1,0,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst33 (i : Fin 7) : Nat := autoPacked 0x1ac688 3 i.val
def autoNext33 (i : Fin 7) (j : Fin 8) : Fin 7 := Fin.ofNat 7 (autoPacked 0x3b6c74d8dd29c74324324863d2990a24924990a8d1 3 (8*i.val+j.val))
theorem autoOk33 : autoGood autoExpr33 autoDfa33 0 := by
  apply autoTransfer (N := 6) autoAtom autoDfa33 autoSrc33 autoDst33 autoNext33
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.dis ⟨1,0,1,-1⟩ ⟨0,1,0,-1⟩))
  · rfl

def autoExpr34 : AutoF := .con autoExpr6 autoExpr33
def autoDfa34 : AutoM Nat := autoPackedTab 0x24924f30cc74c264663412792793a6863079279209249244c6c688 3
def autoSrc34 (i : Fin 20) : Nat × Nat := (autoPacked 0xb5992591a443440 3 i.val, autoPacked 0xc75d64289854688 3 i.val)
def autoDst34 (i : Fin 20) : Nat := autoPacked 0xe6224f249c6c688 3 i.val
def autoNext34 (i : Fin 20) (j : Fin 8) : Fin 20 := Fin.ofNat 20 (autoPacked 0x5bdef7adec5ad6b5ad725bdf37adec7cd6e7b1cb5bdef7aded7bd6e7b5cb7aded5b5ad7aded5b5ac5ad6b5ad6b7b5cb6b56a5ad725ad724a1284a1288a22749c875c96b5c96b89e0121cc57adec5b5ac49c87220837b1cb6b16a4a0c14a0c121cc520c41 5 (8*i.val+j.val))
theorem autoOk34 : autoGood autoExpr34 autoDfa34 0 := by
  apply autoTransfer (N := 19) (autoCombine autoDfa6 autoDfa33 Bool.and) autoDfa34 autoSrc34 autoDst34 autoNext34
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk33)
  · rfl

def autoExpr35 : AutoF := .con autoExpr32 autoExpr34
def autoDfa35 : AutoM Nat := autoPackedTab 0x124926124984b049261209249241249688 3
def autoSrc35 (i : Fin 17) : Nat × Nat := (autoPacked 0x56abb118c3440 3 i.val, autoPacked 0x15a7e49c6c688 3 i.val)
def autoDst35 (i : Fin 17) : Nat := autoPacked 0x1261849249688 3 i.val
def autoNext35 (i : Fin 17) (j : Fin 8) : Fin 17 := Fin.ofNat 17 (autoPacked 0x318c6318d0330c6330c6224878388e318cc318cb318c6318cc318c6318cb328ca324ca324ca824c9318c6340c62288733887318c6318c621de123905318cc318cc338876a483330c632cc6328c13250121cc520c41 5 (8*i.val+j.val))
theorem autoOk35 : autoGood autoExpr35 autoDfa35 0 := by
  apply autoTransfer (N := 16) (autoCombine autoDfa32 autoDfa34 Bool.and) autoDfa35 autoSrc35 autoDst35 autoNext35
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk32 autoOk34)
  · rfl

def autoExpr36 : AutoF := .con autoExpr30 autoExpr35
def autoDfa36 : AutoM Nat := autoPackedTab 0x124926124984b049261209249241249688 3
def autoSrc36 (i : Fin 11) : Nat × Nat := (autoPacked 0xed88b440 3 i.val, autoPacked 0x10c249688 3 i.val)
def autoDst36 (i : Fin 11) : Nat := autoPacked 0x10c249688 3 i.val
def autoNext36 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x777977787777777977777778777777774646464679777977777977794646a643797778774651465146514321 4 (8*i.val+j.val))
theorem autoOk36 : autoGood autoExpr36 autoDfa36 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa30 autoDfa35 Bool.and) autoDfa36 autoSrc36 autoDst36 autoNext36
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk30 autoOk35)
  · rfl

def autoExpr37 : AutoF := .con autoExpr28 autoExpr36
def autoDfa37 : AutoM Nat := autoPackedTab 0x124926124984b049261209249241249688 3
def autoSrc37 (i : Fin 9) : Nat × Nat := (autoPacked 0x3463440 3 i.val, autoPacked 0x4249688 3 i.val)
def autoDst37 (i : Fin 9) : Nat := autoPacked 0x4249688 3 i.val
def autoNext37 (i : Fin 9) (j : Fin 8) : Fin 9 := Fin.ofNat 9 (autoPacked 0x555555585555474755555455555555555555555455558743555558555555476155554321 4 (8*i.val+j.val))
theorem autoOk37 : autoGood autoExpr37 autoDfa37 0 := by
  apply autoTransfer (N := 8) (autoCombine autoDfa28 autoDfa36 Bool.and) autoDfa37 autoSrc37 autoDst37 autoNext37
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk28 autoOk36)
  · rfl

def autoExpr38 : AutoF := (.ge ⟨0,0,1,-1⟩)
def autoDfa38 : AutoM Nat := autoPackedTab 0x3ffe0 1
def autoSrc38 (i : Fin 2) : AutoLit := (#[(.ge ⟨0,0,1,-1⟩),(.ge ⟨0,0,1,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst38 (i : Fin 2) : Nat := autoPacked 0x2 1 i.val
def autoNext38 (i : Fin 2) (j : Fin 8) : Fin 2 := Fin.ofNat 2 (autoPacked 0xfff0 1 (8*i.val+j.val))
theorem autoOk38 : autoGood autoExpr38 autoDfa38 0 := by
  apply autoTransfer (N := 1) autoAtom autoDfa38 autoSrc38 autoDst38 autoNext38
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨0,0,1,-1⟩))
  · rfl

def autoExpr39 : AutoF := .con autoExpr6 autoExpr38
def autoDfa39 : AutoM Nat := autoPackedTab 0x888888891888888880888988891767676760898889880765476540888988880767632320898888880765432100 4
def autoSrc39 (i : Fin 12) : Nat × Nat := (autoPacked 0xb2c688688 3 i.val, autoPacked 0xcf0 1 i.val)
def autoDst39 (i : Fin 12) : Nat := autoPacked 0x988876543210 4 i.val
def autoNext39 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0xaaaaaaabaaaaaaaaaaaa8889aaaa8888aaabaaab76767676abaaabaa76547654aaab888976763232abaa898876543210 4 (8*i.val+j.val))
theorem autoOk39 : autoGood autoExpr39 autoDfa39 0 := by
  apply autoTransfer (N := 11) (autoCombine autoDfa6 autoDfa38 Bool.and) autoDfa39 autoSrc39 autoDst39 autoNext39
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk38)
  · rfl

def autoExpr40 : AutoF := (.ge ⟨-3,0,1,-1⟩)
def autoDfa40 : AutoM Nat := autoPackedTab 0xccdd0899944cc19910 2
def autoSrc40 (i : Fin 4) : AutoLit := (#[(.ge ⟨-3,0,1,-1⟩),(.ge ⟨-3,0,1,-2⟩),(.ge ⟨-3,0,1,0⟩),(.ge ⟨-3,0,1,-3⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst40 (i : Fin 4) : Nat := autoPacked 0xe4 2 i.val
def autoNext40 (i : Fin 4) (j : Fin 8) : Fin 4 := Fin.ofNat 4 (autoPacked 0xccdd226644cc6644 2 (8*i.val+j.val))
theorem autoOk40 : autoGood autoExpr40 autoDfa40 0 := by
  apply autoTransfer (N := 3) autoAtom autoDfa40 autoSrc40 autoDst40 autoNext40
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨-3,0,1,-1⟩))
  · rfl

def autoExpr41 : AutoF := .con autoExpr6 autoExpr40
def autoDfa41 : AutoM Nat := autoPackedTab 0x24924f249e4920f2492469a1860d2b30b061851409249241859440 3
def autoSrc41 (i : Fin 14) : Nat × Nat := (autoPacked 0x2c665910688 3 i.val, autoPacked 0xa04ca44 2 i.val)
def autoDst41 (i : Fin 14) : Nat := autoPacked 0x39d49263288 3 i.val
def autoNext41 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0x6c6c9c9d6c6c9c9c9c9d96989d9c9896969676769c9c9698767679799c9c9696b5b53535b5a4351496987678353532329896787635143210 4 (8*i.val+j.val))
theorem autoOk41 : autoGood autoExpr41 autoDfa41 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa6 autoDfa40 Bool.and) autoDfa41 autoSrc41 autoDst41 autoNext41
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk40)
  · rfl

def autoExpr42 : AutoF := (.ge ⟨3,1,-1,0⟩)
def autoDfa42 : AutoM Nat := autoPackedTab 0x428c5092c320b08a10a25021140905a041 3
def autoSrc42 (i : Fin 5) : AutoLit := (#[(.ge ⟨3,1,-1,0⟩),(.ge ⟨3,1,-1,1⟩),(.ge ⟨3,1,-1,2⟩),(.ge ⟨3,1,-1,-1⟩),(.ge ⟨3,1,-1,3⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst42 (i : Fin 5) : Nat := autoPacked 0x4688 3 i.val
def autoNext42 (i : Fin 5) (j : Fin 8) : Fin 5 := Fin.ofNat 5 (autoPacked 0x8518a12c320b45085140845020b408 3 (8*i.val+j.val))
theorem autoOk42 : autoGood autoExpr42 autoDfa42 0 := by
  apply autoTransfer (N := 4) autoAtom autoDfa42 autoSrc42 autoDst42 autoNext42
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨3,1,-1,0⟩))
  · rfl

def autoExpr43 : AutoF := .con autoExpr6 autoExpr42
def autoDfa43 : AutoM Nat := autoPackedTab 0x7f769f16db6dc6db6db43e63460b6eb6e2d3ed342eb6eb43463440 3
def autoSrc43 (i : Fin 17) : Nat × Nat := (autoPacked 0x570c565918688 3 i.val, autoPacked 0x30c460940b408 3 i.val)
def autoDst43 (i : Fin 17) : Nat := autoPacked 0x5d4dfaeb5c688 3 i.val
def autoNext43 (i : Fin 17) (j : Fin 8) : Fin 17 := Fin.ofNat 17 (autoPacked 0x4b8ce49930499303992a4b8ce4992e4a92e3a926624e961d892adeb288ab4992e3992a399263a4e6399263a4ea3a4e6624e94992e399263992a3a4ea2ada4288243a4ea624e8288ab188a23a9263a0e62882418820 5 (8*i.val+j.val))
theorem autoOk43 : autoGood autoExpr43 autoDfa43 0 := by
  apply autoTransfer (N := 16) (autoCombine autoDfa6 autoDfa42 Bool.and) autoDfa43 autoSrc43 autoDst43 autoNext43
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk42)
  · rfl

def autoExpr44 : AutoF := (.dis ⟨-3,0,1,-1⟩ ⟨0,1,0,0⟩)
def autoDfa44 : AutoM Nat := autoPackedTab 0x21045080834cb29249240a210802659440 3
def autoSrc44 (i : Fin 5) : AutoLit := (#[(.dis ⟨-3,0,1,-1⟩ ⟨0,1,0,0⟩),(.dis ⟨-3,0,1,-2⟩ ⟨0,1,0,0⟩),(.no),(.dis ⟨-3,0,1,0⟩ ⟨0,1,0,0⟩),(.dis ⟨-3,0,1,-3⟩ ⟨0,1,0,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst44 (i : Fin 5) : Nat := autoPacked 0x4688 3 i.val
def autoNext44 (i : Fin 5) (j : Fin 8) : Fin 5 := Fin.ofNat 5 (autoPacked 0x4208a10834cb4924922884204cb288 3 (8*i.val+j.val))
theorem autoOk44 : autoGood autoExpr44 autoDfa44 0 := by
  apply autoTransfer (N := 4) autoAtom autoDfa44 autoSrc44 autoDst44 autoNext44
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.dis ⟨-3,0,1,-1⟩ ⟨0,1,0,0⟩))
  · rfl
