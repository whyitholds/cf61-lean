import AutoCert0
import AutoCert5
import AutoCert7
import AutoCert19
import AutoCert21

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr318 : AutoF := .con autoExpr6 autoExpr317
def autoDfa318 : AutoM Nat := autoPackedTab 0x888988880ba43baba08888888918888888808988888804376ba7604345434308889888914343ba430898889880432143760452143210 4
def autoSrc318 (i : Fin 17) : Nat × Nat := (autoPacked 0x5b1a9610d3440 3 i.val, autoPacked 0x37f6a9694 2 i.val)
def autoDst318 (i : Fin 17) : Nat := autoPacked 0x898ba898764543210 4 i.val
def autoNext318 (i : Fin 17) (j : Fin 8) : Fin 17 := Fin.ofNat 17 (autoPacked 0x73929739d04a56b4a52a73929739ce7392a739d06b0836b1ac4a56b4a5294a5297392a4a529739294a9297412920d076b1074a56f4a52a20cc520c834a52a7392a20c836b0834a96b4a92920c4120d073144120c41 5 (8*i.val+j.val))
theorem autoOk318 : autoGood autoExpr318 autoDfa318 0 := by
  apply autoTransfer (N := 16) (autoCombine autoDfa6 autoDfa317 Bool.and) autoDfa318 autoSrc318 autoDst318 autoNext318
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk317)
  · rfl

def autoExpr319 : AutoF := (.dis ⟨0,0,1,1⟩ ⟨0,1,0,-2⟩)
def autoDfa319 : AutoM Nat := autoPackedTab 0x2db5290a524921b5b9120924924244a42436da448 3
def autoSrc319 (i : Fin 6) : AutoLit := (#[(.dis ⟨0,0,1,1⟩ ⟨0,1,0,-2⟩),(.dis ⟨0,0,1,0⟩ ⟨0,1,0,-1⟩),(.no),(.dis ⟨0,0,1,1⟩ ⟨0,1,0,-1⟩),(.dis ⟨0,0,1,0⟩ ⟨0,1,0,0⟩),(.dis ⟨0,0,1,1⟩ ⟨0,1,0,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst319 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext319 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0xb6d4a44a4924b5b9124924929129096db489 3 (8*i.val+j.val))
theorem autoOk319 : autoGood autoExpr319 autoDfa319 0 := by
  apply autoTransfer (N := 5) autoAtom autoDfa319 autoSrc319 autoDst319 autoNext319
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.dis ⟨0,0,1,1⟩ ⟨0,1,0,-2⟩))
  · rfl

def autoExpr320 : AutoF := .con autoExpr6 autoExpr319
def autoDfa320 : AutoM Nat := autoPackedTab 0x797933760333333381333833381337676760793576330792476330333333330383338330763376210352433210 4
def autoSrc320 (i : Fin 24) : Nat × Nat := (autoPacked 0xb2c6ac9610d3443440 3 i.val, autoPacked 0x76bb5290a5236da448 3 i.val)
def autoDst320 (i : Fin 24) : Nat := autoPacked 0x338379333833376352433210 4 i.val
def autoNext320 (i : Fin 24) (j : Fin 8) : Fin 24 := Fin.ofNat 24 (autoPacked 0xb5a947be11b5ad6841efb5ad6841eeb5a947be10b5ad5841ee9ca7220d4984210842118421084210841ef7bdef841ef7bdee7be107bdad846108461020d8b20d8b841ee7bdee20d4952549b5a977be119c90752483b56947ba109c8c55258b842118421120c8320c837ba107b9ad5258b5244141cc520c41 5 (8*i.val+j.val))
theorem autoOk320 : autoGood autoExpr320 autoDfa320 0 := by
  apply autoTransfer (N := 23) (autoCombine autoDfa6 autoDfa319 Bool.and) autoDfa320 autoSrc320 autoDst320 autoNext320
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk319)
  · rfl

def autoExpr321 : AutoF := .con autoExpr280 autoExpr320
def autoDfa321 : AutoM Nat := autoPackedTab 0x7df6f50db6dbc5bd75d43ee6ad86db6db0db6f36356f54438e3688 3
def autoSrc321 (i : Fin 17) : Nat × Nat := (autoPacked 0x5d6231dd44688 3 i.val, autoPacked 0x79883376352433210 4 i.val)
def autoDst321 (i : Fin 17) : Nat := autoPacked 0x3ef37ab8e3688 3 i.val
def autoNext321 (i : Fin 17) (j : Fin 8) : Fin 17 := Fin.ofNat 17 (autoPacked 0x4210e4210e83e0f20d49421084210e421084210d421084110820d8b20d8b4210e4210d20d4952549421084210883d0752483439084390883cc55258b421084210420c8320c8343908435085258b5244141cc520c41 5 (8*i.val+j.val))
theorem autoOk321 : autoGood autoExpr321 autoDfa321 0 := by
  apply autoTransfer (N := 16) (autoCombine autoDfa280 autoDfa320 Bool.and) autoDfa321 autoSrc321 autoDst321 autoNext321
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk280 autoOk320)
  · rfl

def autoExpr322 : AutoF := .con autoExpr318 autoExpr321
def autoDfa322 : AutoM Nat := autoPackedTab 0x337639390383833760333333371337639760763339350383476330333333330333337330763376350343433210 4
def autoSrc322 (i : Fin 24) : Nat × Nat := (autoPacked 0x8ba376ba9981437652143210 4 i.val, autoPacked 0xdaf6db79bd518e3688 3 i.val)
def autoDst322 (i : Fin 24) : Nat := autoPacked 0x339833333733763543433210 4 i.val
def autoNext322 (i : Fin 24) (j : Fin 8) : Fin 24 := Fin.ofNat 24 (autoPacked 0x6b5ad6b5b76b5af6b5b78c16ab56d5250948c16a6bdad6b5ad20e728c2726b5af6b5ad8c0838c2306b5ad6b5af6b5ad6b5ae6b5ad6b5ad20ccc20e726b5af6b5ae20d6ab556a6bdad6ddad5aa72b5528250875a8836bdad6bdad250c55aa726b5af6b5af20c838c0836bdad6b9ad5a8cc5a92821cc520c41 5 (8*i.val+j.val))
theorem autoOk322 : autoGood autoExpr322 autoDfa322 0 := by
  apply autoTransfer (N := 23) (autoCombine autoDfa318 autoDfa321 Bool.and) autoDfa322 autoSrc322 autoDst322 autoNext322
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk318 autoOk321)
  · rfl

def autoExpr323 : AutoF := (.ge ⟨-2,0,1,1⟩)
def autoDfa323 : AutoM Nat := autoPackedTab 0xeeee267b8999951265 2
def autoSrc323 (i : Fin 4) : AutoLit := (#[(.ge ⟨-2,0,1,1⟩),(.ge ⟨-2,0,1,0⟩),(.ge ⟨-2,0,1,-1⟩),(.ge ⟨-2,0,1,-2⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst323 (i : Fin 4) : Nat := autoPacked 0xe4 2 i.val
def autoNext323 (i : Fin 4) (j : Fin 8) : Fin 4 := Fin.ofNat 4 (autoPacked 0xeeee99ee99994499 2 (8*i.val+j.val))
theorem autoOk323 : autoGood autoExpr323 autoDfa323 0 := by
  apply autoTransfer (N := 3) autoAtom autoDfa323 autoSrc323 autoDst323 autoNext323
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨-2,0,1,1⟩))
  · rfl

def autoExpr324 : AutoF := .con autoExpr6 autoExpr323
def autoDfa324 : AutoM Nat := autoPackedTab 0x888888891888888880888988891767643430898889880888988880434343430898888880432143210765043210 4
def autoSrc324 (i : Fin 13) : Nat × Nat := (autoPacked 0x596468b440 3 i.val, autoPacked 0x16e4664 2 i.val)
def autoDst324 (i : Fin 13) : Nat := autoPacked 0x9888876543210 4 i.val
def autoNext324 (i : Fin 13) (j : Fin 8) : Fin 13 := Fin.ofNat 13 (autoPacked 0x8b8b8b8c8b8b8b8b8b8b989a989898988b8b98988b8c8b8c767643438c8b8c8b8b8c989a434343438c8b9a984321432176504321 4 (8*i.val+j.val))
theorem autoOk324 : autoGood autoExpr324 autoDfa324 0 := by
  apply autoTransfer (N := 12) (autoCombine autoDfa6 autoDfa323 Bool.and) autoDfa324 autoSrc324 autoDst324 autoNext324
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk323)
  · rfl

def autoExpr325 : AutoF := .con autoExpr108 autoExpr324
def autoDfa325 : AutoM Nat := autoPackedTab 0x12492618e3249049261209249244681248 3
def autoSrc325 (i : Fin 12) : Nat × Nat := (autoPacked 0x71c68b440 3 i.val, autoPacked 0x998876543210 4 i.val)
def autoDst325 (i : Fin 12) : Nat := autoPacked 0x8498d1248 3 i.val
def autoNext325 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0x8888888b8888888a8888888988888888888a888b767643438a888b88888a8889434343438a8889884321432176504321 4 (8*i.val+j.val))
theorem autoOk325 : autoGood autoExpr325 autoDfa325 0 := by
  apply autoTransfer (N := 11) (autoCombine autoDfa108 autoDfa324 Bool.and) autoDfa325 autoSrc325 autoDst325 autoNext325
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk108 autoOk324)
  · rfl

def autoExpr326 : AutoF := .con autoExpr325 autoExpr72
def autoDfa326 : AutoM Nat := autoPackedTab 0x555757954555539554 2
def autoSrc326 (i : Fin 12) : Nat × Nat := (autoPacked 0x9198d0248 3 i.val, autoPacked 0x84c689688 3 i.val)
def autoDst326 (i : Fin 12) : Nat := autoPacked 0xd5e554 2 i.val
def autoNext326 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0x1111111b1111111aa9a91111111111181118111ba976113211111a11a954111111181118113211321111111176543211 4 (8*i.val+j.val))
theorem autoOk326 : autoGood autoExpr326 autoDfa326 0 := by
  apply autoTransfer (N := 11) (autoCombine autoDfa325 autoDfa72 Bool.and) autoDfa326 autoSrc326 autoDst326 autoNext326
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk325 autoOk72)
  · rfl

def autoExpr327 : AutoF := .disj autoExpr322 autoExpr326
def autoDfa327 : AutoM Nat := autoPackedTab 0x33683a3a039393368033683a68068333a370333333361396568330393468330333333330333336330683368370653433210 4
def autoSrc327 (i : Fin 12) : Nat × Nat := (autoPacked 0x987653443210 4 i.val, autoPacked 0x557954 2 i.val)
def autoDst327 (i : Fin 12) : Nat := autoPacked 0xa96876543210 4 i.val
def autoNext327 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0x33983b3b3a3a33983333333933983b9898333b37333333363a6598333a34983333333333333339339833983765343321 4 (8*i.val+j.val))
theorem autoOk327 : autoGood autoExpr327 autoDfa327 0 := by
  apply autoTransfer (N := 11) (autoCombine autoDfa322 autoDfa326 Bool.or) autoDfa327 autoSrc327 autoDst327 autoNext327
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk322 autoOk326)
  · rfl
