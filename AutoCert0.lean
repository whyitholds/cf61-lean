import AutoRestrict

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr0 : AutoF := (.pow)
def autoDfa0 : AutoM Nat := autoPackedTab 0x2aaa8999951110 2
def autoSrc0 (i : Fin 3) : AutoLit := (#[(.pow),(.ge ⟨-1,0,0,0⟩),(.ge ⟨-1,0,0,-1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst0 (i : Fin 3) : Nat := autoPacked 0x24 2 i.val
def autoNext0 (i : Fin 3) (j : Fin 8) : Fin 3 := Fin.ofNat 3 (autoPacked 0xaaaa99994444 2 (8*i.val+j.val))
theorem autoOk0 : autoGood autoExpr0 autoDfa0 0 := by
  apply autoTransfer (N := 2) autoAtom autoDfa0 autoSrc0 autoDst0 autoNext0
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.pow))
  · rfl

def autoExpr1 : AutoF := (.ge ⟨0,1,0,-1⟩)
def autoDfa1 : AutoM Nat := autoPackedTab 0x3ff98 1
def autoSrc1 (i : Fin 2) : AutoLit := (#[(.ge ⟨0,1,0,-1⟩),(.ge ⟨0,1,0,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst1 (i : Fin 2) : Nat := autoPacked 0x2 1 i.val
def autoNext1 (i : Fin 2) (j : Fin 8) : Fin 2 := Fin.ofNat 2 (autoPacked 0xffcc 1 (8*i.val+j.val))
theorem autoOk1 : autoGood autoExpr1 autoDfa1 0 := by
  apply autoTransfer (N := 1) autoAtom autoDfa1 autoSrc1 autoDst1 autoNext1
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨0,1,0,-1⟩))
  · rfl

def autoExpr2 : AutoF := (.ge ⟨2,-1,0,0⟩)
def autoDfa2 : AutoM Nat := autoPackedTab 0x8888444449091 2
def autoSrc2 (i : Fin 3) : AutoLit := (#[(.ge ⟨2,-1,0,0⟩),(.ge ⟨2,-1,0,1⟩),(.ge ⟨2,-1,0,-1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst2 (i : Fin 3) : Nat := autoPacked 0x24 2 i.val
def autoNext2 (i : Fin 3) (j : Fin 8) : Fin 3 := Fin.ofNat 3 (autoPacked 0x222244442424 2 (8*i.val+j.val))
theorem autoOk2 : autoGood autoExpr2 autoDfa2 0 := by
  apply autoTransfer (N := 2) autoAtom autoDfa2 autoSrc2 autoDst2 autoNext2
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨2,-1,0,0⟩))
  · rfl

def autoExpr3 : AutoF := (.ge ⟨4,0,-1,-1⟩)
def autoDfa3 : AutoM Nat := autoPackedTab 0x430c30969a8612410d345a69a689041040 3
def autoSrc3 (i : Fin 5) : AutoLit := (#[(.ge ⟨4,0,-1,-1⟩),(.ge ⟨4,0,-1,1⟩),(.ge ⟨4,0,-1,0⟩),(.ge ⟨4,0,-1,2⟩),(.ge ⟨4,0,-1,3⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst3 (i : Fin 5) : Nat := autoPacked 0x4688 3 i.val
def autoNext3 (i : Fin 5) (j : Fin 8) : Fin 5 := Fin.ofNat 5 (autoPacked 0x86186169a86120869a69a69a208208 3 (8*i.val+j.val))
theorem autoOk3 : autoGood autoExpr3 autoDfa3 0 := by
  apply autoTransfer (N := 4) autoAtom autoDfa3 autoSrc3 autoDst3 autoNext3
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨4,0,-1,-1⟩))
  · rfl

def autoExpr4 : AutoF := .con autoExpr2 autoExpr3
def autoDfa4 : AutoM Nat := autoPackedTab 0xa983a98317676767608383838317654a9831323276760545483831321076541765476541323232320545454541321032100 4
def autoSrc4 (i : Fin 11) : Nat × Nat := (autoPacked 0x92424 2 i.val, autoPacked 0x10c69a208 3 i.val)
def autoDst4 (i : Fin 11) : Nat := autoPacked 0xa9876543210 4 i.val
def autoNext4 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0xa983a98376767676838383837654a98332327676545483833210765476547654323232325454545432103210 4 (8*i.val+j.val))
theorem autoOk4 : autoGood autoExpr4 autoDfa4 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa2 autoDfa3 Bool.and) autoDfa4 autoSrc4 autoDst4 autoNext4
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk2 autoOk3)
  · rfl

def autoExpr5 : AutoF := .con autoExpr1 autoExpr4
def autoDfa5 : AutoM Nat := autoPackedTab 0x107b0707b0614a1284a12801cc731cc730462734627340c1b06c1b06160d6a60d6a02505225052012839a0f60c2310c4942500398e660d8308c4e6a507304e6291835a80310409414804a0e64a0e608c4310c43100e6290e6290031040310400 5
def autoSrc5 (i : Fin 17) : Nat × Nat := (autoPacked 0x1f3cc 1 i.val, autoPacked 0xa9108837654543210 4 i.val)
def autoDst5 (i : Fin 17) : Nat := autoPacked 0x107b9ac5a928398a418820 5 i.val
def autoNext5 (i : Fin 17) (j : Fin 8) : Fin 17 := Fin.ofNat 17 (autoPacked 0x83d8383d834a1284a128398e6398e6189cd189cd60d8360d8360d6a60d6a4a0a44a0a44a0e683d83188624a128398e660d83189cd4a0e6398a460d6a188204a0a44a0e64a0e61886218862398a4398a41882018820 5 (8*i.val+j.val))
theorem autoOk5 : autoGood autoExpr5 autoDfa5 0 := by
  apply autoTransfer (N := 16) (autoCombine autoDfa1 autoDfa4 Bool.and) autoDfa5 autoSrc5 autoDst5 autoNext5
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk1 autoOk4)
  · rfl

def autoExpr6 : AutoF := .con autoExpr0 autoExpr5
def autoDfa6 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc6 (i : Fin 27) : Nat × Nat := (autoPacked 0x2aaa6aa9999944 2 i.val, autoPacked 0x3440441ee6988c5a86208128398a418820 5 i.val)
def autoDst6 (i : Fin 27) : Nat := autoPacked 0x124924924924924964688 3 i.val
def autoNext6 (i : Fin 27) (j : Fin 8) : Fin 27 := Fin.ofNat 27 (autoPacked 0x6e69a6e69a6e5b96e5b96e5786e5786e5b94dd37b560db560d4dd374dd373c8f23c8f26b2936b2936e69a4dcf26e5784dcb18360d8360d835ee835ee4dcb14dcb14dcf24dcf26b1ac6b1ac3c8b13c8b16b16a6b16a4dcf2b560d6b1ac4a1283c8f28360d6b2934a0e63c8b1835ee6b16a4a0a44a0e64a0e61886218862398a4398a41882018820 5 (8*i.val+j.val))
theorem autoOk6 : autoGood autoExpr6 autoDfa6 0 := by
  apply autoTransfer (N := 26) (autoCombine autoDfa0 autoDfa5 Bool.and) autoDfa6 autoSrc6 autoDst6 autoNext6
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk0 autoOk5)
  · rfl

def autoExpr7 : AutoF := .neg autoExpr6
def autoDfa7 : AutoM Nat := autoFlip autoDfa6
theorem autoOk7 : autoGood autoExpr7 autoDfa7 0 := (autoGoodNeg _ autoOk6)

def autoExpr8 : AutoF := (.ge ⟨-1,0,1,0⟩)
def autoDfa8 : AutoM Nat := autoPackedTab 0x2bc15 1
def autoSrc8 (i : Fin 2) : AutoLit := (#[(.ge ⟨-1,0,1,0⟩),(.ge ⟨-1,0,1,-1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst8 (i : Fin 2) : Nat := autoPacked 0x2 1 i.val
def autoNext8 (i : Fin 2) (j : Fin 8) : Fin 2 := Fin.ofNat 2 (autoPacked 0xaf0a 1 (8*i.val+j.val))
theorem autoOk8 : autoGood autoExpr8 autoDfa8 0 := by
  apply autoTransfer (N := 1) autoAtom autoDfa8 autoSrc8 autoDst8 autoNext8
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨-1,0,1,0⟩))
  · rfl

def autoExpr9 : AutoF := .con autoExpr6 autoExpr8
def autoDfa9 : AutoM Nat := autoPackedTab 0xdb6db73b6db6c36df6dcefb6fb0db7db61554d3437db6d85503440 3
def autoSrc9 (i : Fin 10) : Nat × Nat := (autoPacked 0x2cb19688 3 i.val, autoPacked 0xca 1 i.val)
def autoDst9 (i : Fin 10) : Nat := autoPacked 0x3edac688 3 i.val
def autoNext9 (i : Fin 10) (j : Fin 8) : Fin 10 := Fin.ofNat 10 (autoPacked 0x88886869888868686868666768686666888968698988696868696667525232326968676652403210 4 (8*i.val+j.val))
theorem autoOk9 : autoGood autoExpr9 autoDfa9 0 := by
  apply autoTransfer (N := 9) (autoCombine autoDfa6 autoDfa8 Bool.and) autoDfa9 autoSrc9 autoDst9 autoNext9
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk8)
  · rfl

def autoExpr10 : AutoF := (.ge ⟨3,0,-1,-1⟩)
def autoDfa10 : AutoM Nat := autoPackedTab 0xeedd5119966ee62110 2
def autoSrc10 (i : Fin 4) : AutoLit := (#[(.ge ⟨3,0,-1,-1⟩),(.ge ⟨3,0,-1,1⟩),(.ge ⟨3,0,-1,0⟩),(.ge ⟨3,0,-1,2⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst10 (i : Fin 4) : Nat := autoPacked 0xe4 2 i.val
def autoNext10 (i : Fin 4) (j : Fin 8) : Fin 4 := Fin.ofNat 4 (autoPacked 0xeedd446666ee8844 2 (8*i.val+j.val))
theorem autoOk10 : autoGood autoExpr10 autoDfa10 0 := by
  apply autoTransfer (N := 3) autoAtom autoDfa10 autoSrc10 autoDst10 autoNext10
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨3,0,-1,-1⟩))
  · rfl

def autoExpr11 : AutoF := .con autoExpr6 autoExpr10
def autoDfa11 : AutoM Nat := autoPackedTab 0x1b6db6c36db6d4edb6bb0db5db53554d3435db5d85503440 3
def autoSrc11 (i : Fin 12) : Nat × Nat := (autoPacked 0xb25919688 3 i.val, autoPacked 0x6ea44 2 i.val)
def autoDst11 (i : Fin 12) : Nat := autoPacked 0xdb5dac688 3 i.val
def autoNext11 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0x6a6a9a9b6a6a9a9a969676769a9a9698767679799a9a96969a9b96989b9a989696987678525232329896787652403210 4 (8*i.val+j.val))
theorem autoOk11 : autoGood autoExpr11 autoDfa11 0 := by
  apply autoTransfer (N := 11) (autoCombine autoDfa6 autoDfa10 Bool.and) autoDfa11 autoSrc11 autoDst11 autoNext11
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk10)
  · rfl

def autoExpr12 : AutoF := (.dis ⟨-1,0,1,0⟩ ⟨0,1,0,-1⟩)
def autoDfa12 : AutoM Nat := autoPackedTab 0x6edf269b9555528790 2
def autoSrc12 (i : Fin 4) : AutoLit := (#[(.dis ⟨-1,0,1,0⟩ ⟨0,1,0,-1⟩),(.no),(.dis ⟨-1,0,1,0⟩ ⟨0,1,0,0⟩),(.dis ⟨-1,0,1,-1⟩ ⟨0,1,0,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst12 (i : Fin 4) : Nat := autoPacked 0xe4 2 i.val
def autoNext12 (i : Fin 4) (j : Fin 8) : Fin 4 := Fin.ofNat 4 (autoPacked 0x6edf9a6e5555a1e4 2 (8*i.val+j.val))
theorem autoOk12 : autoGood autoExpr12 autoDfa12 0 := by
  apply autoTransfer (N := 3) autoAtom autoDfa12 autoSrc12 autoDst12 autoNext12
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.dis ⟨-1,0,1,0⟩ ⟨0,1,0,-1⟩))
  · rfl

def autoExpr13 : AutoF := .con autoExpr6 autoExpr12
def autoDfa13 : AutoM Nat := autoPackedTab 0x49249c49389389c49c4824e24914d45340924924550b440 3
def autoSrc13 (i : Fin 16) : Nat × Nat := (autoPacked 0x92ca9d8c8688 3 i.val, autoPacked 0x2bd561e4 2 i.val)
def autoDst13 (i : Fin 16) : Nat := autoPacked 0x271249361688 3 i.val
def autoNext13 (i : Fin 16) (j : Fin 8) : Fin 16 := Fin.ofNat 16 (autoPacked 0xeef7ce7fe7ee7ecee7ee7ecd7ecec7cc7ecec7cb9a9a9a9a777877787777777877777777e7ed7ecdedf7cd7f9a149a147ecdc7cb6a6292327877787762543210 4 (8*i.val+j.val))
theorem autoOk13 : autoGood autoExpr13 autoDfa13 0 := by
  apply autoTransfer (N := 15) (autoCombine autoDfa6 autoDfa12 Bool.and) autoDfa13 autoSrc13 autoDst13 autoNext13
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk12)
  · rfl

def autoExpr14 : AutoF := .con autoExpr11 autoExpr13
def autoDfa14 : AutoM Nat := autoPackedTab 0x9249349249a4824d24914d45340924924550b440 3
def autoSrc14 (i : Fin 14) : Nat × Nat := (autoPacked 0x34a9dd60688 3 i.val, autoPacked 0x31c49361688 3 i.val)
def autoDst14 (i : Fin 14) : Nat := autoPacked 0x9a49361688 3 i.val
def autoNext14 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0x7777777d777778777777777b8a8a9a9a777877787777777877777777777d777b7d777b778ac49a14777b77786a6292327877787762543210 4 (8*i.val+j.val))
theorem autoOk14 : autoGood autoExpr14 autoDfa14 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa11 autoDfa13 Bool.and) autoDfa14 autoSrc14 autoDst14 autoNext14
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk11 autoOk13)
  · rfl

def autoExpr15 : AutoF := .con autoExpr9 autoExpr14
def autoDfa15 : AutoM Nat := autoPackedTab 0x9249349249a4824d24914d45340924924550b440 3
def autoSrc15 (i : Fin 14) : Nat × Nat := (autoPacked 0x2ce9fd60688 3 i.val, autoPacked 0x9a49361688 3 i.val)
def autoDst15 (i : Fin 14) : Nat := autoPacked 0x9a49361688 3 i.val
def autoNext15 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0x77787778787778777777777bdada9a9a7778777777777778777777777778777b78777b77dac49a14777b77776a6292327877777762543210 4 (8*i.val+j.val))
theorem autoOk15 : autoGood autoExpr15 autoDfa15 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa9 autoDfa14 Bool.and) autoDfa15 autoSrc15 autoDst15 autoNext15
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk9 autoOk14)
  · rfl
