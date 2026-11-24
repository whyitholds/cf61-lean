import AutoCert0
import AutoCert3
import AutoCert4

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr72 : AutoF := .con autoExpr70 autoExpr71
def autoDfa72 : AutoM Nat := autoPackedTab 0x124926124c24c24b44b40924924344b448 3
def autoSrc72 (i : Fin 10) : Nat × Nat := (autoPacked 0x2124b448 3 i.val, autoPacked 0x2d8d3440 3 i.val)
def autoDst72 (i : Fin 10) : Nat := autoPacked 0x2124b448 3 i.val
def autoNext72 (i : Fin 10) (j : Fin 8) : Fin 10 := Fin.ofNat 10 (autoPacked 0x77777779777777787777777777787778656565657779777965436543787778776521652143214321 4 (8*i.val+j.val))
theorem autoOk72 : autoGood autoExpr72 autoDfa72 0 := by
  apply autoTransfer (N := 9) (autoCombine autoDfa70 autoDfa71 Bool.and) autoDfa72 autoSrc72 autoDst72 autoNext72
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk70 autoOk71)
  · rfl

def autoExpr73 : AutoF := .con autoExpr68 autoExpr72
def autoDfa73 : AutoM Nat := autoPackedTab 0x555757558555535594 2
def autoSrc73 (i : Fin 12) : Nat × Nat := (autoPacked 0x862859440 3 i.val, autoPacked 0x90968b448 3 i.val)
def autoDst73 (i : Fin 12) : Nat := autoPacked 0xd5d594 2 i.val
def autoNext73 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0x2222222b2222222a2222222992922828222a222b2246224622222922222a222a92762843222222229252282176524321 4 (8*i.val+j.val))
theorem autoOk73 : autoGood autoExpr73 autoDfa73 0 := by
  apply autoTransfer (N := 11) (autoCombine autoDfa68 autoDfa72 Bool.and) autoDfa73 autoSrc73 autoDst73 autoNext73
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk68 autoOk72)
  · rfl

def autoExpr74 : AutoF := .disj autoExpr67 autoExpr73
def autoDfa74 : AutoM Nat := autoPackedTab 0x124d35c2492494c9249209acba312492c82692e84590c688 3
def autoSrc74 (i : Fin 8) : Nat × Nat := (autoPacked 0xb1b288 3 i.val, autoPacked 0x5d94 2 i.val)
def autoDst74 (i : Fin 8) : Nat := autoPacked 0xbac688 3 i.val
def autoNext74 (i : Fin 8) (j : Fin 8) : Fin 8 := Fin.ofNat 8 (autoPacked 0x9249279269be9249259249249acfa39249e49a4fa1b218d1 3 (8*i.val+j.val))
theorem autoOk74 : autoGood autoExpr74 autoDfa74 0 := by
  apply autoTransfer (N := 7) (autoCombine autoDfa67 autoDfa73 Bool.or) autoDfa74 autoSrc74 autoDst74 autoNext74
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk67 autoOk73)
  · rfl

def autoExpr75 : AutoF := .disj autoExpr59 autoExpr74
def autoDfa75 : AutoM Nat := autoPackedTab 0x124d35c2492494c9249209acba312492c82692e84590c688 3
def autoSrc75 (i : Fin 7) : Nat × Nat := (autoPacked 0x0 1 i.val, autoPacked 0x1ac688 3 i.val)
def autoDst75 (i : Fin 7) : Nat := autoPacked 0x1ac688 3 i.val
def autoNext75 (i : Fin 7) (j : Fin 8) : Fin 7 := Fin.ofNat 7 (autoPacked 0x9269ae9249259249249acba39249649a4ba1b218d1 3 (8*i.val+j.val))
theorem autoOk75 : autoGood autoExpr75 autoDfa75 0 := by
  apply autoTransfer (N := 6) (autoCombine autoDfa59 autoDfa74 Bool.or) autoDfa75 autoSrc75 autoDst75 autoNext75
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk59 autoOk74)
  · rfl

def autoExpr76 : AutoF := .con autoExpr51 autoExpr75
def autoDfa76 : AutoM Nat := autoPackedTab 0x124d35c2492494c9249209acba312492c82692e84590c688 3
def autoSrc76 (i : Fin 13) : Nat × Nat := (autoPacked 0x6b13a63440 3 i.val, autoPacked 0x4d3590c688 3 i.val)
def autoDst76 (i : Fin 13) : Nat := autoPacked 0x4d3590c688 3 i.val
def autoNext76 (i : Fin 13) (j : Fin 8) : Fin 13 := Fin.ofNat 13 (autoPacked 0xccccccccc7cb4b8bc7ca476a474b4989ccccccc8c7c74747ccccc4cccbca8b65ccccccc44b878943ccccc8cc4b6a896187654321 4 (8*i.val+j.val))
theorem autoOk76 : autoGood autoExpr76 autoDfa76 0 := by
  apply autoTransfer (N := 12) (autoCombine autoDfa51 autoDfa75 Bool.and) autoDfa76 autoSrc76 autoDst76 autoNext76
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk51 autoOk75)
  · rfl

def autoExpr77 : AutoF := (.ge ⟨-1,0,1,-1⟩)
def autoDfa77 : AutoM Nat := autoPackedTab 0x3d6a0 1
def autoSrc77 (i : Fin 2) : AutoLit := (#[(.ge ⟨-1,0,1,-1⟩),(.ge ⟨-1,0,1,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst77 (i : Fin 2) : Nat := autoPacked 0x2 1 i.val
def autoNext77 (i : Fin 2) (j : Fin 8) : Fin 2 := Fin.ofNat 2 (autoPacked 0xf550 1 (8*i.val+j.val))
theorem autoOk77 : autoGood autoExpr77 autoDfa77 0 := by
  apply autoTransfer (N := 1) autoAtom autoDfa77 autoSrc77 autoDst77 autoNext77
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨-1,0,1,-1⟩))
  · rfl

def autoExpr78 : AutoF := .con autoExpr6 autoExpr77
def autoDfa78 : AutoM Nat := autoPackedTab 0x666766671676667660666666671666666660959535350958435140666766660353532320676666660351432100 4
def autoSrc78 (i : Fin 12) : Nat × Nat := (autoPacked 0x66cb10688 3 i.val, autoPacked 0xf30 1 i.val)
def autoDst78 (i : Fin 12) : Nat := autoPacked 0x987666543210 4 i.val
def autoNext78 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0x888968698988696888886869888868686868666768686666b5b53535b5a4351468696667353532326968676635143210 4 (8*i.val+j.val))
theorem autoOk78 : autoGood autoExpr78 autoDfa78 0 := by
  apply autoTransfer (N := 11) (autoCombine autoDfa6 autoDfa77 Bool.and) autoDfa78 autoSrc78 autoDst78 autoNext78
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk77)
  · rfl

def autoExpr79 : AutoF := (.ge ⟨-1,-1,1,0⟩)
def autoDfa79 : AutoM Nat := autoPackedTab 0x256a4549510151 2
def autoSrc79 (i : Fin 3) : AutoLit := (#[(.ge ⟨-1,-1,1,0⟩),(.ge ⟨-1,-1,1,-1⟩),(.ge ⟨-1,-1,1,-2⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst79 (i : Fin 3) : Nat := autoPacked 0x24 2 i.val
def autoNext79 (i : Fin 3) (j : Fin 8) : Fin 3 := Fin.ofNat 3 (autoPacked 0x95a954954054 2 (8*i.val+j.val))
theorem autoOk79 : autoGood autoExpr79 autoDfa79 0 := by
  apply autoTransfer (N := 2) autoAtom autoDfa79 autoSrc79 autoDst79 autoNext79
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨-1,-1,1,0⟩))
  · rfl

def autoExpr80 : AutoF := .con autoExpr6 autoExpr79
def autoDfa80 : AutoM Nat := autoPackedTab 0x24e24e249249c5df5a741c4924824e2490d3a53409249243b03440 3
def autoSrc80 (i : Fin 13) : Nat × Nat := (autoPacked 0x3ae4b11688 3 i.val, autoPacked 0x225054 2 i.val)
def autoDst80 (i : Fin 13) : Nat := autoPacked 0x7c4926c688 3 i.val
def autoNext80 (i : Fin 13) (j : Fin 8) : Fin 13 := Fin.ofNat 13 (autoPacked 0x699b666b6999666b866788876999666986668886666986676669866635c532356b996769666b86673235a2326769876635403210 4 (8*i.val+j.val))
theorem autoOk80 : autoGood autoExpr80 autoDfa80 0 := by
  apply autoTransfer (N := 12) (autoCombine autoDfa6 autoDfa79 Bool.and) autoDfa80 autoSrc80 autoDst80 autoNext80
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk79)
  · rfl

def autoExpr81 : AutoF := .con autoExpr80 autoExpr14
def autoDfa81 : AutoM Nat := autoPackedTab 0x92493493614e024d24904985340924924184b440 3
def autoSrc81 (i : Fin 17) : Nat × Nat := (autoPacked 0x7f8d8f2760688 3 i.val, autoPacked 0x1a69269aa1688 3 i.val)
def autoDst81 (i : Fin 17) : Nat := autoPacked 0x1a49269309688 3 i.val
def autoNext81 (i : Fin 17) (j : Fin 8) : Fin 17 := Fin.ofNat 17 (autoPacked 0x842e0842e0842e08429084210842e084210842d5320c5214c0b821084210842e0842108421084295214c0a1480842e0842d3b1e6508660b8210b421531645202408429084213a0e6088620842108421398a418820 5 (8*i.val+j.val))
theorem autoOk81 : autoGood autoExpr81 autoDfa81 0 := by
  apply autoTransfer (N := 16) (autoCombine autoDfa80 autoDfa14 Bool.and) autoDfa81 autoSrc81 autoDst81 autoNext81
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk80 autoOk14)
  · rfl

def autoExpr82 : AutoF := (.ge ⟨-3,-1,1,0⟩)
def autoDfa82 : AutoM Nat := autoPackedTab 0x42cc70865a8590510d141a299681081441 3
def autoSrc82 (i : Fin 5) : AutoLit := (#[(.ge ⟨-3,-1,1,0⟩),(.ge ⟨-3,-1,1,-2⟩),(.ge ⟨-3,-1,1,-1⟩),(.ge ⟨-3,-1,1,-3⟩),(.ge ⟨-3,-1,1,-4⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst82 (i : Fin 5) : Nat := autoPacked 0x4688 3 i.val
def autoNext82 (i : Fin 5) (j : Fin 8) : Fin 5 := Fin.ofNat 5 (autoPacked 0x8598e165a85928868a68a65a210288 3 (8*i.val+j.val))
theorem autoOk82 : autoGood autoExpr82 autoDfa82 0 := by
  apply autoTransfer (N := 4) autoAtom autoDfa82 autoSrc82 autoDst82 autoNext82
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨-3,-1,1,0⟩))
  · rfl

def autoExpr83 : AutoF := .con autoExpr6 autoExpr82
def autoDfa83 : AutoM Nat := autoPackedTab 0x92493492692482e328b051651409249241641440 3
def autoSrc83 (i : Fin 16) : Nat × Nat := (autoPacked 0xb1c765911688 3 i.val, autoPacked 0x110689682288 3 i.val)
def autoDst83 (i : Fin 16) : Nat := autoPacked 0xa61249259288 3 i.val
def autoNext83 (i : Fin 16) (j : Fin 8) : Fin 16 := Fin.ofNat 16 (autoPacked 0x9c6c969fe979e7e9969f769a9c6c969c797ae978969c769a769679767696797a7976e979969c769635d532359a9c7a96769a797a3235b2327a96787635403210 4 (8*i.val+j.val))
theorem autoOk83 : autoGood autoExpr83 autoDfa83 0 := by
  apply autoTransfer (N := 15) (autoCombine autoDfa6 autoDfa82 Bool.and) autoDfa83 autoSrc83 autoDst83 autoNext83
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk82)
  · rfl

def autoExpr84 : AutoF := (.ge ⟨5,0,-1,-1⟩)
def autoDfa84 : AutoM Nat := autoPackedTab 0x2aaa9a4904186169aaaa2618e385c71a68a081040 3
def autoSrc84 (i : Fin 6) : AutoLit := (#[(.ge ⟨5,0,-1,-1⟩),(.ge ⟨5,0,-1,2⟩),(.ge ⟨5,0,-1,1⟩),(.ge ⟨5,0,-1,3⟩),(.ge ⟨5,0,-1,0⟩),(.ge ⟨5,0,-1,4⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst84 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext84 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0xaaaa6920830c69aaaa30c71c71c69a410208 3 (8*i.val+j.val))
theorem autoOk84 : autoGood autoExpr84 autoDfa84 0 := by
  apply autoTransfer (N := 5) autoAtom autoDfa84 autoSrc84 autoDst84 autoNext84
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨5,0,-1,-1⟩))
  · rfl

def autoExpr85 : AutoF := .con autoExpr6 autoExpr84
def autoDfa85 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc85 (i : Fin 14) : Nat × Nat := (autoPacked 0x24965919688 3 i.val, autoPacked 0x5322692208 3 i.val)
def autoDst85 (i : Fin 14) : Nat := autoPacked 0x24965919688 3 i.val
def autoNext85 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0x6d6dbdbdc6c6cbcb79797676bdbdb9babdbdb9b9b9b9797a7676c6c6b9b97979b9ba797abab97a79797a7678525232327a79787652403210 4 (8*i.val+j.val))
theorem autoOk85 : autoGood autoExpr85 autoDfa85 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa6 autoDfa84 Bool.and) autoDfa85 autoSrc85 autoDst85 autoNext85
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk84)
  · rfl

def autoExpr86 : AutoF := (.dis ⟨-3,0,1,0⟩ ⟨0,1,0,-1⟩)
def autoDfa86 : AutoM Nat := autoPackedTab 0x779d4c06eb8e60a699743443bc865d37514d45344924924550b440 3
def autoSrc86 (i : Fin 8) : AutoLit := (#[(.dis ⟨-3,0,1,0⟩ ⟨0,1,0,-1⟩),(.no),(.dis ⟨-3,0,1,0⟩ ⟨0,1,0,0⟩),(.dis ⟨-3,0,1,-2⟩ ⟨0,1,0,0⟩),(.dis ⟨-3,0,1,-1⟩ ⟨0,1,0,-1⟩),(.dis ⟨-3,0,1,-1⟩ ⟨0,1,0,0⟩),(.dis ⟨-3,0,1,-3⟩ ⟨0,1,0,0⟩),(.dis ⟨-3,0,1,-2⟩ ⟨0,1,0,-1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst86 (i : Fin 8) : Nat := autoPacked 0xfac688 3 i.val
def autoNext86 (i : Fin 8) (j : Fin 8) : Fin 8 := Fin.ofNat 8 (autoPacked 0x779d4c375c7329a65d68877965d375a6a29a249249aa1688 3 (8*i.val+j.val))
theorem autoOk86 : autoGood autoExpr86 autoDfa86 0 := by
  apply autoTransfer (N := 7) autoAtom autoDfa86 autoSrc86 autoDst86 autoNext86
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.dis ⟨-3,0,1,0⟩ ⟨0,1,0,-1⟩))
  · rfl
