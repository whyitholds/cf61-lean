import AutoCert0
import AutoCert4
import AutoCert11
import AutoCert12
import AutoCert14
import AutoCert20

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr302 : AutoF := .con autoExpr170 autoExpr150
def autoDfa302 : AutoM Nat := autoPackedTab 0x49249209249233234d3424923903523440 3
def autoSrc302 (i : Fin 11) : Nat × Nat := (autoPacked 0xd5b08688 3 i.val, autoPacked 0x124724688 3 i.val)
def autoDst302 (i : Fin 11) : Nat := autoPacked 0x124724688 3 i.val
def autoNext302 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x66686668a9a9a9a966666668666666676666666668666866a954a95466686667a93232326866676632543210 4 (8*i.val+j.val))
theorem autoOk302 : autoGood autoExpr302 autoDfa302 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa170 autoDfa150 Bool.and) autoDfa302 autoSrc302 autoDst302 autoNext302
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk170 autoOk150)
  · rfl

def autoExpr303 : AutoF := .disj autoExpr301 autoExpr302
def autoDfa303 : AutoM Nat := autoPackedTab 0x49249209249233234d3424923903523440 3
def autoSrc303 (i : Fin 5) : Nat × Nat := (autoPacked 0x0 1 i.val, autoPacked 0x4688 3 i.val)
def autoDst303 (i : Fin 5) : Nat := autoPacked 0x4688 3 i.val
def autoNext303 (i : Fin 5) (j : Fin 8) : Fin 5 := Fin.ofNat 5 (autoPacked 0x92492492492391a69a9248e46a4688 3 (8*i.val+j.val))
theorem autoOk303 : autoGood autoExpr303 autoDfa303 0 := by
  apply autoTransfer (N := 4) (autoCombine autoDfa301 autoDfa302 Bool.or) autoDfa303 autoSrc303 autoDst303 autoNext303
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk301 autoOk302)
  · rfl

def autoExpr304 : AutoF := .con autoExpr63 autoExpr202
def autoDfa304 : AutoM Nat := autoPackedTab 0x124924c648f5d44924920923d63124934823935444724688 3
def autoSrc304 (i : Fin 11) : Nat × Nat := (autoPacked 0x53503440 3 i.val, autoPacked 0x126b24688 3 i.val)
def autoDst304 (i : Fin 11) : Nat := autoPacked 0x126b24688 3 i.val
def autoNext304 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x6666646669694949666666686963878766666666696549a56666666469638743666668666365872163654321 4 (8*i.val+j.val))
theorem autoOk304 : autoGood autoExpr304 autoDfa304 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa63 autoDfa202 Bool.and) autoDfa304 autoSrc304 autoDst304 autoNext304
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk63 autoOk202)
  · rfl

def autoExpr305 : AutoF := .con autoExpr9 autoExpr211
def autoDfa305 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc305 (i : Fin 8) : Nat × Nat := (autoPacked 0xfac688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst305 (i : Fin 8) : Nat := autoPacked 0x0 1 i.val
def autoNext305 (i : Fin 8) (j : Fin 8) : Fin 8 := Fin.ofNat 8 (autoPacked 0xdb6db7db6db6db7db7df6df6db7db6aaa69adf6db6aa0688 3 (8*i.val+j.val))
theorem autoOk305 : autoGood autoExpr305 autoDfa305 0 := by
  apply autoTransfer (N := 7) (autoCombine autoDfa9 autoDfa211 Bool.and) autoDfa305 autoSrc305 autoDst305 autoNext305
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk9 autoOk211)
  · rfl

def autoExpr306 : AutoF := .disj autoExpr304 autoExpr305
def autoDfa306 : AutoM Nat := autoPackedTab 0x124924c648f5d44924920923d63124934823935444724688 3
def autoSrc306 (i : Fin 7) : Nat × Nat := (autoPacked 0x1ac688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst306 (i : Fin 7) : Nat := autoPacked 0x1ac688 3 i.val
def autoNext306 (i : Fin 7) (j : Fin 8) : Fin 7 := Fin.ofNat 7 (autoPacked 0x924926923d75924924923d639249a48e4d518e48d1 3 (8*i.val+j.val))
theorem autoOk306 : autoGood autoExpr306 autoDfa306 0 := by
  apply autoTransfer (N := 6) (autoCombine autoDfa304 autoDfa305 Bool.or) autoDfa306 autoSrc306 autoDst306 autoNext306
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk304 autoOk305)
  · rfl

def autoExpr307 : AutoF := .neg autoExpr306
def autoDfa307 : AutoM Nat := autoFlip autoDfa306
theorem autoOk307 : autoGood autoExpr307 autoDfa307 0 := (autoGoodNeg _ autoOk306)

def autoExpr308 : AutoF := .con autoExpr6 autoExpr307
def autoDfa308 : AutoM Nat := autoPackedTab 0x4b4b4b4b09999999a1999999990999a999904b43878709a999a9904b654b650999a999a14b43874309a9999990436587210436543210 4
def autoSrc308 (i : Fin 13) : Nat × Nat := (autoPacked 0x2b63443440 3 i.val, autoPacked 0x49a6b24688 3 i.val)
def autoDst308 (i : Fin 13) : Nat := autoPacked 0xba99876543210 4 i.val
def autoNext308 (i : Fin 13) (j : Fin 8) : Fin 13 := Fin.ofNat 13 (autoPacked 0x4c4c4c4c9999999b9999999a99999999999b999a4c4387879b999b994c654c65999b999b4c4387439b999a994365872143654321 4 (8*i.val+j.val))
theorem autoOk308 : autoGood autoExpr308 autoDfa308 0 := by
  apply autoTransfer (N := 12) (autoCombine autoDfa6 autoDfa307 Bool.and) autoDfa308 autoSrc308 autoDst308 autoNext308
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk307)
  · rfl

def autoExpr309 : AutoF := (.ge ⟨2,-1,1,2⟩)
def autoDfa309 : AutoM Nat := autoPackedTab 0xb6bb19ad9616644585 2
def autoSrc309 (i : Fin 4) : AutoLit := (#[(.ge ⟨2,-1,1,2⟩),(.ge ⟨2,-1,1,1⟩),(.ge ⟨2,-1,1,0⟩),(.ge ⟨2,-1,1,-1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst309 (i : Fin 4) : Nat := autoPacked 0xe4 2 i.val
def autoNext309 (i : Fin 4) (j : Fin 8) : Fin 4 := Fin.ofNat 4 (autoPacked 0xb6bb66b661661161 2 (8*i.val+j.val))
theorem autoOk309 : autoGood autoExpr309 autoDfa309 0 := by
  apply autoTransfer (N := 3) autoAtom autoDfa309 autoSrc309 autoDst309 autoNext309
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨2,-1,1,2⟩))
  · rfl

def autoExpr310 : AutoF := .con autoExpr6 autoExpr309
def autoDfa310 : AutoM Nat := autoPackedTab 0x2492494c9249209259252d34d3425925903443440 3
def autoSrc310 (i : Fin 17) : Nat × Nat := (autoPacked 0x48d5b210d3440 3 i.val, autoPacked 0x3ad858584 2 i.val)
def autoDst310 (i : Fin 17) : Nat := autoPacked 0x48d5b210d3440 3 i.val
def autoNext310 (i : Fin 17) (j : Fin 8) : Fin 17 := Fin.ofNat 17 (autoPacked 0x7c12f7c1f04bd2f7c12f4bd2b7c12b73483735cd4bd494bd2b4bd2f7c12b525494bd494bd494bd2f4ad494ad2f20d07735075254c4bd4c20cc520c834bd4c4bd2b20c8373483531494ad4920c4120d073144120c41 5 (8*i.val+j.val))
theorem autoOk310 : autoGood autoExpr310 autoDfa310 0 := by
  apply autoTransfer (N := 16) (autoCombine autoDfa6 autoDfa309 Bool.and) autoDfa310 autoSrc310 autoDst310 autoNext310
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk309)
  · rfl

def autoExpr311 : AutoF := (.ge ⟨0,0,-1,-2⟩)
def autoDfa311 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc311 (i : Fin 2) : AutoLit := (#[(.ge ⟨0,0,-1,-2⟩),(.ge ⟨0,0,-1,-1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst311 (i : Fin 2) : Nat := autoPacked 0x0 1 i.val
def autoNext311 (i : Fin 2) (j : Fin 8) : Fin 2 := Fin.ofNat 2 (autoPacked 0xff0f 1 (8*i.val+j.val))
theorem autoOk311 : autoGood autoExpr311 autoDfa311 0 := by
  apply autoTransfer (N := 1) autoAtom autoDfa311 autoSrc311 autoDst311 autoNext311
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨0,0,-1,-2⟩))
  · rfl

def autoExpr312 : AutoF := .con autoExpr6 autoExpr311
def autoDfa312 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc312 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst312 (i : Fin 6) : Nat := autoPacked 0x0 1 i.val
def autoNext312 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk312 : autoGood autoExpr312 autoDfa312 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa6 autoDfa311 Bool.and) autoDfa312 autoSrc312 autoDst312 autoNext312
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk311)
  · rfl

def autoExpr313 : AutoF := (.dis ⟨2,0,1,1⟩ ⟨0,1,0,-2⟩)
def autoDfa313 : AutoM Nat := autoPackedTab 0x6fefbe3f7cdea5bd75d4fcdfd106db6db1f45ab6356f5444513688 3
def autoSrc313 (i : Fin 8) : AutoLit := (#[(.dis ⟨2,0,1,1⟩ ⟨0,1,0,-2⟩),(.dis ⟨2,0,1,0⟩ ⟨0,1,0,-1⟩),(.dis ⟨2,0,1,1⟩ ⟨0,1,0,-1⟩),(.no),(.dis ⟨2,0,1,2⟩ ⟨0,1,0,-1⟩),(.dis ⟨2,0,1,0⟩ ⟨0,1,0,0⟩),(.dis ⟨2,0,1,1⟩ ⟨0,1,0,0⟩),(.dis ⟨2,0,1,2⟩ ⟨0,1,0,0⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst313 (i : Fin 8) : Nat := autoPacked 0xfac688 3 i.val
def autoNext313 (i : Fin 8) (j : Fin 8) : Fin 8 := Fin.ofNat 8 (autoPacked 0x6fefbefbe6f56f5d75f9bfa26db6dbfa2d5bd5bd518a26d1 3 (8*i.val+j.val))
theorem autoOk313 : autoGood autoExpr313 autoDfa313 0 := by
  apply autoTransfer (N := 7) autoAtom autoDfa313 autoSrc313 autoDst313 autoNext313
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.dis ⟨2,0,1,1⟩ ⟨0,1,0,-2⟩))
  · rfl

def autoExpr314 : AutoF := .con autoExpr6 autoExpr313
def autoDfa314 : AutoM Nat := autoPackedTab 0x797933760333333381333833381337676760793576330792476330333333330383338330763376210352433210 4
def autoSrc314 (i : Fin 25) : Nat × Nat := (autoPacked 0x4ad59649610d3443440 3 i.val, autoPacked 0x55f3fa2d5b7ac513688 3 i.val)
def autoDst314 (i : Fin 25) : Nat := autoPacked 0x3379338333833376352433210 4 i.val
def autoNext314 (i : Fin 25) (j : Fin 8) : Fin 25 := Fin.ofNat 25 (autoPacked 0x6b5f87e1f89be307e1b46b6729be72b56d520d496b5ad6b5b46b66f9be6f9be6f6b5ee9bdad9be309be307e1ad9be6f6b5f86b5f87e1ee6b5ad6b5ad6d1ad6d1ad20d8b20d8b9be726b5ee20d49525499bdb49be37b5507524839c9ad9ca30b54c55258b6b5b46b5b420c8320c839ca307b9ad5258b5244141cc520c41 5 (8*i.val+j.val))
theorem autoOk314 : autoGood autoExpr314 autoDfa314 0 := by
  apply autoTransfer (N := 24) (autoCombine autoDfa6 autoDfa313 Bool.and) autoDfa314 autoSrc314 autoDst314 autoNext314
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk313)
  · rfl

def autoExpr315 : AutoF := .con autoExpr312 autoExpr314
def autoDfa315 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc315 (i : Fin 10) : Nat × Nat := (autoPacked 0x0 1 i.val, autoPacked 0x9876543210 4 i.val)
def autoDst315 (i : Fin 10) : Nat := autoPacked 0x0 1 i.val
def autoNext315 (i : Fin 10) (j : Fin 8) : Fin 10 := Fin.ofNat 10 (autoPacked 0x79793376333333383338333833767676793576337924763333333333383338337633762135243321 4 (8*i.val+j.val))
theorem autoOk315 : autoGood autoExpr315 autoDfa315 0 := by
  apply autoTransfer (N := 9) (autoCombine autoDfa312 autoDfa314 Bool.and) autoDfa315 autoSrc315 autoDst315 autoNext315
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk312 autoOk314)
  · rfl

def autoExpr316 : AutoF := .con autoExpr310 autoExpr315
def autoDfa316 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc316 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst316 (i : Fin 6) : Nat := autoPacked 0x0 1 i.val
def autoNext316 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk316 : autoGood autoExpr316 autoDfa316 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa310 autoDfa315 Bool.and) autoDfa316 autoSrc316 autoDst316 autoNext316
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk310 autoOk315)
  · rfl

def autoExpr317 : AutoF := (.ge ⟨0,-1,1,2⟩)
def autoDfa317 : AutoM Nat := autoPackedTab 0xfaff2abe9a5aa55695 2
def autoSrc317 (i : Fin 4) : AutoLit := (#[(.ge ⟨0,-1,1,2⟩),(.ge ⟨0,-1,1,1⟩),(.ge ⟨0,-1,1,0⟩),(.ge ⟨0,-1,1,-1⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst317 (i : Fin 4) : Nat := autoPacked 0xe4 2 i.val
def autoNext317 (i : Fin 4) (j : Fin 8) : Fin 4 := Fin.ofNat 4 (autoPacked 0xfaffaafaa5aa55a5 2 (8*i.val+j.val))
theorem autoOk317 : autoGood autoExpr317 autoDfa317 0 := by
  apply autoTransfer (N := 3) autoAtom autoDfa317 autoSrc317 autoDst317 autoNext317
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨0,-1,1,2⟩))
  · rfl
