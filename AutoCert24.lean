import AutoCert0
import AutoCert6
import AutoCert8
import AutoCert20
import AutoCert21
import AutoCert23

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr340 : AutoF := (.ge ⟨-6,0,1,1⟩)
def autoDfa340 : AutoM Nat := autoPackedTab 0xebaeba11c71c611475d4471f5d0d75d751aeb1c61145144b0c2289 3
def autoSrc340 (i : Fin 8) : AutoLit := (#[(.ge ⟨-6,0,1,1⟩),(.ge ⟨-6,0,1,0⟩),(.ge ⟨-6,0,1,-3⟩),(.ge ⟨-6,0,1,-2⟩),(.ge ⟨-6,0,1,-5⟩),(.ge ⟨-6,0,1,-1⟩),(.ge ⟨-6,0,1,-4⟩),(.ge ⟨-6,0,1,-6⟩)] : Array AutoLit)[i.val]?.getD default
def autoDst340 (i : Fin 8) : Nat := autoPacked 0xfac688 3 i.val
def autoNext340 (i : Fin 8) (j : Fin 8) : Fin 8 := Fin.ofNat 8 (autoPacked 0xebaeba8e38e3451d758e3ebad75d75d758e3451451618451 3 (8*i.val+j.val))
theorem autoOk340 : autoGood autoExpr340 autoDfa340 0 := by
  apply autoTransfer (N := 7) autoAtom autoDfa340 autoSrc340 autoDst340 autoNext340
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoLitGood (.ge ⟨-6,0,1,1⟩))
  · rfl

def autoExpr341 : AutoF := .con autoExpr6 autoExpr340
def autoDfa341 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc341 (i : Fin 17) : Nat × Nat := (autoPacked 0x492c96468b440 3 i.val, autoPacked 0x1eaeae361a288 3 i.val)
def autoDst341 (i : Fin 17) : Nat := autoPacked 0x0 1 i.val
def autoNext341 (i : Fin 17) (j : Fin 8) : Fin 17 := Fin.ofNat 17 (autoPacked 0x741d0741d07b9ee7b9ee62d8b4a128741d062d8d4a1284a128741d062d8b62d8b62d8d4a1287b9ee62d8b62d8b62d8d62d8d398e620c836358b6358b62d8d4a12a20c8320c836358b4a92820c4120c41398a020c41 5 (8*i.val+j.val))
theorem autoOk341 : autoGood autoExpr341 autoDfa341 0 := by
  apply autoTransfer (N := 16) (autoCombine autoDfa6 autoDfa340 Bool.and) autoDfa341 autoSrc341 autoDst341 autoNext341
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk340)
  · rfl

def autoExpr342 : AutoF := .con autoExpr339 autoExpr341
def autoDfa342 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc342 (i : Fin 6) : Nat × Nat := (autoPacked 0x2c688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst342 (i : Fin 6) : Nat := autoPacked 0x0 1 i.val
def autoNext342 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592569a69a964964688688 3 (8*i.val+j.val))
theorem autoOk342 : autoGood autoExpr342 autoDfa342 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa339 autoDfa341 Bool.and) autoDfa342 autoSrc342 autoDst342 autoNext342
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk339 autoOk341)
  · rfl

def autoExpr343 : AutoF := .con autoExpr342 autoExpr99
def autoDfa343 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc343 (i : Fin 1) : Nat × Nat := (autoPacked 0x0 1 i.val, autoPacked 0x0 1 i.val)
def autoDst343 (i : Fin 1) : Nat := autoPacked 0x0 1 i.val
def autoNext343 (i : Fin 1) (j : Fin 8) : Fin 1 := Fin.ofNat 1 (autoPacked 0x0 1 (8*i.val+j.val))
theorem autoOk343 : autoGood autoExpr343 autoDfa343 0 := by
  apply autoTransfer (N := 0) (autoCombine autoDfa342 autoDfa99 Bool.and) autoDfa343 autoSrc343 autoDst343 autoNext343
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk342 autoOk99)
  · rfl

def autoExpr344 : AutoF := .disj autoExpr337 autoExpr343
def autoDfa344 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc344 (i : Fin 1) : Nat × Nat := (autoPacked 0x0 1 i.val, autoPacked 0x0 1 i.val)
def autoDst344 (i : Fin 1) : Nat := autoPacked 0x0 1 i.val
def autoNext344 (i : Fin 1) (j : Fin 8) : Fin 1 := Fin.ofNat 1 (autoPacked 0x0 1 (8*i.val+j.val))
theorem autoOk344 : autoGood autoExpr344 autoDfa344 0 := by
  apply autoTransfer (N := 0) (autoCombine autoDfa337 autoDfa343 Bool.or) autoDfa344 autoSrc344 autoDst344 autoNext344
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk337 autoOk343)
  · rfl

def autoExpr345 : AutoF := .disj autoExpr292 autoExpr344
def autoDfa345 : AutoM Nat := autoPackedTab 0x49249c4968d3418612d024e24904b46b409249241843448 3
def autoSrc345 (i : Fin 7) : Nat × Nat := (autoPacked 0x1ac688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst345 (i : Fin 7) : Nat := autoPacked 0x1ac688 3 i.val
def autoNext345 (i : Fin 7) (j : Fin 8) : Fin 7 := Fin.ofNat 7 (autoPacked 0x24924e25a34d30c25a24e24925a35a249249308689 3 (8*i.val+j.val))
theorem autoOk345 : autoGood autoExpr345 autoDfa345 0 := by
  apply autoTransfer (N := 6) (autoCombine autoDfa292 autoDfa344 Bool.or) autoDfa345 autoSrc345 autoDst345 autoNext345
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk292 autoOk344)
  · rfl

def autoExpr346 : AutoF := .con autoExpr119 autoExpr345
def autoDfa346 : AutoM Nat := autoPackedTab 0x49249c4968d3418612d024e24904b46b409249241843448 3
def autoSrc346 (i : Fin 12) : Nat × Nat := (autoPacked 0xaac4d3440 3 i.val, autoPacked 0xd49263448 3 i.val)
def autoDst346 (i : Fin 12) : Nat := autoPacked 0xd49263448 3 i.val
def autoNext346 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0x8888888b67436a6a8888888988888888676767678889888865656743888b888867436a43898888886721672165204321 4 (8*i.val+j.val))
theorem autoOk346 : autoGood autoExpr346 autoDfa346 0 := by
  apply autoTransfer (N := 11) (autoCombine autoDfa119 autoDfa345 Bool.and) autoDfa346 autoSrc346 autoDst346 autoNext346
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk119 autoOk345)
  · rfl

def autoExpr347 : AutoF := .disj autoExpr329 autoExpr346
def autoDfa347 : AutoM Nat := autoPackedTab 0x63358681a003190a33ccf019c6718cd600c6320c63202633586835803188332ccb018c8519e85010a318cf32406318c6319013390742883018c6318c6300ce315ac3180631906318c03188332c83018c6319063010a3190a32408398a418820 5
def autoSrc347 (i : Fin 18) : Nat × Nat := (autoPacked 0xaa9683387653433210 4 i.val, autoPacked 0x298d6a49843448 3 i.val)
def autoDst347 (i : Fin 18) : Nat := autoPacked 0x20f735885a928398a418820 5 i.val
def autoNext347 (i : Fin 18) (j : Fin 8) : Fin 18 := Fin.ofNat 18 (autoPacked 0x319cd344d13190a340d033ccf319cd318cc318c8319cd345cd318c6318cc3188332ccb3190a3410a428c6340c9318c6318c833d0742883318c6318c633cc5734c6318cc318c63188332c83318c6320c6428c6428c941cc520c41 5 (8*i.val+j.val))
theorem autoOk347 : autoGood autoExpr347 autoDfa347 0 := by
  apply autoTransfer (N := 17) (autoCombine autoDfa329 autoDfa346 Bool.or) autoDfa347 autoSrc347 autoDst347 autoNext347
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk329 autoOk346)
  · rfl

def autoExpr348 : AutoF := .neg autoExpr347
def autoDfa348 : AutoM Nat := autoFlip autoDfa347
theorem autoOk348 : autoGood autoExpr348 autoDfa348 0 := (autoGoodNeg _ autoOk347)

def autoExpr349 : AutoF := .con autoExpr6 autoExpr348
def autoDfa349 : AutoM Nat := autoPackedTab 0x73d9074dd3039e853a4e901d1745cf6400e7b20e9b20073dcf73dcf0318c2318c205cf20dcd7340c6318c6318073ccb73ccb039e853a485010a32dd23240c6308c6318074507428830308c6308c601d13159032c0c6318c6308173c83734830308c6318c6010a32d0a32408398a418820 5
def autoSrc349 (i : Fin 23) : Nat × Nat := (autoPacked 0x9269356c083443440 3 i.val, autoPacked 0x41ee6b0c65990632928398a418820 5 i.val)
def autoDst349 (i : Fin 23) : Nat := autoPacked 0x4e51641ee6918c5a928398a418820 5 i.val
def autoNext349 (i : Fin 23) (j : Fin 8) : Fin 23 := Fin.ofNat 23 (autoPacked 0x8467285a168450a8561585214846726318d6318d8467285a7284611846116318e6318e8448383e0f6318c6318e6318c6318d6318c6318c844cb844cb8450a8550a428cb854c96318e6318d85107428836398c6398c850c59c8cb6318d6318e8448383c836398c6358c428cb428c941cc520c41 5 (8*i.val+j.val))
theorem autoOk349 : autoGood autoExpr349 autoDfa349 0 := by
  apply autoTransfer (N := 22) (autoCombine autoDfa6 autoDfa348 Bool.and) autoDfa349 autoSrc349 autoDst349 autoNext349
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk348)
  · rfl

def autoExpr350 : AutoF := .con autoExpr308 autoExpr349
def autoDfa350 : AutoM Nat := autoPackedTab 0x1cd5bdd17440e83a0e6ade07356f7456f02d6b22d6b205cd735cd7340e69068621805ad6b5ad6b039a6539a6501cd425094240b5ac8b5ad60741074248302c8b5ac8b581d03156f3280b5ad6b5ac81734834308302c8b5ad6b581093290910408398a418820 5
def autoSrc350 (i : Fin 28) : Nat × Nat := (autoPacked 0xb97b4ba4b87a9358721436543210 4 i.val, autoPacked 0x992516418e7b9a46296851928398a418820 5 i.val)
def autoDst350 (i : Fin 28) : Nat := autoPacked 0x8ad305bd6e6a1845a54848828398a418820 5 i.val
def autoNext350 (i : Fin 28) (j : Fin 8) : Fin 28 := Fin.ofNat 28 (autoPacked 0xa4ef6a6e9b7bdef7bdfaa4d0e96659a6298a4ef67bdf57bdf5a4ef6a6ef67bdef7bdf57bdf07bdf0a4e93a4e937bdf07bdfaa4c83946517bdef7bdf07bdef7bdefa4d0e9650ea4ccda4ccd7bdf07bdefa4d0e9658b7c1ef7e9ef438cd965497bdf07bdf5a610762c837c1ef7c1efa60c5bd8cd7bdf57bdf0a4c83944837c1ef7bdef438cd62d4941cc520c41 5 (8*i.val+j.val))
theorem autoOk350 : autoGood autoExpr350 autoDfa350 0 := by
  apply autoTransfer (N := 27) (autoCombine autoDfa308 autoDfa349 Bool.and) autoDfa350 autoSrc350 autoDst350 autoNext350
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk308 autoOk349)
  · rfl
