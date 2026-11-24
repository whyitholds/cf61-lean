import AutoCert0
import AutoCert3
import AutoCert7
import AutoCert8

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr131 : AutoF := .con autoExpr6 autoExpr130
def autoDfa131 : AutoM Nat := autoPackedTab 0x48120481200340c723c8f01204711cb700d04348a5b4048258482580318c8318c601a066914b500c8318c831806318c6319013410723c87018c6318c63008e4b16e494063190631901339075a88301906318c6300cd3316a48408398a418820 5
def autoSrc131 (i : Fin 21) : Nat × Nat := (autoPacked 0x24ad8d068b443440 3 i.val, autoPacked 0x4ed4a4cb4a94876543210 4 i.val)
def autoDst131 (i : Fin 21) : Nat := autoPacked 0x107b906319ac5a928398a418820 5 i.val
def autoNext131 (i : Fin 21) (j : Fin 8) : Fin 21 := Fin.ofNat 21 (autoPacked 0x2509425094751c724c9325092249727bdef7bdf17bdef7bdf07bdef7bdef7bdf07bdf07510d2296d2512c2512c7bdf17bdf0751cd2296a7c5ef7c5ef7bdf07bdf17510724c877c1ef7c1ef2492c5c9257bdf17bdf1749075a8837c5ef7c1ef734cc5a92141cc520c41 5 (8*i.val+j.val))
theorem autoOk131 : autoGood autoExpr131 autoDfa131 0 := by
  apply autoTransfer (N := 20) (autoCombine autoDfa6 autoDfa130 Bool.and) autoDfa131 autoSrc131 autoDst131 autoNext131
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk130)
  · rfl

def autoExpr132 : AutoF := .con autoExpr106 autoExpr131
def autoDfa132 : AutoM Nat := autoPackedTab 0xdededede0666466641dedcdcbc0666466660de8ade8a06e69d96906466646606e67d7470666666660dc8abc8506666666416c67b9430646666660696a69810676543210 4
def autoSrc132 (i : Fin 24) : Nat × Nat := (autoPacked 0x83c8d539045358b524c8398a418820 5 i.val, autoPacked 0x83cc443968319ac5a928398a418820 5 i.val)
def autoDst132 (i : Fin 24) : Nat := autoPacked 0xe76d6cb4669a698676543210 4 i.val
def autoNext132 (i : Fin 24) (j : Fin 8) : Fin 24 := Fin.ofNat 24 (autoPacked 0xa5e97a5e9775dc7a58967bdef7bdf57bdf07bdf07bdef7bdf3a5e92a4a327bdf07bdef7bdef7bdf07bdef7bdef7bdf57bdf575e6da296da5d2ca5d2c7bdf37bdef75dcda296a7c1ef7c1ef7bdf57bdf375e67a58877d5ef7d5efa492c8c9257bdf37bdf0749078a8837c1ef7bdef734cc5a92141cc520c41 5 (8*i.val+j.val))
theorem autoOk132 : autoGood autoExpr132 autoDfa132 0 := by
  apply autoTransfer (N := 23) (autoCombine autoDfa106 autoDfa131 Bool.and) autoDfa132 autoSrc132 autoDst132 autoNext132
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk106 autoOk131)
  · rfl

def autoExpr133 : AutoF := .con autoExpr49 autoExpr132
def autoDfa133 : AutoM Nat := autoPackedTab 0x24924f349c59c093c9241e49248a6e2cb14c459409249241251240 3
def autoSrc133 (i : Fin 29) : Nat × Nat := (autoPacked 0xa7aa649a498464477654464543210 4 i.val, autoPacked 0xe4c9ee67dd8bcc7b69a9876543210 4 i.val)
def autoDst133 (i : Fin 29) : Nat := autoPacked 0x6f8b249b0b249289251240 3 i.val
def autoNext133 (i : Fin 29) (j : Fin 8) : Fin 29 := Fin.ofNat 29 (autoPacked 0x9de9ca629c318c6318db9de9aa423ab5cd9a2cd99de7ca6298a5e97a5e97318cc318c6b5cd5a1c95318c4318c4318db318c436cc6310c6318c4318c69de7aa4230a5e8fa3e2f35ccea388e318c4318cc318c6318ccb5ed9a2ccb9de4aa610a35cc9a24c9310c6310c6b5ed5a1c87318c6318c69be4a8c105318c6318c433cce6a483310c6330c632cca3250131cc520c41 5 (8*i.val+j.val))
theorem autoOk133 : autoGood autoExpr133 autoDfa133 0 := by
  apply autoTransfer (N := 28) (autoCombine autoDfa49 autoDfa132 Bool.and) autoDfa133 autoSrc133 autoDst133 autoNext133
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk49 autoOk132)
  · rfl

def autoExpr134 : AutoF := .neg autoExpr49
def autoDfa134 : AutoM Nat := autoFlip autoDfa49
theorem autoOk134 : autoGood autoExpr134 autoDfa134 0 := (autoGoodNeg _ autoOk49)

def autoExpr135 : AutoF := .con autoExpr6 autoExpr134
def autoDfa135 : AutoM Nat := autoPackedTab 0xa84d474d099999a990999a999909999999a1999999990484848480a8ad474709a999a990a8c547650999a999a14848b84309a9999990476548610476543210 4
def autoSrc135 (i : Fin 16) : Nat × Nat := (autoPacked 0x4cbb62443440 3 i.val, autoPacked 0xa987474464543210 4 i.val)
def autoDst135 (i : Fin 16) : Nat := autoPacked 0xdacba99876543210 4 i.val
def autoNext135 (i : Fin 16) (j : Fin 8) : Fin 16 := Fin.ofNat 16 (autoPacked 0xe84f474f999a999b9a999b99999b999a9999999b9999999a9999999948484848e8ef47479b999b99e8d54765999b999b4848c8439b999a994765486147654321 4 (8*i.val+j.val))
theorem autoOk135 : autoGood autoExpr135 autoDfa135 0 := by
  apply autoTransfer (N := 15) (autoCombine autoDfa6 autoDfa134 Bool.and) autoDfa135 autoSrc135 autoDst135 autoNext135
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk134)
  · rfl

def autoExpr136 : AutoF := .con autoExpr104 autoExpr131
def autoDfa136 : AutoM Nat := autoPackedTab 0x926b4c1249254a4aa4904ab5a30924924134a6445694688 3
def autoSrc136 (i : Fin 22) : Nat × Nat := (autoPacked 0x6ad6c868b6a96876543210 4 i.val, autoPacked 0x208791cb419ac5a928398a418820 5 i.val)
def autoDst136 (i : Fin 22) : Nat := autoPacked 0x15c9249a995694688 3 i.val
def autoNext136 (i : Fin 22) (j : Fin 8) : Fin 22 := Fin.ofNat 22 (autoPacked 0x9565595655318ce318c8354c794c93318cf318cf9565194611318cf318ce318c6318cf318c6318ce3568d9296d9552c9552c318c8318ce354cd9296a33cc633cc6318c6318c83568794c87318c6318c69452c84525318c8318cf345078288333cc6338c6334cc5a92141cc520c41 5 (8*i.val+j.val))
theorem autoOk136 : autoGood autoExpr136 autoDfa136 0 := by
  apply autoTransfer (N := 21) (autoCombine autoDfa104 autoDfa131 Bool.and) autoDfa136 autoSrc136 autoDst136 autoNext136
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk104 autoOk131)
  · rfl

def autoExpr137 : AutoF := .con autoExpr135 autoExpr136
def autoDfa137 : AutoM Nat := autoPackedTab 0x926b4c1249254a4aa4904ab5a30924924134a6445694688 3
def autoSrc137 (i : Fin 22) : Nat × Nat := (autoPacked 0xdd7c7a88ba948476543210 4 i.val, autoPacked 0x13c954d24b5694688 3 i.val)
def autoDst137 (i : Fin 22) : Nat := autoPacked 0x13c954d24b5694688 3 i.val
def autoNext137 (i : Fin 22) (j : Fin 8) : Fin 22 := Fin.ofNat 22 (autoPacked 0x63d555455563d1454c9463d9454c935ad6b5b16b63d95545515ad6b5ad7053d4f53d4f53d0e5248e5ad6c5ad6b5ad6b5ad6c5ad6b5ad6b5ad6c5ad6c53d4e524895ad6c5ad7063e1454c875b16b5b16b63e45544c55ad705ad6c53d0e6a4835b16b5ad6b51cc5224c141cc520c41 5 (8*i.val+j.val))
theorem autoOk137 : autoGood autoExpr137 autoDfa137 0 := by
  apply autoTransfer (N := 21) (autoCombine autoDfa135 autoDfa136 Bool.and) autoDfa137 autoSrc137 autoDst137 autoNext137
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk135 autoOk136)
  · rfl
