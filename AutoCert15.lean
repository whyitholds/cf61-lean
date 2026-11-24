import AutoCert0
import AutoCert7
import AutoCert12
import AutoCert13
import AutoCert14

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def autoExpr215 : AutoF := .neg autoExpr214
def autoDfa215 : AutoM Nat := autoFlip autoDfa214
theorem autoOk215 : autoGood autoExpr215 autoDfa215 0 := (autoGoodNeg _ autoOk214)

def autoExpr216 : AutoF := .con autoExpr6 autoExpr215
def autoDfa216 : AutoM Nat := autoPackedTab 0x222422241989898980984327270242224220986598650222222241984327430222222220436527210436543210 4
def autoSrc216 (i : Fin 14) : Nat × Nat := (autoPacked 0x2b563443440 3 i.val, autoPacked 0x55585765543210 4 i.val)
def autoDst216 (i : Fin 14) : Nat := autoPacked 0x49822276543210 4 i.val
def autoNext216 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0x9999999d999d999dcbcbcbcb9999999a99999999999a999acb4387879d999d99cb65cb65999a999dcb4387439a999a994365872143654321 4 (8*i.val+j.val))
theorem autoOk216 : autoGood autoExpr216 autoDfa216 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa6 autoDfa215 Bool.and) autoDfa216 autoSrc216 autoDst216 autoNext216
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk215)
  · rfl

def autoExpr217 : AutoF := .con autoExpr108 autoExpr167
def autoDfa217 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc217 (i : Fin 5) : Nat × Nat := (autoPacked 0x4688 3 i.val, autoPacked 0x0 1 i.val)
def autoDst217 (i : Fin 5) : Nat := autoPacked 0x0 1 i.val
def autoNext217 (i : Fin 5) (j : Fin 8) : Fin 5 := Fin.ofNat 5 (autoPacked 0x92492492492369a69a9248e4688688 3 (8*i.val+j.val))
theorem autoOk217 : autoGood autoExpr217 autoDfa217 0 := by
  apply autoTransfer (N := 4) (autoCombine autoDfa108 autoDfa167 Bool.and) autoDfa217 autoSrc217 autoDst217 autoNext217
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk108 autoOk167)
  · rfl

def autoExpr218 : AutoF := .disj autoExpr217 autoExpr205
def autoDfa218 : AutoM Nat := autoPackedTab 0x2492494c9249209259241234d3425924903523440 3
def autoSrc218 (i : Fin 6) : Nat × Nat := (autoPacked 0x0 1 i.val, autoPacked 0x2c688 3 i.val)
def autoDst218 (i : Fin 6) : Nat := autoPacked 0x2c688 3 i.val
def autoNext218 (i : Fin 6) (j : Fin 8) : Fin 6 := Fin.ofNat 6 (autoPacked 0x92492592492492592491a69a9649246a4688 3 (8*i.val+j.val))
theorem autoOk218 : autoGood autoExpr218 autoDfa218 0 := by
  apply autoTransfer (N := 5) (autoCombine autoDfa217 autoDfa205 Bool.or) autoDfa218 autoSrc218 autoDst218 autoNext218
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodOr _ _ autoOk217 autoOk205)
  · rfl

def autoExpr219 : AutoF := .neg autoExpr218
def autoDfa219 : AutoM Nat := autoFlip autoDfa218
theorem autoOk219 : autoGood autoExpr219 autoDfa219 0 := (autoGoodNeg _ autoOk218)

def autoExpr220 : AutoF := .con autoExpr6 autoExpr219
def autoDfa220 : AutoM Nat := autoPackedTab 0x666366631878787870666666660636663660875487540666666631873232320666663660325432100 4
def autoSrc220 (i : Fin 11) : Nat × Nat := (autoPacked 0xd5b08688 3 i.val, autoPacked 0x125924688 3 i.val)
def autoDst220 (i : Fin 11) : Nat := autoPacked 0x87636543210 4 i.val
def autoNext220 (i : Fin 11) (j : Fin 8) : Fin 11 := Fin.ofNat 11 (autoPacked 0x66676667a9a9a9a966666668666666676666666667666766a954a95466686667a93232326866676632543210 4 (8*i.val+j.val))
theorem autoOk220 : autoGood autoExpr220 autoDfa220 0 := by
  apply autoTransfer (N := 10) (autoCombine autoDfa6 autoDfa219 Bool.and) autoDfa220 autoSrc220 autoDst220 autoNext220
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk219)
  · rfl

def autoExpr221 : AutoF := .con autoExpr216 autoExpr220
def autoDfa221 : AutoM Nat := autoPackedTab 0x222422241989898980984327270242224220986598650222222241984327430222222220436527210436543210 4
def autoSrc221 (i : Fin 12) : Nat × Nat := (autoPacked 0x982276543210 4 i.val, autoPacked 0x876325432100 4 i.val)
def autoDst221 (i : Fin 12) : Nat := autoPacked 0x982276543210 4 i.val
def autoNext221 (i : Fin 12) (j : Fin 8) : Fin 12 := Fin.ofNat 12 (autoPacked 0x99949994babababa9999999999999998ba43878794999499ba65ba6599999994ba438743999998994365872143654321 4 (8*i.val+j.val))
theorem autoOk221 : autoGood autoExpr221 autoDfa221 0 := by
  apply autoTransfer (N := 11) (autoCombine autoDfa216 autoDfa220 Bool.and) autoDfa221 autoSrc221 autoDst221 autoNext221
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk216 autoOk220)
  · rfl

def autoExpr222 : AutoF := .con autoExpr195 autoExpr221
def autoDfa222 : AutoM Nat := autoPackedTab 0x128d55424924a14a3563092492423495444694688 3
def autoSrc222 (i : Fin 14) : Nat × Nat := (autoPacked 0x224bea94688 3 i.val, autoPacked 0x24987436543210 4 i.val)
def autoDst222 (i : Fin 14) : Nat := autoPacked 0x124ac694688 3 i.val
def autoNext222 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0x2222222d2222222c222c222cbababababa872929222d2224ba8729872c222c22ba65ba6522222224ba872943222222228765292187654321 4 (8*i.val+j.val))
theorem autoOk222 : autoGood autoExpr222 autoDfa222 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa195 autoDfa221 Bool.and) autoDfa222 autoSrc222 autoDst222 autoNext222
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk195 autoOk221)
  · rfl

def autoExpr223 : AutoF := .neg autoExpr195
def autoDfa223 : AutoM Nat := autoFlip autoDfa195
theorem autoOk223 : autoGood autoExpr223 autoDfa223 0 := (autoGoodNeg _ autoOk195)

def autoExpr224 : AutoF := .con autoExpr6 autoExpr223
def autoDfa224 : AutoM Nat := autoPackedTab 0x9b9b9b9b07777777a1777a777a19b76989807777777709b76987609b259b250777a777709b76984307a777a770762598210762543210 4
def autoSrc224 (i : Fin 14) : Nat × Nat := (autoPacked 0x2ab1a683440 3 i.val, autoPacked 0x22497d54688 3 i.val)
def autoDst224 (i : Fin 14) : Nat := autoPacked 0x7ba79876543210 4 i.val
def autoNext224 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0xaaaaaaad9c9c9c9caaaaaaabaaaaaaaaaaabaaab9c769898aaadaaad9c7698769c259c25aaabaaad9c769843abaaabaa7625982176254321 4 (8*i.val+j.val))
theorem autoOk224 : autoGood autoExpr224 autoDfa224 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa6 autoDfa223 Bool.and) autoDfa224 autoSrc224 autoDst224 autoNext224
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk6 autoOk223)
  · rfl

def autoExpr225 : AutoF := .con autoExpr214 autoExpr220
def autoDfa225 : AutoM Nat := autoPackedTab 0x124924c648f5d44924920923d63124934823935444724688 3
def autoSrc225 (i : Fin 15) : Nat × Nat := (autoPacked 0x555885765543210 4 i.val, autoPacked 0x387636325432100 4 i.val)
def autoDst225 (i : Fin 15) : Nat := autoPacked 0x1249a6b24688 3 i.val
def autoNext225 (i : Fin 15) (j : Fin 8) : Fin 15 := Fin.ofNat 15 (autoPacked 0x9999999e999e999edcdcdcdc9999999b9999999a99999999999b999adc4387879e999e99dc65dc65999b999edc4387439b999a994365872143654321 4 (8*i.val+j.val))
theorem autoOk225 : autoGood autoExpr225 autoDfa225 0 := by
  apply autoTransfer (N := 14) (autoCombine autoDfa214 autoDfa220 Bool.and) autoDfa225 autoSrc225 autoDst225 autoNext225
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk214 autoOk220)
  · rfl

def autoExpr226 : AutoF := .con autoExpr224 autoExpr225
def autoDfa226 : AutoM Nat := autoPackedTab 0x124924c648f5d44924920923d63124934823935444724688 3
def autoSrc226 (i : Fin 15) : Nat × Nat := (autoPacked 0x9baa98762543210 4 i.val, autoPacked 0x124dac724688 3 i.val)
def autoDst226 (i : Fin 15) : Nat := autoPacked 0x124dac724688 3 i.val
def autoNext226 (i : Fin 15) (j : Fin 8) : Fin 15 := Fin.ofNat 15 (autoPacked 0x888c888cedededed8888888c8888888b888c888bed87a9a988888888ed87a9878c888c88ed65ed65888c8888ed87a9438c888b888765a92187654321 4 (8*i.val+j.val))
theorem autoOk226 : autoGood autoExpr226 autoDfa226 0 := by
  apply autoTransfer (N := 14) (autoCombine autoDfa224 autoDfa225 Bool.and) autoDfa226 autoSrc226 autoDst226 autoNext226
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk224 autoOk225)
  · rfl

def autoExpr227 : AutoF := .con autoExpr216 autoExpr218
def autoDfa227 : AutoM Nat := autoPackedTab 0x0 1
def autoSrc227 (i : Fin 14) : Nat × Nat := (autoPacked 0x49822276543210 4 i.val, autoPacked 0x24963523440 3 i.val)
def autoDst227 (i : Fin 14) : Nat := autoPacked 0x0 1 i.val
def autoNext227 (i : Fin 14) (j : Fin 8) : Fin 14 := Fin.ofNat 14 (autoPacked 0x9999999d999d999dcbcbcbcb9999999a99999999999a9999cb4387879d999d99cb65cb65999a999dcb4387439a9999994365872143654321 4 (8*i.val+j.val))
theorem autoOk227 : autoGood autoExpr227 autoDfa227 0 := by
  apply autoTransfer (N := 13) (autoCombine autoDfa216 autoDfa218 Bool.and) autoDfa227 autoSrc227 autoDst227 autoNext227
  · apply autoForall; rfl
  · apply autoForall; rfl
  · exact (autoGoodCon _ _ autoOk216 autoOk218)
  · rfl
