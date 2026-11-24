import PartIAuto
import PartIWord

theorem piWordMark {x : ℕ} (hx : x ≤ 500) :
    (x+508) &&& 512=512*(if 4 ≤ x then 1 else 0) := by
  change (x+508) &&& 2^9=_
  rw [Nat.and_two_pow,Nat.testBit_eq_decide_div_mod_eq]
  norm_num only [Nat.reducePow]
  by_cases h : 4 ≤ x
  · rw [if_pos h,show (x+508)/512=1 by omega]
    decide
  · rw [if_neg h,show (x+508)/512=0 by omega]
    decide

theorem piClampWord {f : ℕ → ℕ} (hf : ∀ i, i<8 → f i ≤ 500) :
    piPackedClamp (piWord 8 f)=piWord 8 (fun i=>min 4 (f i)) := by
  let M := piWord 8 (fun _ => 1)
  let g := fun i => if 4 ≤ f i then (1:ℕ) else 0
  have hg (i) : g i ≤ 1 := by dsimp [g]; split <;> omega
  have h508 : 508*M=piWord 8 (fun _ => 508) := by
    simpa [M] using piWordMul 8 508 (fun _ => 1)
  have h512 : M <<< 9=piWord 8 (fun _ => 512) := by
    rw [Nat.shiftLeft_eq,show 2^9=(512:ℕ) by decide,mul_comm]
    simpa [M] using piWordMul 8 512 (fun _ => 1)
  have hmark : ((piWord 8 f+508*M) &&& (M <<< 9)) >>> 9=piWord 8 g := by
    rw [h508,h512,piWordAdd,piWordAnd (fun i hi => by have := hf i hi; omega)
      (fun i hi => by decide)]
    have e : piWord 8 (fun i => (f i+508) &&& 512)=piWord 8 (fun i => 512*g i) :=
      piWordExt fun i hi => piWordMark (hf i hi)
    rw [e,← piWordMul,Nat.shiftRight_eq_div_pow,show 2^9=(512:ℕ) by decide]
    omega
  have h3 : 3*M=piWord 8 (fun _ => 3) := by
    simpa [M] using piWordMul 8 3 (fun _ => 1)
  have h4 : piWord 8 g <<< 2=piWord 8 (fun i => 4*g i) := by
    rw [Nat.shiftLeft_eq,show 2^2=(4:ℕ) by decide,mul_comm,piWordMul]
  change ((piWord 8 f &&& (3*M-3*(((piWord 8 f+508*M) &&& (M <<< 9)) >>> 9))) |||
    ((((piWord 8 f+508*M) &&& (M <<< 9)) >>> 9) <<< 2))=_
  rw [hmark,h3,piWordMul,piWordSub (fun i hi => by have := hg i; omega),h4]
  have hf' : ∀ i, i<8 → f i<1024 := fun i hi => by have := hf i hi; omega
  rw [piWordAnd hf' (fun i hi => by omega)]
  rw [piWordOr (fun i hi => by
    have := Nat.and_le_left (n:=f i) (m:=3-3*g i)
    have := hf i hi
    omega) (fun i hi => by have := hg i; omega)]
  apply piWordExt
  intro i hi
  by_cases h : 4 ≤ f i
  · simp [g,h,min_eq_left h]
  · have hs : f i &&& 3=f i := by
      change f i &&& (2^2-1)=f i
      rw [Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt (by omega : f i<2^2)]
    simp [g,h,hs,min_eq_right (by omega : f i ≤ 4)]

theorem piSumWord (n : ℕ) (L : List ℕ) (f : ℕ → ℕ → ℕ) :
    (L.map (fun a => piWord n (f a))).sum =
    piWord n (fun i => (L.map (fun a => f a i)).sum) := by
  induction L with
  | nil => simpa using (piWordZero n).symm
  | cons a L ih =>
    simp only [List.map_cons,List.sum_cons,ih,piWordAdd]

theorem piFoldPacked (L : List ℕ) (f : ℕ → ℕ) (init : ℕ) :
    L.foldl (fun acc a => acc+f a) init=init+(L.map f).sum := by
  induction L generalizing init with
  | nil => simp
  | cons a L ih => simp [ih, Nat.add_assoc]

theorem piListSumBound {L : List ℕ} {f : ℕ → ℕ} (hb : ∀ a ∈ L, f a ≤ 4) :
    (L.map f).sum ≤ 4*L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have h0 := hb a (by simp)
    have h1 := ih (fun b h => hb b (by simp [h]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

theorem piStepListDigit (v : ℕ) (L : List ℕ) (hL : L.length ≤ 100)
    (hb : ∀ a ∈ L, ∀ i, i<8 → piDigit (piCol v a) i ≤ 4) {t : ℕ} (ht : t<8) :
    piDigit (piPackedClamp (L.foldl (fun n a => n+piCol v a) 0)) t =
      min 4 ((L.map (fun a => piDigit (piCol v a) t)).sum) := by
  let f := fun a i => piDigit (piCol v a) i
  have recover (a : ℕ) : piCol v a=piWord 8 (f a) := by
    apply Eq.symm
    apply piWordRecover
    exact Nat.mod_lt _ (by decide)
  have hs (i : ℕ) (hi : i<8) : (L.map (fun a=>f a i)).sum ≤ 500 := by
    have := piListSumBound (fun a ha => hb a ha i hi)
    change (L.map (fun a => f a i)).sum ≤ 4*L.length at this
    omega
  rw [piFoldPacked, Nat.zero_add]
  have he : L.map (fun a => piCol v a)=L.map (fun a => piWord 8 (f a)) :=
    List.map_congr_left (fun a _ => recover a)
  rw [he,piSumWord,piClampWord hs]
  exact piBaseDigitWord (fun i hi => by omega) ht

set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
theorem piIncomingSize : ∀ a : Fin 4, ∀ s : Fin 72,
    let L := (piIncoming[a.val]!)[s.val]!
    L.length ≤ 100 ∧ L.all (fun i => decide (i<72)) = true := by decide

theorem piStepDigit (v : ℕ) {a s t : ℕ} (ha : a<4) (hs : s<72) (ht : t<8)
    (hb : ∀ i, i<72 → ∀ j, j<8 → piDigit (piCol v i) j ≤ 4) :
    piDigit (piStepAt v a s) t =
      min 4 ((((piIncoming[a]!)[s]!).map (fun i => piDigit (piCol v i) t)).sum) := by
  let L := (piIncoming[a]!)[s]!
  have h : L.length ≤ 100 ∧ L.all (fun i => decide (i<72)) = true :=
    piIncomingSize ⟨a,ha⟩ ⟨s,hs⟩
  apply piStepListDigit _ _ h.1 _ ht
  intro i hi
  exact hb i (of_decide_eq_true ((List.all_eq_true.mp h.2) i hi))
