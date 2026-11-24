import PartIMoves

abbrev PILiftKey := ℕ × (Fin 3 × Fin 3)
abbrev PILiftEntry := Sigma (fun _ : PILiftKey => PIQuad)

def piLiftBucket (k a v j e s : ℕ) :=
  piLowBucket k a v j e (s/18) (s/9%2) (s/3%3) (s%3)

theorem piLiftMem (k a v j e s : ℕ) (q : PIQuad) :
    q ∈ piLiftBucket k a v j e s ↔
      ((q.1.1 < k ∧ q.1.2 < k) ∧ (q.2.1 < k ∧ q.2.2 < k)) ∧
      piLowPred k a v j e (s/18) (s/9%2) (s/3%3) (s%3) q := by
  simp only [piLiftBucket,piLowBucket,piLowGrid,Finset.mem_filter,Finset.mem_product,Finset.mem_range]

theorem piLiftCmpBound (u v : ℕ) : piCmp u v < 3 := by
  unfold piCmp
  split <;> (try split) <;> decide

theorem piLiftCmpUpBound {f : ℕ} (hf : f < 3) (u v : ℕ) : piCmpUp f u v < 3 := by
  unfold piCmpUp
  split
  · exact hf
  · exact piLiftCmpBound _ _

theorem piLiftDigits (x : Fin 3) : piHU x ≤ 1 ∧ piHV x ≤ 1 ∧ piHU x &&& piHV x = 0 := by
  fin_cases x <;> decide

theorem piLiftMove {s sn l : ℕ} (hsn : sn < 72) (hl : l < 4) (x y : Fin 3) :
    (s,(x,y)) ∈ piMoveSet l sn ↔
      s < 72 ∧
      s/18 + piHU x + piHU y = l/2 + 2*(sn/18) ∧
      s/9%2 + piHV x + piHV y = l%2 + 2*(sn/9%2) ∧
      piCmpUp (s/3%3) (piHU x) (piHV x) = sn/3%3 ∧
      piCmpUp (s%3) (piHU y) (piHV y) = sn%3 := by
  obtain ⟨hx,hx',_⟩ := piLiftDigits x
  obtain ⟨hy,hy',_⟩ := piLiftDigits y
  have hf := piLiftCmpUpBound (Nat.mod_lt (s/3) (by decide : 0 < 3)) (piHU x) (piHV x)
  have hg := piLiftCmpUpBound (Nat.mod_lt s (by decide : 0 < 3)) (piHU y) (piHV y)
  have raw : (s,(x,y)) ∈ piMoveSet l sn ↔ s < 72 ∧ piNextLetter s x y=l ∧ piNextCol s x y=sn := by
    unfold piMoveSet
    rw [Finset.mem_filter,Finset.mem_product,Finset.mem_range]
    simp only [Finset.mem_univ,and_true]
  rw [raw]
  unfold piNextLetter piNextCol
  omega

def piLiftCode (u v : ℕ) : Fin 3 := if u=1 then 1 else if v=1 then 2 else 0

theorem piLiftCodeBits (u v : ℕ) (hu : u < 2) (hv : v < 2) (hd : u &&& v = 0) :
    piHU (piLiftCode u v) = u ∧ piHV (piLiftCode u v) = v := by
  interval_cases u <;> interval_cases v <;> first | decide | exact False.elim ((by decide : ¬((1:ℕ) &&& 1=0)) hd)

theorem piLiftCodeH (x : Fin 3) : piLiftCode (piHU x) (piHV x) = x := by
  fin_cases x <;> decide

theorem piLiftMod (k u h : ℕ) (hu : u < k) : (u+k*h)%k = u := by
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hu]

theorem piLiftDiv (k u h : ℕ) (hk : 0 < k) (hu : u < k) : (u+k*h)/k = h := by
  rw [Nat.add_mul_div_left _ _ hk,Nat.div_eq_of_lt hu,zero_add]

theorem piLiftBoth (k u v h i : ℕ) (hu : u < k) (hv : v < k) (E : u+k*h=v+k*i) :
    u=v ∧ h=i := by
  have hk : 0 < k := by omega
  have lo := congrArg (fun n => n % k) E
  have hi := congrArg (fun n => n / k) E
  simpa only [piLiftMod _ _ _ hu,piLiftMod _ _ _ hv,piLiftDiv _ _ _ hk hu,piLiftDiv _ _ _ hk hv] using And.intro lo hi

theorem piLiftBitAnd (d u v : ℕ) :
    u &&& v = 0 ↔
    (u%2^d) &&& (v%2^d)=0 ∧ (u/2^d) &&& (v/2^d)=0 := by
  rw [← Nat.and_mod_two_pow,← Nat.and_div_two_pow]
  constructor
  · intro h; simp [h]
  · rintro ⟨h,h'⟩
    have e := Nat.mod_add_div (u &&& v) (2^d)
    simpa only [h,h',Nat.mul_zero,zero_add] using e.symm

theorem piLiftAndJoin (k d u v : ℕ) (hk : k=2^d) (hu : u<k) (hv : v<k)
    (hd : u &&& v=0) (x : Fin 3) : (u+k*piHU x) &&& (v+k*piHV x)=0 := by
  have e := (piLiftBitAnd d (u+k*piHU x) (v+k*piHV x)).2
  rw [← hk] at e
  apply e
  have hp : 0 < k := by omega
  simpa only [piLiftMod _ _ _ hu,piLiftMod _ _ _ hv,piLiftDiv _ _ _ hp hu,piLiftDiv _ _ _ hp hv] using
    And.intro hd (piLiftDigits x).2.2

theorem piLiftCmpJoin (k u v : ℕ) (hu : u<k) (hv : v<k) (x : Fin 3) :
    piCmp (u+k*piHU x) (v+k*piHV x) = piCmpUp (piCmp u v) (piHU x) (piHV x) := by
  fin_cases x <;> norm_num [piHU,piHV,piCmpUp,piCmp] <;> split_ifs <;> omega

theorem piLiftColumn (k a u w j U W b c : ℕ) (hk : 0 < k) (ha : a < k)
    (he : (u+k*U)+(w+k*W)+j=(a+k*b)+2*k*c) :
    u+w+j=a+k*((u+w+j)/k) ∧ (u+w+j)/k+U+W=b+2*c := by
  have eh := Nat.mod_add_div (u+w+j) k
  have eq : (u+w+j)%k+k*((u+w+j)/k+U+W)=a+k*(b+2*c) := by nlinarith only [eh,he]
  have h := piLiftBoth _ _ _ _ _ (Nat.mod_lt _ hk) ha eq
  exact ⟨by omega,h.2⟩

def piLiftPack (c b f g : ℕ) := 18*c+9*b+3*f+g

theorem piLiftPackRead {c b f g : ℕ} (hc : c<4) (hb : b<2) (hf : f<3) (hg : g<3) :
    piLiftPack c b f g < 72 ∧ piLiftPack c b f g /18=c ∧ piLiftPack c b f g /9%2=b ∧
      piLiftPack c b f g /3%3=f ∧ piLiftPack c b f g %3=g := by
  unfold piLiftPack
  omega

theorem piLiftPackBack (s : ℕ) : piLiftPack (s/18) (s/9%2) (s/3%3) (s%3)=s := by
  unfold piLiftPack
  omega
