import MainModel

open CF61

theorem cfUniqueBijection {P Q : ℕ → Prop} (f g : ℕ → ℕ)
    (hf : ∀ x, P x → Q (f x)) (hg : ∀ x, Q x → P (g x))
    (hl : ∀ x, P x → g (f x) = x) (hr : ∀ x, Q x → f (g x) = x) :
    (∃! x, P x) ↔ ∃! x, Q x := by
  constructor
  · rintro ⟨x,h,u⟩
    refine ⟨f x,hf x h,?_⟩
    intro y hy
    rw [← hr y hy, u (g y) (hg y hy)]
  · rintro ⟨y,h,u⟩
    refine ⟨g y,hg y h,?_⟩
    intro x hx
    rw [← hl x hx, u (f x) (hf x hx)]

def cfEvenMember (P : ℕ → Prop) (t e : ℕ) : Prop :=
  0 < e ∧ e < t ∧ e % 2 = 0 ∧ P e ∧ P (t-e)

theorem cfUniqueEvenMember (P : ℕ → Prop) {t : ℕ} (ht : t%2=1) :
    (∃! v, cfValuePair P t v) ↔ ∃! e, cfEvenMember P t e := by
  let f := fun v : ℕ => if v%2=0 then v else t-v
  let g := fun e : ℕ => min e (t-e)
  apply cfUniqueBijection f g
  · rintro v ⟨hv,hl,p,q⟩
    by_cases he : v%2=0
    · simpa only [f,he,ite_true,cfEvenMember] using
        (show 0 < v ∧ v < t ∧ v%2=0 ∧ P v ∧ P (t-v) from ⟨hv,by omega,he,p,q⟩)
    · simp only [f,he,ite_false,cfEvenMember]
      exact ⟨by omega,by omega,by omega,q,by rwa [show t-(t-v)=v by omega]⟩
  · rintro e ⟨he,hl,ev,p,q⟩
    by_cases h : e ≤ t-e
    · change cfValuePair P t (min e (t-e))
      rw [min_eq_left h]
      exact ⟨he,by omega,p,q⟩
    · change cfValuePair P t (min e (t-e))
      rw [min_eq_right (by omega)]
      exact ⟨by omega,by omega,q,by rwa [show t-(t-e)=e by omega]⟩
  · rintro v ⟨hv,hl,_,_⟩
    by_cases he : v%2=0
    · simp [f,g,he,min_eq_left (le_of_lt hl)]
    · simp [f,g,he,show t-(t-v)=v by omega,min_eq_right (le_of_lt hl)]
  · rintro e ⟨he,hl,ev,_,_⟩
    by_cases h : e ≤ t-e
    · simp [f,g,min_eq_left h,ev]
    · simp [f,g,min_eq_right (show t-e ≤ e by omega),
        show ¬ (t-e)%2=0 by omega,show t-(t-e)=e by omega]

theorem cfSeedEven {m e : ℕ} (he : cfEvenSeed m e) : e%2=0 := by
  rcases he with h|h|h <;> omega

theorem cfEvenModelIff {m e : ℕ} (hm : 3 ≤ m) (he : e%2=0) :
    cfModel m e ↔ cfEvenSeed m e := by
  have hb := cfBFromK m hm
  constructor
  · rintro (h|⟨d,hd,_⟩)
    · exact h
    · omega
  · exact Or.inl

theorem cfOddModelIff {m t : ℕ} (ho : t%2=1) :
    cfModel m t ↔ ∃ d, t = b m + 2*d ∧ cfOffset m d = 1 := by
  constructor
  · rintro (h|h)
    · have := cfSeedEven h
      omega
    · exact h
  · exact Or.inr

theorem cfThreeFlags {a b c u v w : ℕ} (hab : a<b) (hbc : b<c)
    (hu : u ≤ 1) (hv : v ≤ 1) (hw : w ≤ 1) :
    u+v+w=1 ↔ ∃! e, (e=a ∧ u=1) ∨ (e=b ∧ v=1) ∨ (e=c ∧ w=1) := by
  rcases (show u=0 ∨ u=1 by omega) with rfl|rfl <;>
    rcases (show v=0 ∨ v=1 by omega) with rfl|rfl <;>
    rcases (show w=0 ∨ w=1 by omega) with rfl|rfl <;>
    simp [ExistsUnique] <;> grind

theorem cfLagIsOne (eqs : BitsEquations) {m d h : ℕ} (hm : 3 ≤ m)
    (hd : 0 < d) (hh : h ≤ 8*K m) :
    y m (8*K m+d-h)=1 ↔ ∃ j, d=h+j ∧ cfOffset m j=1 := by
  by_cases hle : h ≤ d
  · constructor
    · intro hbit
      exact ⟨d-h,by omega,by simpa [cfOffset,show 8*K m+(d-h)=8*K m+d-h by omega] using hbit⟩
    · rintro ⟨j,he,hbit⟩
      simpa [cfOffset,show 8*K m+d-h=8*K m+j by omega] using hbit
  · rw [(eqs m hm).1 _ (by omega) (by omega)]
    constructor
    · omega
    · rintro ⟨j,hj,_⟩
      omega

theorem cfEvenMemberLag (eqs : BitsEquations) {m d e h : ℕ} (hm : 3 ≤ m)
    (hd : 0 < d) (hh : h ≤ 8*K m) (hp : 0 < h) (he : e=2*h) (hs : cfEvenSeed m e) :
    cfEvenMember (cfModel m) (b m+2*d) e ↔ y m (8*K m+d-h)=1 := by
  have hb := cfBFromK m hm
  have hk := cfKTwo m hm
  rw [cfLagIsOne eqs hm hd hh]
  constructor
  · rintro ⟨_,lt,_,_,ho⟩
    obtain ⟨j,hj,hy⟩ := (cfOddModelIff (show (b m+2*d-e)%2=1 by omega)).1 ho
    exact ⟨j,by omega,hy⟩
  · rintro ⟨j,hj,hy⟩
    exact ⟨by omega,by omega,by omega,Or.inl hs,Or.inr ⟨j,by omega,hy⟩⟩

theorem cfOddRule (eqs : BitsEquations) {m t : ℕ} (hm : 3 ≤ m) (ht : b m<t) (ho : t%2=1) :
    cfModel m t ↔ ∃! v, cfValuePair (cfModel m) t v := by
  have hk := cfKTwo m hm
  have hb := cfBFromK m hm
  obtain ⟨d,rfl⟩ : ∃ d, t=b m+2*d := ⟨(t-b m)/2,by omega⟩
  have hd : 0 < d := by omega
  let n := 8*K m+d
  have hrec := (eqs m hm).2.2 n (by dsimp [n]; omega)
  have comp : cfModel m (b m+2*d) ↔ cfOffset m d=1 := by
    rw [cfOddModelIff ho]
    constructor
    · rintro ⟨j,eq,hj⟩
      rwa [show d=j by omega]
    · exact fun h => ⟨d,rfl,h⟩
  rw [comp,cfUniqueEvenMember _ ho]
  change y m n=1 ↔ _
  rw [hrec]
  let u := y m (n-2)
  let v := y m (n-(4*K m+1))
  let w := y m (n-8*K m)
  have flag : (if u+v+w=1 then (1:ℕ) else 0)=1 ↔ u+v+w=1 := by split <;> simp_all
  rw [show n-4*K m-1=n-(4*K m+1) by omega]
  change (if u+v+w=1 then (1:ℕ) else 0)=1 ↔ _
  rw [flag,cfThreeFlags (a:=4) (b:=8*K m+2) (c:=16*K m) (by omega) (by omega)
    (cfBitAtMost eqs m hm (by dsimp [n]; omega))
    (cfBitAtMost eqs m hm (by dsimp [n]; omega))
    (cfBitAtMost eqs m hm (by dsimp [n]; omega))]
  apply existsUnique_congr
  intro e
  have h1 := cfEvenMemberLag (h:=2) eqs hm hd (by omega) (by omega) (e:=4) (by omega) (Or.inl rfl)
  have h2 := cfEvenMemberLag (h:=4*K m+1) eqs hm hd (by omega) (by omega)
    (e:=8*K m+2) (by omega) (Or.inr (Or.inl rfl))
  have h3 := cfEvenMemberLag (h:=8*K m) eqs hm hd (by omega) (by omega)
    (e:=16*K m) (by omega) (Or.inr (Or.inr rfl))
  constructor
  · rintro (⟨rfl,hu⟩|⟨rfl,hv⟩|⟨rfl,hw⟩)
    · exact h1.2 hu
    · exact h2.2 hv
    · exact h3.2 hw
  · intro hp
    rcases (cfEvenModelIff hm hp.2.2.1).1 hp.2.2.2.1 with he|he|he
    · exact Or.inl ⟨he,h1.1 (he ▸ hp)⟩
    · exact Or.inr (Or.inl ⟨he,h2.1 (he ▸ hp)⟩)
    · exact Or.inr (Or.inr ⟨he,h3.1 (he ▸ hp)⟩)
