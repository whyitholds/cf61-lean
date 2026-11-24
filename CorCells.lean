import CorPairs
import PartISpec

open CF61

theorem corWidth {m : ℕ} (hm : 3 ≤ m) : 2^(m-1) = 2*K m := by
  rw [show m-1 = (m-2)+1 by omega, pow_succ, K, Nat.mul_comm]

def corKinds (u v : ℕ) : Finset (Fin 6) :=
  if u < v then {0,1,2,3} else if v < u then {0,1,4,5} else {0,1,2}

theorem corMemKinds {u v : ℕ} {i : Fin 6} : i ∈ corKinds u v ↔ PITagOK u v i := by
  rcases lt_trichotomy u v with h | rfl | h
  · rw [corKinds, ite_eq_left h]
    fin_cases i <;> simp [PITagOK] <;> omega
  · simp only [corKinds, lt_self_iff_false, ite_false]
    fin_cases i <;> simp [PITagOK]
  · rw [corKinds, ite_eq_right (by omega), ite_eq_left h]
    fin_cases i <;> simp [PITagOK] <;> omega

def corFibre (p : ℕ × ℕ) : Finset PICell :=
  (corKinds p.1 p.2).map
    ⟨fun i => ⟨p.1,p.2,i⟩, fun _ _ h => congrArg PICell.kind h⟩

theorem corMemFibre {p : ℕ × ℕ} {a : PICell} :
    a ∈ corFibre p ↔ (a.u,a.v) = p ∧ PITagOK p.1 p.2 a.kind := by
  rw [corFibre, Finset.mem_map]
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact ⟨rfl, corMemKinds.mp hi⟩
  · rcases a with ⟨u,v,i⟩
    rintro ⟨rfl,hi⟩
    exact ⟨i,corMemKinds.mpr hi,rfl⟩

def corCells (j : ℕ) : Finset PICell := (corPairs j).biUnion corFibre

theorem corMemCells {m : ℕ} (hm : 3 ≤ m) {a : PICell} :
    a ∈ corCells (m-1) ↔ PIValid (K m) a := by
  rw [corCells, Finset.mem_biUnion]
  constructor
  · rintro ⟨p,hp,ha⟩
    obtain ⟨rfl,hi⟩ := corMemFibre.mp ha
    obtain ⟨hu,hv,hd⟩ := corMemPairs.mp hp
    rw [corWidth hm] at hu hv
    exact ⟨hu,hv,hd,hi⟩
  · rintro ⟨hu,hv,hd,hi⟩
    rw [← corWidth hm] at hu hv
    exact ⟨(a.u,a.v),corMemPairs.mpr ⟨hu,hv,hd⟩,corMemFibre.mpr ⟨rfl,hi⟩⟩

theorem corCellsCard (j : ℕ) : (corCells j).card + 1 = 4*3^j := by
  have hsum : (corCells j).card = ∑ p ∈ corPairs j, (corFibre p).card := by
    apply Finset.card_biUnion
    intro p _ q _ hpq
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact hpq ((corMemFibre.mp hx).1.symm.trans (corMemFibre.mp hy).1)
  have hf (p : ℕ × ℕ) (hp : p ∈ corPairs j) :
      (corFibre p).card + (if p = (0,0) then 1 else 0) = 4 := by
    obtain ⟨u,v⟩ := p
    obtain ⟨_,_,hd⟩ := corMemPairs.mp hp
    simp only [corFibre, Finset.card_map]
    rcases lt_trichotomy u v with h | rfl | h
    · have hn : (u,v) ≠ (0,0) := by rintro hh; obtain ⟨rfl,rfl⟩ := Prod.mk.inj hh; omega
      rw [ite_eq_right hn, corKinds, ite_eq_left h]
      decide
    · have hz : u = 0 := by simpa using hd
      subst u
      decide
    · have hn : (u,v) ≠ (0,0) := by rintro hh; obtain ⟨rfl,rfl⟩ := Prod.mk.inj hh; omega
      rw [ite_eq_right hn, corKinds, ite_eq_right (by omega), ite_eq_left h]
      decide
  have hzero : (0,0) ∈ corPairs j := corMemPairs.mpr ⟨by positivity, by positivity, by decide⟩
  have hone : (∑ p ∈ corPairs j, if p = (0,0) then 1 else 0) = 1 := by simp [hzero]
  rw [hsum, ← hone, ← Finset.sum_add_distrib, Finset.sum_const_nat hf, corPairsCard, Nat.mul_comm]
