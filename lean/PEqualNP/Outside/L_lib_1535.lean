import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1535_aux
abbrev Hue := Fin 3
abbrev Assign (k : Nat) := Fin k → Bool
abbrev H (k : Nat) := Fin k ⊕ (Assign k × (Fin (k+1) ⊕ (Fin k × Bool)))
abbrev V (k : Nat) := Hue ⊕ (Fin k ⊕ H k)
def pal (z : Hue) : V k := .inl z
def term (i : Fin k) : V k := .inr (.inl i)
def inv (i : Fin k) : V k := .inr (.inr (.inl i))
def acc (a : Assign k) (j : Fin (k+1)) : V k := .inr (.inr (.inr (a,.inl j)))
def aux (a : Assign k) (i : Fin k) (s : Bool) : V k := .inr (.inr (.inr (a,.inr (i,s))))
def lit (a : Assign k) (i : Fin k) := if a i then inv i else term i
def bit (b : Bool) : Hue := if b then 1 else 0
def tri (x y z s t : Hue) := x≠s ∧ y≠t ∧ s≠t ∧ s≠z ∧ t≠z
instance (x y z s t : Hue) : Decidable (tri x y z s t) := by unfold tri;infer_instance
theorem triOr : ∀ a b : Bool,∃ s t : Hue, tri (bit a) (bit b) (bit (a || b)) s t := by decide +kernel
theorem triZero : ∀ z s t,tri 0 0 z s t → z=0 := by decide +kernel
theorem forceZero : ∀ z : Hue,z≠1 → z≠2 → z=0 := by decide +kernel
theorem forceOne : ∀ z : Hue,z≠0 → z≠2 → z=1 := by decide +kernel
theorem opposite : ∀ b z,z≠(2:Hue) → bit b≠z → z=bit (!b) := by decide +kernel
inductive edge (R : Finset (Assign k)) : V k → V k → Prop
  | palette (a b : Hue) (h : a≠b) : edge R (pal a) (pal b)
  | boolean (i : Fin k) : edge R (term i) (pal 2)
  | invBool (i : Fin k) : edge R (inv i) (pal 2)
  | different (i : Fin k) : edge R (term i) (inv i)
  | startOne (a : Assign k) : edge R (acc a 0) (pal 1)
  | startTwo (a : Assign k) : edge R (acc a 0) (pal 2)
  | finish (a : Assign k) (forbid : a∉R) : edge R (acc a (Fin.last k)) (pal 0)
  | prev (a : Assign k) (i : Fin k) : edge R (acc a i.castSucc) (aux a i false)
  | curr (a : Assign k) (i : Fin k) : edge R (lit a i) (aux a i true)
  | across (a : Assign k) (i : Fin k) : edge R (aux a i false) (aux a i true)
  | outF (a : Assign k) (i : Fin k) : edge R (aux a i false) (acc a i.succ)
  | outT (a : Assign k) (i : Fin k) : edge R (aux a i true) (acc a i.succ)
theorem distinct {R : Finset (Assign k)} {u v} (h : edge R u v) : u≠v := by
  cases h <;> simp_all [pal,term,inv,acc,aux,lit,ite_eq_iff]
def adj (R : Finset (Assign k)) (u v) := edge R u v ∨ edge R v u
theorem symmAdj (R : Finset (Assign k)) : Symmetric (adj R) := fun _ _ h => h.symm
theorem irrAdj (R : Finset (Assign k)) (v) : ¬adj R v v := fun h => h.elim (fun e => distinct e rfl) (fun e => distinct e rfl)
end PEqualNP.Outside.L_lib_1535_aux

namespace PEqualNP.Outside.L_lib_1535_aux
theorem decode {R : Finset (Assign k)} {x : Assign k} {c : V k → Hue}
    (proper : ∀u v,edge R u v → c u≠c v) (rail : ∀a,c (pal a)=a)
    (value : ∀i,c (term i)=bit (x i)) : x∈R := by
  by_contra bad
  have neg (i) : c (inv i)=bit (!(x i)) := by
    apply opposite <;> first | simpa only [rail] using proper _ _ (.invBool i) | simpa only [value] using proper _ _ (.different i)
  have zero (i) : c (lit x i)=0 := by cases h : x i <;> simp [lit,h,neg,value,bit]
  have accZero (j : Fin (k+1)) : c (acc x j)=0 := by
    induction j using Fin.induction with
    | zero => apply forceZero <;> first | simpa only [rail] using proper _ _ (.startOne x) | simpa only [rail] using proper _ _ (.startTwo x)
    | succ i ih =>
      apply triZero _ (c (aux x i false)) (c (aux x i true))
      exact ⟨ih ▸ proper _ _ (.prev x i),zero i ▸ proper _ _ (.curr x i),
        proper _ _ (.across x i),proper _ _ (.outF x i),proper _ _ (.outT x i)⟩
  have no := proper _ _ (.finish x bad)
  rw [accZero,rail] at no
  exact no rfl
def miss (x a : Bool) := if a then !x else x
theorem missIff : ∀x a,miss x a=true ↔ x≠a := by decide +kernel
def seen (x a : Assign k) (j : Nat) := decide (∃ i : Fin k,i.val<j ∧ x i≠a i)
theorem seenStart (x a : Assign k) : seen x a 0=false := by simp [seen]
theorem seenNext (x a : Assign k) (i : Fin k) : seen x a (i.val+1)=(seen x a i.val || miss (x i) (a i)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [seen,Bool.or_eq_true,decide_eq_true_eq,missIff]
  constructor
  · rintro ⟨j,le,ne⟩;by_cases h : j=i
    · subst j;exact Or.inr ne
    · exact Or.inl ⟨j,by have v : j.val≠i.val := fun e => h (Fin.ext e);omega,ne⟩
  · rintro (⟨j,lt,ne⟩|ne)
    · exact ⟨j,by omega,ne⟩
    · exact ⟨i,by omega,ne⟩
theorem seenEnd {x a : Assign k} (h : x≠a) : seen x a k=true := by
  apply decide_eq_true
  by_contra! none;exact h (funext (fun i => none i i.isLt))
end PEqualNP.Outside.L_lib_1535_aux

namespace PEqualNP.Outside.L_lib_1535_aux
noncomputable def first (b d : Bool) := Classical.choose (triOr b d)
noncomputable def second (b d : Bool) := Classical.choose (Classical.choose_spec (triOr b d))
theorem works (b d : Bool) : tri (bit b) (bit d) (bit (b || d)) (first b d) (second b d) :=
  Classical.choose_spec (Classical.choose_spec (triOr b d))
noncomputable def assignColor (x : Assign k) : V k → Hue
  | .inl z => z
  | .inr (.inl i) => bit (x i)
  | .inr (.inr (.inl i)) => bit (!(x i))
  | .inr (.inr (.inr (a,.inl j))) => bit (seen x a j.val)
  | .inr (.inr (.inr (a,.inr (i,s)))) =>
    if s then second (seen x a i.val) (miss (x i) (a i))
    else first (seen x a i.val) (miss (x i) (a i))
theorem litColor (x a : Assign k) (i : Fin k) : assignColor x (lit a i)=bit (miss (x i) (a i)) := by
  cases h : a i <;> simp [lit,h,miss,inv,term,assignColor]
theorem realizeColor {R : Finset (Assign k)} {x : Assign k} (hx : x∈R) {u v} (ed : edge R u v) :
    assignColor x u≠assignColor x v := by
  cases ed with
  | palette a b ne => exact ne
  | boolean i => cases h : x i <;> simp [assignColor,term,pal,bit,h]
  | invBool i => cases h : x i <;> simp [assignColor,inv,pal,bit,h]
  | different i => cases h : x i <;> simp [assignColor,inv,term,bit,h]
  | startOne a => simp [assignColor,acc,pal,seenStart,bit]
  | startTwo a => simp [assignColor,acc,pal,seenStart,bit]
  | finish a bad =>
    have ne : x≠a := fun h => bad (h ▸ hx)
    simp [assignColor,acc,pal,seenEnd ne,bit]
  | prev a i => exact (works (seen x a i.val) (miss (x i) (a i))).1
  | curr a i => rw [litColor];exact (works _ _).2.1
  | across a i => exact (works _ _).2.2.1
  | outF a i =>
    change first _ _ ≠ bit (seen x a (i.val+1))
    rw [seenNext];exact (works _ _).2.2.2.1
  | outT a i =>
    change second _ _ ≠ bit (seen x a (i.val+1))
    rw [seenNext];exact (works _ _).2.2.2.2
end PEqualNP.Outside.L_lib_1535_aux

open PEqualNP.Outside.L_lib_1535_aux in
theorem PEqualNP.Outside.L_lib_1535 : ∀ (k : Nat) (R : Finset (Fin k → Bool)),
  ∃ h : Nat,
    let V := Fin 3 ⊕ (Fin k ⊕ Fin h)
    ∃ Adj : V → V → Prop, Symmetric Adj ∧ (∀ v, ¬ Adj v v) ∧
      (∀ a b : Fin 3, a ≠ b → Adj (Sum.inl a) (Sum.inl b)) ∧
      (∀ i : Fin k, Adj (Sum.inr (Sum.inl i)) (Sum.inl 2)) ∧
      ∀ x : Fin k → Bool, x ∈ R ↔
        ∃ col : V → Fin 3,
          (∀ u v, Adj u v → col u ≠ col v) ∧
          (∀ a : Fin 3, col (Sum.inl a) = a) ∧
          ∀ i : Fin k, col (Sum.inr (Sum.inl i)) = if x i then 1 else 0 := by
  classical
  intro k R
  let h := Fintype.card (H k)
  let e : V k ≃ (Fin 3 ⊕ (Fin k ⊕ Fin h)) := Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin (H k)))
  let relation := fun u v => adj R (e.symm u) (e.symm v)
  refine ⟨h,relation,fun _ _ z => symmAdj R z,fun v => irrAdj R _,?_,?_,?_⟩
  · intro a b ne;exact Or.inl (.palette a b ne)
  · intro i;exact Or.inl (.boolean i)
  · intro x;constructor
    · intro hx;refine ⟨fun v => assignColor x (e.symm v),?_,fun _ => rfl,fun _ => rfl⟩
      intro u v eq;rcases eq with ed|ed
      · exact realizeColor hx ed
      · exact (realizeColor hx ed).symm
    · rintro ⟨c,valid,anchors,values⟩
      apply decode (c:=fun u => c (e u)) _ anchors values
      intro u v ed;apply valid
      change adj R (e.symm (e u)) (e.symm (e v))
      simpa only [Equiv.symm_apply_apply] using (show adj R u v from Or.inl ed)
