import Mathlib
import PEqualNP.Defs
import PEqualNP.Library.Helpers.GraphSampleDistance

namespace PEqualNP.Outside.L_meta_53216_aux
open scoped Classical
variable {α : Type} [DecidableEq α]
abbrev Row (α : Type) := Finset α
theorem notBoth {B x : Row α} (ne : B.Nonempty) (l : Disjoint x B) : ¬ B⊆x := by
  obtain ⟨a,ha⟩ := ne;exact fun h => Finset.disjoint_left.mp l (h ha) ha
theorem loErase (x B : Row α) : Disjoint (x\B) B := Finset.sdiff_disjoint
theorem recover {B x : Row α} (h : Disjoint x B) : (x∪B)\B=x := Finset.union_sdiff_cancel_right h
theorem restore {B x : Row α} (h : B⊆x) : x\B∪B=x := Finset.sdiff_union_of_subset h
theorem high (x B : Row α) : B⊆x∪B := Finset.subset_union_right
theorem pairsSum (S : Finset (Row α)) (B : Row α) (ne : B.Nonempty)
    (closed : ∀x,Disjoint x B → (x∈S ↔ x∪B∈S)) (f : Row α → ℕ) :
    S.sum f=(S.filter (fun x => Disjoint x B)).sum (fun x => f x+f (x∪B))+
      (S.filter (fun x => ¬Disjoint x B ∧ ¬B⊆x)).sum f := by
  classical
  let L := S.filter (fun x => Disjoint x B)
  let H := S.filter (fun x => B⊆x)
  let R := S.filter (fun x => ¬Disjoint x B ∧ ¬B⊆x)
  have hi : H=L.image (fun x => x∪B) := by
    ext x;simp only [H,L,Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨inside,h⟩; have eq := restore h
      exact ⟨x\B,⟨(closed _ (loErase _ _)).mpr (by rwa [eq]),loErase _ _⟩,eq⟩
    · rintro ⟨y,⟨inside,h⟩,rfl⟩;exact ⟨(closed _ h).mp inside,high _ _⟩
  have hl : Disjoint L H := Finset.disjoint_left.mpr (fun x h k => notBoth ne (Finset.mem_filter.mp h).2 (Finset.mem_filter.mp k).2)
  have hr : Disjoint (L∪H) R := by
    apply Finset.disjoint_left.mpr;intro x h k;rcases Finset.mem_union.mp h with l|u
    · exact (Finset.mem_filter.mp k).2.1 (Finset.mem_filter.mp l).2
    · exact (Finset.mem_filter.mp k).2.2 (Finset.mem_filter.mp u).2
  have decomp : (L∪H)∪R=S := by ext x;simp [L,H,R];tauto
  have inj : Set.InjOn (fun x : Row α => x∪B) L := by
    intro x hx y hy h
    simpa only [recover (Finset.mem_filter.mp hx).2,recover (Finset.mem_filter.mp hy).2] using congrArg (fun t : Row α => t\B) h
  change S.sum f=L.sum _+R.sum f
  calc
    S.sum f = ((L∪H)∪R).sum f := by rw [decomp]
    _ = (L.sum f+H.sum f)+R.sum f := by rw [Finset.sum_union hr,Finset.sum_union hl]
    _ = _ := by rw [hi,Finset.sum_image inj,Finset.sum_add_distrib]
theorem pairCompare (S : Finset (Row α)) (B : Row α) (ne : B.Nonempty)
    (closed : ∀x,Disjoint x B → (x∈S ↔ x∪B∈S)) (f g : Row α → ℕ)
    (pairs : ∀x∈S,Disjoint x B → f x+f (x∪B) ≤ g x+g (x∪B))
    (other : ∀x∈S,¬Disjoint x B → ¬ B⊆x → f x≤g x) : S.sum f ≤ S.sum g := by
  rw [pairsSum S B ne closed f,pairsSum S B ne closed g];apply Nat.add_le_add
  · apply Finset.sum_le_sum; intro x h;exact pairs x (Finset.mem_filter.mp h).1 (Finset.mem_filter.mp h).2
  · apply Finset.sum_le_sum; intro x h;obtain ⟨h,a,b⟩ := Finset.mem_filter.mp h;exact other x h a b
noncomputable def sortW (B : Row α) (w : Row α → Nat) (x : Row α) :=
  if Disjoint x B then max (w x) (w (x∪B)) else if B⊆x then min (w (x\B)) (w x) else w x
theorem lowValue (B : Row α) (w : Row α → ℕ) {x} (l : Disjoint x B) :
    sortW B w x=max (w x) (w (x∪B)) := by simp [sortW,l]
theorem highValue (B : Row α) (ne : B.Nonempty) (w : Row α → ℕ) {x} (l : Disjoint x B) :
    sortW B w (x∪B)=min (w x) (w (x∪B)) := by
  have h := high x B
  have n : ¬Disjoint (x∪B) B := fun d => notBoth ne d h
  simp [sortW,n,h,recover l]
theorem outsideValue (B : Row α) (w : Row α → ℕ) {x} (h : ¬Disjoint x B) (n : ¬B⊆x) :
    sortW B w x=w x := by simp [sortW,h,n]
end PEqualNP.Outside.L_meta_53216_aux

namespace PEqualNP.Outside.L_meta_53216_aux
open scoped Classical
variable {α : Type} [DecidableEq α] [Fintype α]
def lowSet (C : Row α) := Finset.univ.filter (fun x : Row α => Disjoint x C)
def overlap (C : Row α) (w : Row α → Nat) := (lowSet C).sum (fun x => min (w x) (w (x∪C)))
def sortedAt (C : Row α) (w : Row α → Nat) := ∀x,Disjoint x C → w (x∪C) ≤ w x
theorem switch (x B C : Row α) : x∪B∪C=x∪C∪B := by ext a;simp;tauto
theorem sameLow (x : Row α) {B C : Row α} (bc : Disjoint B C) : Disjoint (x∪C) B ↔ Disjoint x B := by simp [Finset.disjoint_union_left,bc.symm]
theorem sameHigh (x : Row α) {B C : Row α} (bc : Disjoint B C) : B⊆x∪C ↔ B⊆x := by
  constructor
  · intro h a ha;rcases Finset.mem_union.mp (h ha) with hx|hc
    · exact hx
    · exact (Finset.disjoint_left.mp bc ha hc).elim
  · intro h;exact h.trans Finset.subset_union_left
theorem erasedUnion (x : Row α) {B C : Row α} (bc : Disjoint B C) : (x∪C)\B=x\B∪C := by
  rw [Finset.union_sdiff_distrib,Finset.sdiff_eq_self_of_disjoint bc.symm]
theorem sortsSelf (B : Row α) (ne : B.Nonempty) (w : Row α → Nat) : sortedAt B (sortW B w) := by
  intro x l;rw [highValue _ ne _ l,lowValue _ _ l];omega
theorem keepsSorted {B C : Row α} (bc : Disjoint B C) (w : Row α → Nat) (h : sortedAt C w) :
    sortedAt C (sortW B w) := by
  intro x lc
  have up := h x lc
  by_cases lb : Disjoint x B
  · have up' := h (x∪B) (by simp [Finset.disjoint_union_left,lc,bc])
    rw [lowValue _ _ ((sameLow _ bc).mpr lb),lowValue _ _ lb,switch x C B]
    omega
  by_cases hb : B⊆x
  · have l : Disjoint (x\B) C := Finset.disjoint_of_subset_left Finset.sdiff_subset lc
    have up' := h (x\B) l
    simp only [sortW,sameLow x bc,lb,sameHigh x bc,hb,ite_true,ite_false,erasedUnion x bc]
    omega
  · simpa only [sortW,sameLow x bc,lb,sameHigh x bc,hb,ite_false] using up
theorem overlapSelf (B : Row α) (ne : B.Nonempty) (w : Row α → Nat) : overlap B w=overlap B (sortW B w) := by
  unfold overlap;apply Finset.sum_congr rfl
  intro x hx;have d := (Finset.mem_filter.mp hx).2
  rw [lowValue _ _ d,highValue _ ne _ d];omega
theorem overlapGrows {B C : Row α} (ne : B.Nonempty) (bc : Disjoint B C) (w : Row α → Nat) :
    overlap C w ≤ overlap C (sortW B w) := by
  apply pairCompare (lowSet C) B ne
  · intro x _;simp [lowSet,Finset.disjoint_union_left,bc]
  · intro x _ lb
    have lb' := (sameLow x bc).mpr lb
    simp only [lowValue _ _ lb,lowValue _ _ lb',highValue _ ne _ lb,switch x B C,highValue _ ne _ lb']
    omega
  · intro x _ lb hb
    have lb' : ¬Disjoint (x∪C) B := fun z => lb ((sameLow x bc).mp z)
    have hb' : ¬ B⊆x∪C := fun z => hb ((sameHigh x bc).mp z)
    simp only [outsideValue _ _ lb hb,outsideValue _ _ lb' hb',le_refl]
end PEqualNP.Outside.L_meta_53216_aux

namespace PEqualNP.Outside.L_meta_53216_aux
open scoped Classical
abbrev Word (n : ℕ) := Finset (Fin n)
def block (color : Fin n → Fin c) (j : Fin c) := Finset.univ.filter (fun i => color i=j)
theorem inBlock (color : Fin n → Fin c) (a : Fin n) (j : Fin c) : a∈block color j ↔ color a=j := by simp [block]
theorem blocksApart (color : Fin n → Fin c) {j k : Fin c} (ne : j≠k) : Disjoint (block color j) (block color k) := by
  apply Finset.disjoint_left.mpr;intro a hj hk;exact ne (((inBlock _ _ _).mp hj).symm.trans ((inBlock _ _ _).mp hk))
theorem blockNe {color : Fin n → Fin c} (onto : Function.Surjective color) (j) : (block color j).Nonempty := by
  obtain ⟨a,h⟩ := onto j;exact ⟨a,(inBlock _ _ _).mpr h⟩
noncomputable def norm (color : Fin n → Fin c) (x : Word n) := x.filter (fun i => ¬ block color (color i) ⊆ x)
theorem normPair (color : Fin n → Fin c) (j : Fin c) {x : Word n} (l : Disjoint x (block color j)) :
    norm color (x∪block color j)=norm color x := by
  ext i; by_cases s : color i=j
  · have no : i∉x := fun hi => Finset.disjoint_left.mp l hi ((inBlock _ _ _).mpr s)
    simp [norm,s,no,high]
  · have absent : i∉block color j := by simpa only [inBlock] using s
    have eq : block color (color i) ⊆ x∪block color j ↔ block color (color i) ⊆ x := by
      constructor
      · intro h a ha;rcases Finset.mem_union.mp (h ha) with hx|hj
        · exact hx
        · exact (Finset.disjoint_left.mp (blocksApart color s) ha hj).elim
      · intro h;exact h.trans Finset.subset_union_left
    simp only [norm,Finset.mem_filter,Finset.mem_union,absent,or_false,eq]
noncomputable def zMass (color : Fin n → Fin c) (w : Word n → Nat) (z : Word n) := (Finset.univ.filter (fun x => norm color x=z)).sum w
theorem sortMass {color : Fin n → Fin c} (onto : Function.Surjective color) (j) (w : Word n → Nat) :
    zMass color (sortW (block color j) w) = zMass color w := by
  funext z
  let B := block color j
  let S := Finset.univ.filter (fun x => norm color x=z)
  have cl (x : Word n) (l : Disjoint x B) : x∈S ↔ x∪B∈S := by simp [S,B,normPair color j l]
  change S.sum (sortW B w)=S.sum w
  rw [pairsSum S B (blockNe onto j) cl (sortW B w),pairsSum S B (blockNe onto j) cl w]
  congr 1
  · apply Finset.sum_congr rfl;intro x hx;have l := (Finset.mem_filter.mp hx).2
    rw [lowValue _ _ l,highValue _ (blockNe onto j) _ l];dsimp only [B];omega
  · apply Finset.sum_congr rfl;intro x hx;have h := (Finset.mem_filter.mp hx).2
    exact outsideValue _ _ h.1 h.2
end PEqualNP.Outside.L_meta_53216_aux

namespace PEqualNP.Outside.L_meta_53216_aux
open scoped Classical
def val (f : Word n → Bool) (x : Word n) : Int := (f x).toNat
def delta (color : Fin n → Fin c) (f : Word n → Bool) (j : Fin c) := val f (block color j)-val f ∅
def regular (color : Fin n → Fin c) (f : Word n → Bool) := ∀ j x, Disjoint x (block color j) →
    val f (x∪block color j)-val f x=delta color f j
theorem constantReg (color : Fin n → Fin c) (b : Bool) : regular color (fun _ => b) := by simp [regular,val,delta]
def pin (a : Fin n) (x : Word n) := decide (a∈x)
theorem twoReg (color : Fin n → Fin c) (a b : Fin n) (eqc : color a=color b) (p : Bool → Bool → Bool) :
    regular color (fun x => p (pin a x) (pin b x)) := by
  intro j x lo;by_cases u : color a=j
  · have v := eqc.symm.trans u
    have ha := (inBlock color a j).mpr u;have hb := (inBlock color b j).mpr v
    have na : a∉x := fun z => Finset.disjoint_left.mp lo z ha
    have nb : b∉x := fun z => Finset.disjoint_left.mp lo z hb
    simp [delta,val,pin,ha,hb,na,nb]
  · have v : color b≠j := fun z => u (eqc.trans z)
    have ha : a∉block color j := by simpa only [inBlock] using u
    have hb : b∉block color j := by simpa only [inBlock] using v
    simp [delta,val,pin,ha,hb]
theorem edgeColors {color : Fin n → Fin c} (E : Finset (Fin n × Fin n))
    (part : ∀Z : Word n,(∀e∈E,e.1∈Z ↔ e.2∈Z) ↔ ∀i j,color i=color j → (i∈Z ↔ j∈Z))
    {e : Fin n × Fin n} (he : e∈E) : color e.1=color e.2 := by
  let B := block color (color e.2)
  have h := (part B).mpr (by intro i j eq; simp [B,inBlock,eq])
  exact (inBlock _ _ _).mp ((h e he).mpr ((inBlock _ _ _).mpr rfl))
theorem differenceNorm {color : Fin n → Fin c} (onto : Function.Surjective color)
    {f g : Word n → Bool} (rf : regular color f) (rg : regular color g)
    (same : delta color f=delta color g) (x : Word n) :
    val f x-val g x=val f (norm color x)-val g (norm color x) := by
  induction x using Finset.strongInductionOn
  rename_i x ih
  by_cases found : ∃ j,block color j⊆x
  · obtain ⟨j,sub⟩ := found
    let B := block color j
    let y := x\B
    have low : Disjoint y B := loErase _ _
    have up : y∪B=x := restore sub
    have lt : y ⊂ x := by
      apply Finset.ssubset_iff_subset_ne.mpr;refine ⟨Finset.sdiff_subset,?_⟩
      intro eq; have h : Disjoint x B := eq ▸ low
      exact notBoth (blockNe onto j) h sub
    have h := ih y lt
    have normEq := normPair color j low; rw [show y∪block color j=x from up] at normEq
    have hf := rf j y low; have hg := rg j y low
    rw [show y∪block color j=x from up] at hf hg
    rw [show delta color f j=delta color g j from congrFun same j] at hf
    rw [normEq];omega
  · have unchanged : norm color x=x := by ext a;simp [norm,show ∀j,¬block color j⊆x from not_exists.mp found]
    rw [unchanged]
end PEqualNP.Outside.L_meta_53216_aux

namespace PEqualNP.Outside.L_meta_53216_aux
open scoped Classical
noncomputable def distance (w : Word n → Nat) (f g : Word n → Bool) :=
  (Finset.univ.filter (fun x => f x≠g x)).sum w
theorem distanceNorm {color : Fin n → Fin c} (onto : Function.Surjective color)
    {f g : Word n → Bool} (rf : regular color f) (rg : regular color g)
    (same : delta color f=delta color g) (w : Word n → ℕ) : distance (zMass color w) f g=distance w f g := by
  classical
  have nz (a b : Bool) : (a.toNat : Int)-b.toNat ≠ 0 ↔ a≠b := by cases a <;> cases b <;> decide
  have agree (x : Word n) : f (norm color x)≠g (norm color x) ↔ f x≠g x := by
    rw [←nz,←nz]; exact (not_congr (congrArg (·=0) (differenceNorm onto rf rg same x)).to_iff).symm
  unfold distance zMass
  rw [Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x;simp [agree]
theorem distanceFlip {color : Fin n → Fin c} (onto : Function.Surjective color)
    {f g : Word n → Bool} (rf : regular color f) (rg : regular color g)
    (j : Fin c) (diff : delta color f j≠delta color g j) (w : Word n → ℕ) :
    overlap (block color j) w ≤ distance w f g := by
  classical
  let B := block color j
  let a (x : Word n) := if Disjoint x B then min (w x) (w (x∪B)) else 0
  let b (x : Word n) := if f x≠g x then w x else 0
  have c : Finset.univ.sum a ≤ Finset.univ.sum b := by
    apply pairCompare Finset.univ B (blockNe onto _) (by simp)
    · intro x _ l
      have hit : f x≠g x ∨ f (x∪B)≠g (x∪B) := by
        by_contra! h
        have v := rf j x l; have z := rg j x l
        change val f (x∪B)-val f x=_ at v
        change val g (x∪B)-val g x=_ at z
        unfold val at v z; rw [h.1,h.2] at v; exact diff (v.symm.trans z)
      have nl : ¬Disjoint (x∪B) B := fun k => notBoth (blockNe onto j) k (high _ _)
      simp only [a,l,nl,ite_true,ite_false,Nat.add_zero,b]
      rcases hit with hit|hit <;> simp [hit]
    · intro x _ l _;simp [a,l]
  simpa only [a,b,←Finset.sum_filter,overlap,lowSet,distance,B] using c
end PEqualNP.Outside.L_meta_53216_aux

namespace PEqualNP.Outside.L_meta_53216_aux
theorem compress {color : Fin n → Fin c} (onto : Function.Surjective color) (w : Word n → Nat) :
    ∃v : Word n → Nat, zMass color v=zMass color w ∧ (∀j,sortedAt (block color j) v) ∧
      ∀j,overlap (block color j) w ≤ overlap (block color j) v := by
  classical
  have sweep (J : Finset (Fin c)) :
      ∃v : Word n → Nat, zMass color v=zMass color w ∧ (∀ j∈J,sortedAt (block color j) v) ∧
        ∀ j,overlap (block color j) w ≤ overlap (block color j) v := by
    induction J using Finset.induction_on with
    | empty => exact ⟨w,rfl,by simp,fun _ => le_rfl⟩
    | @insert j J nj ih =>
      obtain ⟨v,z,s,g⟩ := ih
      refine ⟨sortW (block color j) v,(sortMass onto j v).trans z,?_,?_⟩
      · intro k h; rcases Finset.mem_insert.mp h with rfl|hk
        · exact sortsSelf _ (blockNe onto _) _
        · exact keepsSorted (blocksApart color (show j ≠ k from fun eq => nj (eq.symm ▸ hk))) _ (s k hk)
      · intro k;apply (g k).trans;by_cases h : j=k
        · subst k;exact (overlapSelf _ (blockNe onto j) _).le
        · exact overlapGrows (blockNe onto _) (blocksApart color h) _
  obtain ⟨v,z,s,g⟩ := sweep Finset.univ;exact ⟨v,z,fun j => s j (Finset.mem_univ _),g⟩
end PEqualNP.Outside.L_meta_53216_aux

namespace PEqualNP.Outside.L_meta_53216_aux
open scoped Classical
open GraphInversionSeeds GraphSampleDistance
theorem asInj : Function.Injective (@asWord n) := by
  intro f g eq;funext s
  let x := Finset.univ.filter (fun i => s i=true)
  have read : (fun i => decide (i∈x))=s := by funext i;cases h : s i <;> simp [x,h]
  have h := congrFun eq x
  unfold asWord at h
  convert h using 1 <;> rw [←read]
theorem fromPins {color : Fin n → Fin c} (a b : Fin n) (eq : color a=color b) (p : Bool → Bool → Bool) :
    regular color (asWord (fun x => p (x a) (x b))) := by
  have e : asWord (fun x => p (x a) (x b)) = (fun x => p (pin a x) (pin b x)) := by
    funext x;unfold asWord pin;congr 1
  rw [e];exact twoReg color a b eq p
theorem targetReg {color : Fin n → Fin c} (E : Finset (Edge n)) (part : GraphPriceCalibration.classes E color)
    (f : F n) (hf : f∈target E) : regular color (asWord f) := by
  simp only [target,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and] at hf
  rcases hf with ((⟨i,rfl⟩|⟨e,he,rfl⟩)|⟨e,he,rfl⟩)|⟨e,he,rfl⟩
  · exact fromPins i i rfl (fun a _ => !a)
  · exact fromPins e.1 e.2 (edgeColors E part he) (fun a b => !a && !b)
  · exact fromPins e.1 e.2 (edgeColors E part he) (fun a b => a && !b)
  · exact fromPins e.1 e.2 (edgeColors E part he) (fun a b => !a && b)
theorem rawReg {color : Fin n → Fin c} (E : Finset (Edge n)) (part : GraphPriceCalibration.classes E color)
    (f : F n) (hf : f∈raw E) : regular color (asWord f) := by
  simp only [raw,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_image,Finset.mem_univ,true_and] at hf
  rcases hf with (((rfl|rfl)|⟨i,rfl⟩)|⟨e,he,rfl⟩)|⟨e,he,rfl⟩
  · exact constantReg color false
  · exact constantReg color true
  · exact fromPins i i rfl (fun a _ => a)
  · exact fromPins e.1 e.2 (edgeColors E part he) (fun a b => a==b)
  · exact fromPins e.1 e.2 (edgeColors E part he) xor
end PEqualNP.Outside.L_meta_53216_aux

namespace PEqualNP.Outside.L_meta_53216_aux
open scoped Classical
open GraphInversionSeeds GraphSampleDistance
def valid (E : Finset (Edge n)) (color : Fin n → Fin c) (D : Nat) (w : Word n → Nat) :=
  ∀ lost : Word n → Nat, (∑x,lost x)<D → keeps (Finset.univ.filter (fun x => lost x<w x)) E color
noncomputable def fullGap (w : Word n → Nat) (f g : Word n → Bool) :=
  (Finset.univ.filter (fun x => f x≠g x)).sum w
theorem fullCriterion (E : Finset (Edge n)) (color : Fin n → Fin c)
    (sorted : ∀e∈E,e.1<e.2) (onto : Function.Surjective color) (part : GraphPriceCalibration.classes E color)
    (w : Word n → Nat) (D : Nat) :
    valid E color D w ↔ (∀ j,D≤overlap (block color j) w) ∧
    (∀ f∈target E,∀g∈target E,f≠g → D≤fullGap w (asWord f) (asWord g)) ∧
    ∀ f∈target E,∀g∈raw E,D≤fullGap w (asWord f) (asWord g) := by
  classical
  cases D with
  | zero => simp [valid]
  | succ d =>
    let A := Finset.univ.filter (fun x => 0<w x)
    have mem (x) : x∈A ↔ 0<w x := by simp [A]
    let gap (f g : F n) := (A.filter (fun x => asWord f x≠asWord g x)).sum w
    have h := GraphSampleDistance.criterion n c E color onto sorted part A w d (fun x hx => (mem x).mp hx)
    change (∀ lost : Word n → Nat, A.sum lost≤d → keeps (A.filter (fun x => lost x<w x)) E color) ↔
      (∀ j,d<(A.filter (fun x => Disjoint x (block color j) ∧ x∪block color j∈A)).sum
        (fun x => min (w x) (w (x∪block color j)))) ∧
      (∀f∈target E,∀g∈target E,f≠g → d<gap f g) ∧ ∀f∈target E,∀g∈raw E,d<gap f g at h
    have geq (f g) : gap f g=fullGap w (asWord f) (asWord g) := by
      simp only [gap,fullGap,A,Finset.sum_filter]
      apply Finset.sum_congr rfl;intro x _
      by_cases hx : 0<w x
      · simp [hx]
      · have z : w x=0 := by omega
        simp [z]
    have oeq (j) : (A.filter (fun x => Disjoint x (block color j) ∧ x∪block color j∈A)).sum
        (fun x => min (w x) (w (x∪block color j))) = overlap (block color j) w := by
      simp only [mem,A,overlap,lowSet,Finset.sum_filter]
      apply Finset.sum_congr rfl;intro x _
      by_cases hx : 0<w x
      · by_cases hy : 0<w (x∪block color j)
        · simp [hx,hy]
        · have z : w (x∪block color j)=0 := by omega
          simp [hx,z]
      · have z : w x=0 := by omega
        simp [z]
    simp only [oeq,geq] at h
    apply Iff.trans _ h
    constructor
    · intro good lost cost
      let cut (x : Word n) := if x∈A then lost x else 0
      have bill : (∑x,cut x)=A.sum lost := by
        simp only [cut,←Finset.sum_filter]
        congr 1;ext x;simp
      have same : Finset.univ.filter (fun x => cut x<w x) = A.filter (fun x => lost x<w x) := by
        ext x;by_cases hx : x∈A
        · simp [cut,hx]
        · have z : w x=0 := by have := (mem x).not.mp hx;omega
          simp [cut,hx,z]
      rw [←same];exact good cut (by omega)
    · intro good lost cost
      have bill : A.sum lost≤∑x,lost x := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      have same : A.filter (fun x => lost x<w x)=Finset.univ.filter (fun x => lost x<w x) := by
        ext x;simp only [Finset.mem_filter,Finset.mem_univ,true_and,mem];omega
      rw [←same];exact good lost (by omega)
end PEqualNP.Outside.L_meta_53216_aux

namespace PEqualNP.Outside.L_meta_53216_aux
open scoped Classical
open GraphInversionSeeds GraphSampleDistance
noncomputable def inputs (E : Finset (Edge n)) := (raw E).image asWord
def compare (E : Finset (Edge n)) (color : Fin n → Fin c) (f g : Word n → Bool) :=
  f∈req E ∧ (g∈inputs E ∨ (g∈req E ∧ f≠g)) ∧ delta color f=delta color g
theorem exactCriterion (E : Finset (Edge n)) (color : Fin n → Fin c)
    (sorted : ∀e∈E,e.1<e.2) (onto : Function.Surjective color) (part : GraphPriceCalibration.classes E color)
    (w : Word n → Nat) (D : Nat) : valid E color D w ↔
    (∀j,D≤overlap (block color j) w) ∧ ∀f g,compare E color f g → D≤distance (zMass color w) f g := by
  classical
  rw [fullCriterion E color sorted onto part]
  constructor
  · rintro ⟨axes,tt,tr⟩;refine ⟨axes,?_⟩
    rintro _ g ⟨ft,hg,same⟩
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp ft
    rcases hg with hr|⟨ht,ne⟩
    · obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hr
      rw [distanceNorm onto (targetReg E part f hf) (rawReg E part g hg) same];exact tr f hf g hg
    · obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp ht
      rw [distanceNorm onto (targetReg E part f hf) (targetReg E part g hg) same]
      exact tt f hf g hg (fun eq => ne (congrArg asWord eq))
  · rintro ⟨axes,all⟩
    have bound (f g : Word n → Bool) (ft : f∈req E) (gg : g∈inputs E ∨ (g∈req E ∧ f≠g))
        (rf : regular color f) (rg : regular color g) : D≤distance w f g := by
      by_cases same : delta color f=delta color g
      · rw [←distanceNorm onto rf rg same]; exact all f g ⟨ft,gg,same⟩
      · obtain ⟨j,ne⟩ : ∃j,delta color f j≠delta color g j := by
          by_contra! h;exact same (funext h)
        exact (axes j).trans (distanceFlip onto rf rg j ne w)
    refine ⟨axes,?_,?_⟩
    · intro f hf g hg ne;apply bound _ _ (Finset.mem_image_of_mem _ hf)
        (Or.inr ⟨Finset.mem_image_of_mem _ hg,fun eq => ne (asInj eq)⟩)
        (targetReg E part f hf) (targetReg E part g hg)
    · intro f hf g hg;apply bound _ _ (Finset.mem_image_of_mem _ hf)
        (Or.inl (Finset.mem_image_of_mem _ hg)) (targetReg E part f hf) (rawReg E part g hg)
theorem highSum {B : Word n} {v : Word n → Nat} (s : sortedAt B v) :
    overlap B v = (lowSet B).sum (fun x => v (x∪B)) := by
  apply Finset.sum_congr rfl;intro x hx;exact min_eq_right (s x (Finset.mem_filter.mp hx).2)
theorem realize (E : Finset (Edge n)) (color : Fin n → Fin c)
    (sorted : ∀e∈E,e.1<e.2) (onto : Function.Surjective color) (part : GraphPriceCalibration.classes E color)
    (M : Word n → Nat) (D : Nat) : (∃w,zMass color w=M ∧ valid E color D w) ↔
    (∀ f g, compare E color f g → D≤distance M f g) ∧
    ∃ v,zMass color v=M ∧ (∀j,sortedAt (block color j) v) ∧
      ∀j,D≤(lowSet (block color j)).sum (fun x => v (x∪block color j)) := by
  constructor
  · rintro ⟨w,hm,hv⟩
    obtain ⟨axes,cmp⟩ := (exactCriterion E color sorted onto part w D).mp hv
    obtain ⟨v,eq,sv,up⟩ := compress onto w
    rw [hm] at cmp
    refine ⟨cmp,v,eq.trans hm,sv,?_⟩
    intro j;rw [←highSum (sv j)];exact (axes j).trans (up j)
  · rintro ⟨cmp,v,hm,sv,hv⟩
    refine ⟨v,hm,(exactCriterion E color sorted onto part v D).mpr ⟨?_,?_⟩⟩
    · intro j;rw [highSum (sv j)];exact hv j
    · rwa [hm]
end PEqualNP.Outside.L_meta_53216_aux

namespace PEqualNP.Outside.L_meta_53216_aux
noncomputable def chooseF {α : Type*} (P : α → Prop) (A : Finset α) := @Finset.filter α P (fun _ => Classical.propDecidable _) A
theorem normFilter {α : Type*} (P : α → Prop) (d : DecidablePred P) (A : Finset α) : @Finset.filter α P d A=chooseF P A := by
  ext j; simp only [chooseF,Finset.mem_filter]
def allRows (n : ℕ) : Finset (Word n) := Finset.univ
theorem anyUniverse (n : ℕ) (h : Fintype (Word n)) : @Finset.univ (Word n) h=allRows n := by
  ext x;simp [allRows]
def merged (x y : Word n) := x∪y
theorem anyUnion (d : DecidableEq (Fin n)) (x y : Word n) :
    (letI : DecidableEq (Fin n) := d; x∪y)=merged x y := by
  ext i;simp only [merged,Finset.mem_union]
end PEqualNP.Outside.L_meta_53216_aux
open PEqualNP PEqualNP.Outside.L_meta_53216_aux in
theorem PEqualNP.Outside.L_meta_53216 : ∀ (n c : Nat) (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c),
  (∀ e ∈ E, e.1 < e.2) → Function.Surjective color →
  (∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
    ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z)) →
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let W := Finset (Fin n)
  let bit := fun (i : Fin n) (x : W) => decide (i ∈ x)
  let neg := fun (i : Fin n) (x : W) => !(bit i x)
  let same := fun (e : Fin n × Fin n) (x : W) => bit e.1 x == bit e.2 x
  let raw : Finset (W → Bool) := {fun _ => false,fun _ => true} ∪ Finset.univ.image bit ∪
    E.image same ∪ E.image (fun e x => !(same e x))
  let need := Finset.univ.image neg ∪ E.image (fun e x => neg e.1 x && neg e.2 x) ∪
    E.image (fun e x => bit e.1 x && neg e.2 x) ∪ E.image (fun e x => neg e.1 x && bit e.2 x)
  let keeps := fun A : Finset W => ∀ (S : W) (p : Nat),
    let L := (raw ∪ S.image neg).toList
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length C ∧
      C.output < L.length+C.size ∧ C.size ≤ p ∧ ∀ f ∈ need, ∃ j < L.length+C.size,
        ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = f x) ↔
    (∀ j, ∃ i ∈ S, color i = j) ∧ n+3*E.card-S.card ≤ p
  let valid := fun (D : Nat) (w : W → Nat) =>
    ∀ lost : W → Nat, (∑ x, lost x) < D →
      keeps (Finset.univ.filter (fun x => lost x < w x))
  let comp := fun j : Fin c => Finset.univ.filter (fun i : Fin n => color i = j)
  let norm := fun x : W => x.filter (fun i => ¬ comp (color i) ⊆ x)
  let delta := fun (f : W → Bool) (j : Fin c) =>
    ((f (comp j)).toNat : Int) - ((f ∅).toNat : Int)
  let canonMass := fun (w : W → Nat) (z : W) =>
    (Finset.univ.filter (fun x : W => norm x = z)).sum w
  let comparable := fun (f g : W → Bool) =>
    f ∈ need ∧ (g ∈ raw ∨ (g ∈ need ∧ f ≠ g)) ∧ delta f = delta g
  let dist := fun (M : W → Nat) (f g : W → Bool) =>
    (Finset.univ.filter (fun z : W => f z ≠ g z)).sum M
  let low := fun j : Fin c => Finset.univ.filter (fun x : W => Disjoint x (comp j))
  let overlap := fun (w : W → Nat) (j : Fin c) =>
    (low j).sum (fun x => min (w x) (w (x ∪ comp j)))
  let sorted := fun w : W → Nat => ∀ j, ∀ x ∈ low j, w (x ∪ comp j) ≤ w x
  (∀ (w : W → Nat) (D : Nat), valid D w ↔
    (∀ j, D ≤ overlap w j) ∧ ∀ f g, comparable f g → D ≤ dist (canonMass w) f g) ∧
  (∀ w : W → Nat, ∃ v : W → Nat, canonMass v = canonMass w ∧ sorted v ∧
    ∀ j, overlap w j ≤ overlap v j) ∧
  ∀ (M : W → Nat) (D : Nat), (∃ w : W → Nat, canonMass w = M ∧ valid D w) ↔
    (∀ f g, comparable f g → D ≤ dist M f g) ∧
    ∃ v : W → Nat, canonMass v = M ∧ sorted v ∧
      ∀ j, D ≤ (low j).sum (fun x => v (x ∪ comp j)) := by
  classical
  intro n c E color edges onto part
  intro W' bit' neg' same' raw' need' keeps' valid' comp' norm' delta' mass' comparable' dist' low' overlap' sorted'
  have bitEq (i : Fin n) (x : W') : bit' i x=GraphSeedSamples.bit i x := by
    dsimp only [bit',GraphSeedSamples.bit]; congr 1
  have negEq (i : Fin n) : neg' i=GraphSeedSamples.inv i := by
    funext x; by_cases h : i∈x <;> simp [neg',bit',GraphSeedSamples.inv,h]
  have sameEq (e : Fin n × Fin n) : same' e=GraphSeedSamples.same e := by
    funext x; by_cases h : e.1∈x <;> by_cases k : e.2∈x <;> simp [same',bit',GraphSeedSamples.same,h,k]
  have valEq (i : Fin n) (x : W') (dec : Decidable (i∈x)) : @decide _ dec=bit' i x := by
    dsimp only [bit']; congr 1
  have valN (i : Fin n) : GraphSampleDistance.asWord (GraphInversionSeeds.neg i)=(fun x => !bit' i x) := by
    funext x
    dsimp only [GraphSampleDistance.asWord,GraphInversionSeeds.neg]
    simp only [valEq]
  have valZ (e : Fin n × Fin n) : GraphSampleDistance.asWord (GraphInversionSeeds.zz e)=(fun x => !bit' e.1 x && !bit' e.2 x) := by
    funext x
    dsimp only [GraphSampleDistance.asWord,GraphInversionSeeds.zz]
    simp only [valEq]
  have valO (e : Fin n × Fin n) : GraphSampleDistance.asWord (GraphInversionSeeds.oz e)=(fun x => bit' e.1 x && !bit' e.2 x) := by
    funext x
    dsimp only [GraphSampleDistance.asWord,GraphInversionSeeds.oz]
    simp only [valEq]
  have valT (e : Fin n × Fin n) : GraphSampleDistance.asWord (GraphInversionSeeds.zo e)=(fun x => !bit' e.1 x && bit' e.2 x) := by
    funext x
    dsimp only [GraphSampleDistance.asWord,GraphInversionSeeds.zo]
    simp only [valEq]
  have reqEq : GraphSampleDistance.req E=need' := by
    ext f
    simp only [GraphSampleDistance.req,GraphInversionSeeds.target,Finset.image_union,
      Finset.image_image,Function.comp_def,Finset.mem_union,Finset.mem_image,
      Finset.mem_univ,true_and,need',neg',valN,valZ,valO,valT]
  have keepEq (A : Finset W') : keeps' A ↔ GraphSampleDistance.keeps A E color := by
    unfold keeps' GraphSampleDistance.keeps
    apply forall_congr'; intro S
    apply forall_congr'; intro p
    dsimp only
    generalize hl : Finset.toList _ = actual
    have eq : actual=GraphSampleDistance.wire E S := by
      rw [←hl]
      congr 1
      ext f
      simp only [raw',GraphSeedSamples.bank,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
        Finset.mem_image,Finset.mem_univ,true_and,funext (fun i => funext (bitEq i)),funext negEq,
        funext sameEq,GraphSeedSamples.cross]
      rfl
    rw [eq]
    simp only [GraphSampleDistance.fitsAt,reqEq,GraphSeedSamples.cover]
    rfl
  have valP (i : Fin n) : GraphSampleDistance.asWord (GraphInversionSeeds.pos i)=bit' i := by
    funext x; exact valEq i x _
  have valE (e : Fin n × Fin n) : GraphSampleDistance.asWord (GraphInversionSeeds.eqBit e)=same' e := by
    funext x; by_cases h : e.1∈x <;> by_cases k : e.2∈x <;> simp [GraphSampleDistance.asWord,GraphInversionSeeds.eqBit,same',bit',h,k]
  have valX (e : Fin n × Fin n) : GraphSampleDistance.asWord (GraphInversionSeeds.xorBit e)=(fun x => !(same' e x)) := by
    funext x; by_cases h : e.1∈x <;> by_cases k : e.2∈x <;> simp [GraphSampleDistance.asWord,GraphInversionSeeds.xorBit,same',bit',h,k]
  have rawEq : inputs E=raw' := by
    ext f
    simp only [inputs,GraphInversionSeeds.raw,Finset.image_union,Finset.image_image,Function.comp_def,
      Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and,raw',Finset.image_insert,Finset.image_singleton,
      Finset.mem_insert,Finset.mem_singleton,valP,valE,valX]
    rfl
  have compEq (j) : comp' j=block color j := by ext i;simp only [comp',block,Finset.mem_filter]
  have normEq (x) : norm' x=norm color x := by ext i;simp only [norm',L_meta_53216_aux.norm,compEq,Finset.mem_filter]
  have massEq (w) : mass' w=zMass color w := by funext z;simp only [mass',zMass,normEq,normFilter,W',Word,Row,anyUniverse]
  have deltaEq (f) : delta' f=delta color f := by funext j;simp only [delta',delta,val,compEq]
  have cmpEq (f g) : comparable' f g ↔ compare E color f g := by
    simp only [comparable',L_meta_53216_aux.compare,reqEq,rawEq,deltaEq]
  have lowEq (j) : low' j=lowSet (block color j) := by
    ext x;simp only [low',lowSet,compEq,Finset.mem_filter]
  have overlapEq (w) (j) : overlap' w j=overlap (block color j) w := by
    simp only [overlap',overlap,lowEq,compEq,W',Word,Row,anyUnion]
  have sortEq (v) : sorted' v ↔ ∀j,sortedAt (block color j) v := by
    simp only [sorted',sortedAt,low',compEq,Finset.mem_filter,Finset.mem_univ,true_and,W',Word,Row,anyUnion]
  have distEq (w f g) : dist' w f g=distance w f g := by simp only [dist',distance,normFilter,W',Word,Row,anyUniverse]
  have validEq (D w) : valid' D w ↔ valid E color D w := by
    simp only [valid',valid,keepEq,normFilter,W',Word,Row,anyUniverse]
  refine ⟨?_,?_,?_⟩
  · intro w D;simpa only [validEq,overlapEq,cmpEq,distEq,massEq] using exactCriterion E color edges onto part w D
  · intro w;simpa only [massEq,sortEq,overlapEq] using compress onto w
  · intro M D;simpa only [validEq,massEq,cmpEq,distEq,sortEq,lowEq,compEq,W',Word,Row,anyUnion] using realize E color edges onto part M D
