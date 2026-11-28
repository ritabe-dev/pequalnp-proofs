import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1553_aux
open scoped Classical
variable {α : Type} [Fintype α] [DecidableEq α] {n : Nat}
noncomputable def graph (e : α ≃ Fin n) (R : α → α → Prop) :=
  Finset.univ.filter (fun p : Fin n × Fin n => p.1<p.2 ∧ (R (e.symm p.1) (e.symm p.2) ∨ R (e.symm p.2) (e.symm p.1)))
def Cov (G : Finset (Fin n × Fin n)) (C : Finset (Fin n)) := ∀t∈G,t.1∈C ∨ t.2∈C
def Bip (G : Finset (Fin n × Fin n)) (D S : Finset (Fin n)) :=
  ∀t∈G,t.1∉D → t.2∉D → (t.1∈S ↔ t.2∉S)
def Opt (G : Finset (Fin n × Fin n)) (w : Fin n → Nat) (C : Finset (Fin n)) := Cov G C ∧ ∀ B,Cov G B → C.sum w≤B.sum w
def Ind (R : α → α → Prop) (X : α → Bool) := ∀a b,R a b → ¬(X a=true ∧ X b=true)
def omitted (e : α ≃ Fin n) (C : Finset (Fin n)) (x : α) := decide (e x∉C)
def complement (e : α ≃ Fin n) (X : α → Bool) := Finset.univ.filter (fun i => X (e.symm i)=false)
theorem omitted_comp (e : α ≃ Fin n) (X : α → Bool) : omitted e (complement e X)=X := by
  funext x;cases hx : X x <;> simp [omitted,complement,hx]
theorem strictGraph (e : α ≃ Fin n) (R : α → α → Prop) : ∀t∈graph e R,t.1<t.2 :=
  fun _ h => (Finset.mem_filter.mp h).2.1
theorem graphCov (e : α ≃ Fin n) (R : α → α → Prop) (ir : ∀x,¬R x x) (C : Finset (Fin n)) :
    Cov (graph e R) C ↔ Ind R (omitted e C) := by
  constructor
  · intro h x y r both
    obtain ⟨a,b⟩ := both;simp only [omitted,decide_eq_true_eq] at a b
    have ne : e x≠e y := by intro eq;exact ir y (e.injective eq ▸ r)
    rcases lt_or_gt_of_ne ne with lt|gt
    · have inside : (e x,e y)∈graph e R := by simp [graph,lt,r]
      exact (h _ inside).elim a b
    · have inside : (e y,e x)∈graph e R := by simp [graph,gt,r]
      exact (h _ inside).elim b a
  · intro h t ht;by_contra! bad
    obtain ⟨_,_,r⟩ := Finset.mem_filter.mp ht
    have xx : omitted e C (e.symm t.1)=true := by simpa [omitted] using bad.1
    have yy : omitted e C (e.symm t.2)=true := by simpa [omitted] using bad.2
    rcases r with r|r
    · exact h _ _ r ⟨xx,yy⟩
    · exact h _ _ r ⟨yy,xx⟩
theorem compCovered (e : α ≃ Fin n) {R : α → α → Prop} (ir : ∀x,¬R x x) {X : α → Bool}
    (h : Ind R X) : Cov (graph e R) (complement e X) :=
  (graphCov e R ir _).mpr (by rwa [omitted_comp])
def gain (w : α → Nat) (X : α → Bool) := ∑x,if X x then w x else 0
theorem costId (e : α ≃ Fin n) (w : α → Nat) (C : Finset (Fin n)) :
    C.sum (fun i => w (e.symm i)) + gain w (omitted e C) = ∑x,w x := by
  classical
  let amt (i : Fin n) := w (e.symm i)
  have eq1 : gain w (omitted e C) = ∑i : Fin n,if i∈C then 0 else amt i := by
    rw [←e.sum_comp]; unfold gain;apply Finset.sum_congr rfl;intro x _
    by_cases h : e x∈C <;> simp [amt,omitted,h]
  have eq2 : ∑x,w x=∑i,amt i := by rw [←e.sum_comp];simp [amt]
  rw [eq1,eq2]
  have cf : C=Finset.univ.filter (fun x => x∈C) := by ext;simp
  calc
    _ = (Finset.univ.filter (fun x => x∈C)).sum amt+(∑i : Fin n,if i∈C then 0 else amt i) := by rw [←cf]
    _ = _ := by
      simp only [Finset.sum_filter,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl;intro i _;by_cases hi : i∈C <;> simp [hi]
def mark (e : α ≃ Fin n) (b : α → Bool) := Finset.univ.filter (fun i => b (e.symm i)=true)
theorem mem_mark (e : α ≃ Fin n) (b : α → Bool) (i) : i∈mark e b ↔ b (e.symm i)=true := by simp [mark]
theorem graphBip (e : α ≃ Fin n) (R : α → α → Prop) (D S : α → Bool)
    (cross : ∀ x y,R x y → D x=false → D y=false → S x = !S y) :
    Bip (graph e R) (mark e D) (mark e S) := by
  intro t ht hx hy
  simp only [mem_mark,Bool.not_eq_true] at hx hy ⊢
  rcases (Finset.mem_filter.mp ht).2.2 with r|r
  · rw [cross _ _ r hx hy];cases S (e.symm t.2) <;> decide
  · rw [cross _ _ r hy hx];cases S (e.symm t.1) <;> decide
end PEqualNP.Outside.L_lib_1553_aux

namespace PEqualNP.Outside.L_lib_1553_aux
open scoped Classical
abbrev Label (d : Nat) := Fin d → Bool
abbrev Port (d m : Nat) := Label d × Fin m × Bool
abbrev Leaf (d m : Nat) := Fin d × Label d × Fin m
abbrev Vertex (d m : Nat) := Fin d ⊕ (Port d m ⊕ Leaf d m)
def selV (i : Fin d) : Vertex d m := .inl i
def portV (p : Port d m) : Vertex d m := .inr (.inl p)
def leafV (l : Leaf d m) : Vertex d m := .inr (.inr l)
def setBit (z : Label d) (i : Fin d) (b : Bool) : Label d := Function.update z i b
def owner (l : Leaf d m) : Port d m := (setBit l.2.1 l.1 true,l.2.2,l.2.1 l.1)
def leafOf (i : Fin d) (p : Port d m) : Leaf d m := (i,setBit p.1 i p.2.2,p.2.1)
theorem ownerOf {p : Port d m} {i : Fin d} (hi : p.1 i=true) : owner (leafOf i p)=p := by
  rcases p with ⟨z,j,b⟩;dsimp [owner,leafOf,setBit] at *;simp [←hi]
def other (p : Port d m) : Port d m := (p.1,p.2.1,!p.2.2)
def rel : Vertex d m → Vertex d m → Prop
  | .inl i,.inr (.inl p) => p.1 i=false
  | .inl i,.inr (.inr l) => l.1=i
  | .inr (.inl p),.inr (.inl q) => q=other p
  | .inr (.inr l),.inr (.inl p) => owner l=p
  | _,_ => False
theorem ir (v : Vertex d m) : ¬rel v v := by
  cases v with
  | inl i => exact id
  | inr v => cases v with
    | inr l => exact id
    | inl p => intro h;have hh:=congrArg (fun u : Port d m => u.2.2) h;cases b:p.2.2 <;> simp [other,b] at hh
def mult (d m : Nat) := m*2^d
def wgt : Vertex d m → Nat := Sum.elim (fun _ => mult d m) (fun _ => 1)
theorem cardLabel (d) : Fintype.card (Label d)=2^d := by simp [Label]
theorem cardPort (d m) : Fintype.card (Port d m)=2*mult d m := by simp [Port,cardLabel,mult];ring
theorem cardLeaf (d m) : Fintype.card (Leaf d m)=d*mult d m := by simp only [Leaf,Fintype.card_prod,Fintype.card_fin,cardLabel,mult];ring
theorem cardV (d m) : Fintype.card (Vertex d m)=d+(d+2)*mult d m := by simp only [Vertex,Fintype.card_sum,Fintype.card_fin,cardPort,cardLeaf];ring
theorem totalW (d m) : (∑v : Vertex d m,wgt v)=(2*d+2)*mult d m := by
  simp [Fintype.sum_sum_type,wgt,cardPort,cardLeaf,mult];ring
def del : Vertex d m → Bool := Sum.elim (fun _ => true) (fun _ => false)
def side : Vertex d m → Bool := Sum.elim (fun _ => false) (Sum.elim (fun p => p.2.2) (fun l => ! (owner l).2.2))
theorem cross (x y : Vertex d m) (ed : rel x y) (hx : del x=false) (hy : del y=false) : side x= !side y := by
  cases x with
  | inl i => contradiction
  | inr x => cases y with
    | inl i => contradiction
    | inr y => cases x with
      | inl p => cases y with
        | inl q => change q=other p at ed;subst q;simp [side,other]
        | inr l => exact False.elim ed
      | inr l => cases y with
        | inr t => exact False.elim ed
        | inl p => change owner l=p at ed;subst p;rfl
def selected (X : Vertex d m → Bool) : Label d := fun i => X (selV i)
def used (X : Vertex d m → Bool) := Finset.univ.filter (fun p : Port d m => X (portV p)=true)
def holes (X : Vertex d m → Bool) := Finset.univ.filter (fun l : Leaf d m => selected X l.1=false ∧ X (leafV l)=false)
def costs (X : Vertex d m → Bool) := gain (@wgt d m) X
theorem accounting {X : Vertex d m → Bool} (ok : Ind rel X) : costs X+(holes X).card=d*mult d m+(used X).card := by
  classical
  let sc (i : Fin d) := if selected X i then mult d m else 0
  let lc (l : Leaf d m) := (X (leafV l)).toNat
  let hc (l : Leaf d m) := (decide (selected X l.1=false ∧ X (leafV l)=false)).toNat
  have countB {T : Type} [Fintype T] (b : T → Bool) : (∑t,(b t).toNat)=(Finset.univ.filter (fun t => b t=true)).card := by
    have cv t : (b t).toNat=if b t then 1 else 0 := by cases b t <;> rfl
    simp [cv]
  have form : costs X=(∑i,sc i)+(used X).card+∑l,lc l := by
    unfold costs gain
    simp only [Fintype.sum_sum_type,wgt,Sum.elim_inl,Sum.elim_inr]
    have portEq : (∑p : Port d m,if X (portV p) then 1 else 0)=(used X).card := by simp [used]
    have leafEq l : (if X (leafV l) then 1 else 0)=lc l := by unfold lc;cases X (leafV l) <;> rfl
    change (∑i,sc i)+((∑p,if X (portV p) then 1 else 0)+∑l,if X (leafV l) then 1 else 0)=_
    rw [portEq];simp only [leafEq,Nat.add_assoc]
  have holeEq : (∑l,hc l)=(holes X).card := by simpa [hc,holes] using countB (fun l : Leaf d m => decide (selected X l.1=false ∧ X (leafV l)=false))
  have per (l : Leaf d m) : lc l+hc l=if selected X l.1 then 0 else 1 := by
    have no:=ok (selV l.1) (leafV l) rfl
    change ¬(selected X l.1=true ∧ X (leafV l)=true) at no
    cases hs:selected X l.1 <;> cases hl:X (leafV l) <;> simp_all [lc,hc]
  have perI (i : Fin d) : sc i+(∑z : Label d,∑j : Fin m,if selected X i then 0 else 1)=mult d m := by
    by_cases h : selected X i=true <;> simp [sc,h,mult,cardLabel,Nat.mul_comm]
  have sums := Finset.sum_congr (s₁:=Finset.univ) rfl (fun i _ => perI i)
  rw [Finset.sum_add_distrib] at sums
  have sumCost : (∑l,lc l)+(∑l,hc l)=∑i : Fin d,∑z : Label d,∑j : Fin m,if selected X i then 0 else 1 := by
    rw [←Finset.sum_add_distrib];simp only [per,Fintype.sum_prod_type]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.nsmul_eq_mul] at sums sumCost
  rw [form,←holeEq];omega
end PEqualNP.Outside.L_lib_1553_aux

namespace PEqualNP.Outside.L_lib_1553_aux
open scoped Classical
def blocked (Q : Finset (Port d m)) (z : Label d) := Finset.univ.filter (fun j : Fin m => (z,j,false)∈Q ∧ (z,j,true)∈Q)
def avoids (Q : Finset (Port d m)) (X : Vertex d m → Bool) := ∀p∈Q,X (portV p)=false
theorem upper {Q : Finset (Port d m)} {X : Vertex d m → Bool} (ok : Ind rel X) (pins : avoids Q X) :
    costs X+(blocked Q (selected X)).card≤d*mult d m+m := by
  classical
  let z := selected X
  let L := (used X).filter (fun p => p.1=z)
  let F := (used X).filter (fun p => p.1≠z)
  have total : L.card+F.card=(used X).card := Finset.card_filter_add_card_filter_not _
  have missing (p : ↥F) : ∃l∈holes X,owner l=p.val := by
    obtain ⟨hp,ne⟩:=Finset.mem_filter.mp p.property
    have usedP : X (portV p.val)=true := (Finset.mem_filter.mp hp).2
    have mismatch : ∃i,p.val.1 i≠z i := Function.ne_iff.mp ne
    obtain ⟨i,hi⟩:=mismatch
    have case1 : p.val.1 i=true ∧ z i=false := by
      cases hz:z i <;> cases hv:p.val.1 i <;> simp_all
      exact (ok (selV i) (portV p.val) hv ⟨hz,usedP⟩).elim
    have own:=ownerOf (p:=p.val) case1.1
    have off : X (leafV (leafOf i p.val))=false := by
      cases h:X (leafV (leafOf i p.val));rfl;exact (ok (leafV (leafOf i p.val)) (portV p.val) own ⟨h,usedP⟩).elim
    exact ⟨leafOf i p.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,case1.2,off⟩,own⟩
  choose g hg ho using missing
  have extBound : F.card≤(holes X).card := by
    let f (p : ↥F) : ↥(holes X) := ⟨g p,hg p⟩
    have inj : Function.Injective f := fun p q eq => Subtype.ext ((ho p).symm.trans ((congrArg owner (congrArg Subtype.val eq)).trans (ho q)))
    simpa using Fintype.card_le_of_injective f inj
  let free := Finset.univ.filter (fun j : Fin m => ¬((z,j,false)∈Q ∧ (z,j,true)∈Q))
  have cnt : (blocked Q z).card+free.card=m := by simpa [free,blocked] using Finset.card_filter_add_card_filter_not (s:=(Finset.univ : Finset (Fin m))) (fun j => (z,j,false)∈Q ∧ (z,j,true)∈Q)
  have record (p : ↥L) : p.val.2.1∈free := by
    obtain ⟨hp,eq⟩:=Finset.mem_filter.mp p.property
    have on:=(Finset.mem_filter.mp hp).2
    apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩;intro both
    obtain ⟨⟨a,j,b⟩,mem⟩:=p;dsimp at eq;subst a
    cases b <;> first | exact Bool.noConfusion (on.symm.trans (pins _ both.1)) | exact Bool.noConfusion (on.symm.trans (pins _ both.2))
  let addr (p : ↥L) : ↥free := ⟨p.val.2.1,record p⟩
  have inj : Function.Injective addr := by
    intro p q eq
    have same : p.val.2.1=q.val.2.1 := congrArg Subtype.val eq
    obtain ⟨⟨a,j,b⟩,hp⟩:=p;obtain ⟨⟨a',j',b'⟩,hq⟩:=q
    change j=j' at same;subst j'
    obtain ⟨p1,p2⟩:=Finset.mem_filter.mp hp;obtain ⟨q1,q2⟩:=Finset.mem_filter.mp hq
    change a=z at p2;change a'=z at q2;subst a;subst a'
    have ub:=(Finset.mem_filter.mp p1).2;have ub':=(Finset.mem_filter.mp q1).2
    have incompatible (s : Bool) : ¬(X (portV (z,j,s))=true ∧ X (portV (z,j,!s))=true) := ok (portV (z,j,s)) (portV (z,j,!s)) rfl
    cases b <;> cases b' <;> first | rfl | exact (incompatible _ ⟨ub,ub'⟩).elim
  have locBound : L.card≤free.card := by simpa using Fintype.card_le_of_injective addr inj
  have bill:=accounting ok;change costs X+(blocked Q z).card≤_;omega
def prefer (Q : Finset (Port d m)) (z : Label d) (j : Fin m) := decide ((z,j,false)∈Q)
def policy (Q : Finset (Port d m)) (z : Label d) : Vertex d m → Bool :=
  Sum.elim z (Sum.elim (fun p => decide (p.1=z ∧ p.2.1∉blocked Q z ∧ p.2.2=prefer Q z p.2.1)) (fun l => !z l.1))
theorem policyInd (Q : Finset (Port d m)) (z : Label d) : Ind rel (policy Q z) := by
  intro x y ed both
  cases x with
  | inl i =>
    cases y with
    | inl j => exact ed
    | inr y => cases y with
      | inl p =>
        have on:=of_decide_eq_true both.2
        change p.1=z ∧ _ at on
        change p.1 i=false at ed
        rw [on.1] at ed;exact Bool.noConfusion (ed.symm.trans both.1)
      | inr l =>
        change l.1=i at ed
        change z i=true ∧ (!z l.1)=true at both
        simp_all
  | inr x =>
    cases y with
    | inl i => cases x <;> exact ed
    | inr y =>
      cases x with
      | inl p =>
        cases y with
        | inr l => exact ed
        | inl q =>
          change q=other p at ed;subst q
          have a:=of_decide_eq_true both.1;have b:=of_decide_eq_true both.2
          change p.1=z ∧ p.2.1∉blocked Q z ∧ (!p.2.2)=prefer Q z p.2.1 at b
          have eq:=a.2.2.trans b.2.2.symm
          cases h:p.2.2 <;> simp [h] at eq
      | inr l =>
        cases y with
        | inr a => exact ed
        | inl p =>
          change owner l=p at ed;subst p
          have a:=of_decide_eq_true both.2
          change (owner l).1=z ∧ _ at a
          have hi:=congrFun a.1 l.1
          simp [owner,setBit] at hi
          have off : (!z l.1)=true := both.1
          simp_all
theorem policyAvoid (Q : Finset (Port d m)) (z : Label d) : avoids Q (policy Q z) := by
  rintro ⟨a,j,b⟩ mem
  by_cases eq:a=z
  · subst a;cases b <;> simp_all [policy,portV,blocked,prefer]
  · simp [policy,portV,eq]
theorem policyCost (Q : Finset (Port d m)) (z : Label d) :
    costs (policy Q z)+(blocked Q z).card=d*mult d m+m := by
  let X := policy Q z
  have no : holes X=∅ := by ext l;simp [holes,X,selected,selV,leafV,policy]
  have im : used X=(Finset.univ.filter (fun j : Fin m => j∉blocked Q z)).image (fun j => (z,j,prefer Q z j)) := by
    ext p;rcases p with ⟨a,j,b⟩;simp [used,X,portV,policy];aesop
  have cnt := Finset.card_filter_add_card_filter_not (s:=(Finset.univ : Finset (Fin m))) (fun j => j∈blocked Q z)
  have bill:=accounting (policyInd Q z);change costs X+(holes X).card=_ at bill
  rw [no,im,Finset.card_image_of_injective _ (fun a b eq => congrArg (fun p : Port d m => p.2.1) eq)] at bill
  change costs X+_= _
  simp at cnt bill;omega
end PEqualNP.Outside.L_lib_1553_aux

namespace PEqualNP.Outside.L_lib_1553_aux
open scoped Classical
def botL (d : Nat) : Label d := fun _ => false
def topL (d : Nat) : Label d := fun _ => true
theorem apart (hd : 0<d) : botL d≠topL d := by intro eq;exact Bool.noConfusion (congrFun eq ⟨0,hd⟩)
def altPort (p : Port d m) := decide (p.2.2=true ∨ (p.1≠botL d ∧ p.1≠topL d))
def alt : Vertex d m → Bool := Sum.elim (fun _ => false) (Sum.elim altPort (fun _ => false))
def shoreAlt : Vertex d m → Bool := Sum.elim (fun _ => false) (Sum.elim (fun p => decide (p.1=botL d)) (fun _ => true))
theorem altCross (x y : Vertex d m) (ed : rel x y) (hx : alt x=false) (hy : alt y=false) : shoreAlt x= !shoreAlt y := by
  cases x with
  | inl i =>
    cases y with
    | inl i => exact False.elim ed
    | inr y => cases y with
      | inr l => rfl
      | inl p =>
        change p.1 i=false at ed
        have ht:p.1≠topL d := fun eq => by rw [eq] at ed;contradiction
        simp_all [alt,altPort,shoreAlt]
  | inr x =>
    cases y with
    | inl i => cases x <;> exact False.elim ed
    | inr y =>
      cases x with
      | inr l => cases y with
        | inr t => exact False.elim ed
        | inl p =>
          change owner l=p at ed;subst p
          have ne : (owner l).1≠botL d := by intro eq;have hh:=congrFun eq l.1;simp [owner,setBit,botL] at hh
          simp [shoreAlt,ne]
      | inl p => cases y with
        | inr l => exact False.elim ed
        | inl q =>
          change q=other p at ed;subst q
          cases eq:p.2.2 <;> simp_all [alt,altPort,other]
theorem markCost {n} (e : Vertex d m ≃ Fin n) (b : Vertex d m → Bool) :
    (mark e b).sum (fun i => wgt (e.symm i))=gain wgt b := by
  classical
  unfold mark gain;rw [Finset.sum_filter,←e.sum_comp];simp
theorem altCost (hd : 0<d) : gain (@wgt d m) alt=2*(mult d m-m) := by
  unfold gain
  simp only [Fintype.sum_sum_type,alt,Sum.elim_inl,Sum.elim_inr,wgt,Bool.false_eq_true,ite_false,Finset.sum_const_zero,Nat.zero_add,Nat.add_zero]
  have one (z : Label d) (j : Fin m) : (∑s : Bool,if altPort (z,j,s) then 1 else 0)+ (if z=botL d then 1 else 0)+(if z=topL d then 1 else 0)=2 := by
    have ne:=apart hd
    by_cases b:z=botL d <;> by_cases t:z=topL d <;> simp_all [altPort,Fintype.sum_bool]
  have all:=Finset.sum_congr (s₁:=Finset.univ) rfl (fun z _ => Finset.sum_congr (s₁:=Finset.univ) rfl (fun j _ => one z j))
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,cardLabel,Nat.nsmul_eq_mul] at all
  have items (t : Label d) : (∑z : Label d,m*(if z=t then 1 else 0))=m := by simp [mul_ite]
  rw [items,items] at all
  rw [Fintype.sum_prod_type];simp only [Fintype.sum_prod_type]
  rw [show 2^d*(m*2)=(2^d*m)*2 by ring] at all
  unfold mult;rw [Nat.mul_comm m,Nat.mul_sub,Nat.mul_comm 2 (2^d*m),←all,Nat.two_mul,Nat.add_assoc,Nat.add_sub_cancel]
  apply Finset.sum_congr rfl;intro z _;apply Finset.sum_congr rfl;intro j _;apply Finset.sum_congr rfl;intro s _
  by_cases h:altPort (z,j,s)=true <;> simp [h]
theorem selectorsCount {n} (e : Vertex d m ≃ Fin n) : (mark e del).card=d := by
  have im : mark e del=Finset.univ.image (fun i : Fin d => e (selV i)) := by
    ext v;obtain ⟨x,rfl⟩:=e.surjective v;rw [mem_mark,Equiv.symm_apply_apply];cases x <;> simp [del,selV]
  rw [im,Finset.card_image_of_injective]
  · simp
  · intro i j h;exact Sum.inl.inj (e.injective h)
theorem baseW {n} (e : Vertex d m ≃ Fin n) (i : Fin n) :
    wgt (e.symm i) = if i∈mark e del then mult d m else 1 := by
  simp only [mem_mark];cases e.symm i <;> rfl
end PEqualNP.Outside.L_lib_1553_aux

namespace PEqualNP.Outside.L_lib_1553_aux
open scoped Classical
abbrev Hue := Fin 3
def price {α : Type} [Fintype α] (w : α → Nat) (y : α → Hue) := ∑v,w v*(y v).val
def Slack {n} (G : Finset (Fin n × Fin n)) (w : Fin n → Nat) (C : Finset (Fin n)) (g : Nat) :=
  ∀y : Fin n → Hue,(∀t∈G,2≤(y t.1).val+(y t.2).val) → 2*C.sum w≤price w y+g
def rnd (a : Hue) (d s f : Bool) := decide (a=2) || (decide (a=1) && (d || (s == f)))
theorem edgeRound : ∀(a b : Hue) (d e s t f : Bool),2≤a.val+b.val →
    (d=false → e=false → (s=true ↔ t=false)) → rnd a d s f=true ∨ rnd b e t f=true := by decide +kernel
theorem billRound : ∀(a : Hue) (d s : Bool),(rnd a d s true).toNat+(rnd a d s false).toNat≤a.val+d.toNat := by decide +kernel
theorem boolBill {α : Type} [Fintype α] (w : α → Nat) (p : α → Bool) :
    (Finset.univ.filter (fun v => p v=true)).sum w=∑v,w v*(p v).toNat := by
  rw [Finset.sum_filter];apply Finset.sum_congr rfl;intro v _;cases h:p v <;> simp
theorem rounding {n} {G : Finset (Fin n × Fin n)} {w : Fin n → Nat} {C0 D S : Finset (Fin n)}
    (ho : Opt G w C0) (hb : Bip G D S) : Slack G w C0 (D.sum w) := by
  classical
  intro y hy
  let d (v : Fin n) := decide (v∈D)
  let s (v : Fin n) := decide (v∈S)
  let p f v := rnd (y v) (d v) (s v) f
  let c f := Finset.univ.filter (fun v => p f v=true)
  have cheap f : C0.sum w≤(c f).sum w := by
    apply ho.2
    intro t ht
    have h:=edgeRound (y t.1) (y t.2) (d t.1) (d t.2) (s t.1) (s t.2) f (hy t ht) (by
      intro hd he
      simpa [s] using hb t ht (of_decide_eq_false hd) (of_decide_eq_false he))
    simpa [c,p] using h
  have sumD : (∑v,w v*(d v).toNat)=D.sum w := by rw [←boolBill];simp [d]
  have bounds := Finset.sum_le_sum (s:=Finset.univ) (fun v _ => Nat.mul_le_mul_left (w v) (billRound (y v) (d v) (s v)))
  change (∑v,w v*((p true v).toNat+(p false v).toNat)) ≤ ∑v,w v*((y v).val+(d v).toNat) at bounds
  simp only [Nat.mul_add,Finset.sum_add_distrib,sumD] at bounds
  have bill f : (c f).sum w=∑v,w v*(p f v).toNat := boolBill _ _
  have htrue:=cheap true
  have hfalse:=cheap false
  rw [bill] at htrue hfalse
  unfold price
  omega
end PEqualNP.Outside.L_lib_1553_aux

namespace PEqualNP.Outside.L_lib_1553_aux
open scoped Classical
theorem edgeIn {α : Type} [Fintype α] [DecidableEq α] {n} (e : α ≃ Fin n) {R : α → α → Prop} (irr : ∀x,¬R x x)
    {x y} (h : R x y) : (e x,e y)∈graph e R ∨ (e y,e x)∈graph e R := by
  have ne : e x≠e y := fun eq => irr y (e.injective eq ▸ h)
  rcases lt_or_gt_of_ne ne with lt|gt
  · exact Or.inl (by simp [graph,lt,h])
  · exact Or.inr (by simp [graph,gt,h])
theorem pairBound (f : Vertex d m → Hue) (ok : ∀x y,rel x y → 2≤(f x).val+(f y).val) :
    2*((d+1)*mult d m)≤price wgt f := by
  classical
  let a (l : Leaf d m) := (f (selV l.1)).val
  let b (l : Leaf d m) := (f (leafV l)).val
  let c (z : Label d) (j : Fin m) (s : Bool) := (f (portV (z,j,s))).val
  have ab (l : Leaf d m) : 2≤a l+b l := ok (selV l.1) (leafV l) rfl
  have cc (z : Label d) (j : Fin m) : 2≤∑s : Bool,c z j s := by
    rw [Fintype.sum_bool];have hh:=ok (portV (z,j,false)) (portV (z,j,true)) rfl
    change 2≤c z j false+c z j true at hh;omega
  have lo1:=Finset.sum_le_sum (s:=Finset.univ) (fun l _ => ab l)
  have lo2:=Finset.sum_le_sum (s:=Finset.univ) (fun z _ => Finset.sum_le_sum (s:=Finset.univ) (fun j _ => cc z j))
  simp only [Finset.sum_const,Finset.card_univ,cardLeaf,cardLabel,Fintype.card_fin,Nat.nsmul_eq_mul,Finset.sum_add_distrib] at lo1 lo2
  have slots : (∑l,a l)=∑i : Fin d,mult d m*(f (selV i)).val := by
    rw [Fintype.sum_prod_type];simp only [Fintype.sum_prod_type,a,Finset.sum_const,Finset.card_univ,Fintype.card_fin,cardLabel,Nat.nsmul_eq_mul]
    apply Finset.sum_congr rfl;intro i _;simp only [Fintype.card_prod,cardLabel,Fintype.card_fin,mult];ring
  rw [slots] at lo1
  unfold price;rw [Fintype.sum_sum_type];simp only [Fintype.sum_sum_type,wgt,Sum.elim_inl,Sum.elim_inr,Nat.one_mul]
  change _≤(∑i,mult d m*(f (selV i)).val)+((∑p : Port d m,c p.1 p.2.1 p.2.2)+∑l,b l)
  simp only [Fintype.sum_prod_type] at lo1 ⊢
  rw [show 2^d*(m*2)=2*mult d m by unfold mult;ring] at lo2
  rw [Nat.add_mul,Nat.one_mul];omega
theorem lifts {n} (e : Vertex d m ≃ Fin n) (y : Fin n → Hue)
    (ok : ∀t∈graph e rel,2≤(y t.1).val+(y t.2).val) :
    2*((d+1)*mult d m)≤price (fun i => wgt (e.symm i)) y := by
  have b:=pairBound (fun x => y (e x)) (by
    intro x t h;rcases edgeIn e ir h with hit|hit
    · exact ok _ hit
    · have hh:=ok _ hit;dsimp only at hh ⊢;omega)
  unfold price at *;rw [←e.sum_comp];simpa using b
end PEqualNP.Outside.L_lib_1553_aux

namespace PEqualNP.Outside.L_lib_1553_aux
open scoped Classical
def minusOne (i : Fin d) : Label d := fun j => decide (j≠i)
theorem minusInj : Function.Injective (@minusOne d) := by
  intro i j eq;have h:=congrFun eq i;simpa [minusOne] using h.symm
def tri (j : Fin m) (i : Fin d) (s : Fin 3) : Vertex d m :=
  if s=0 then selV i else portV (minusOne i,j,decide (s=2))
theorem disTriangles (j : Fin m) {i h : Fin d} {a b : Fin 3} (eq : tri j i a=tri j h b) : i=h := by
  unfold tri at eq
  split_ifs at eq <;> first | exact Sum.inl.inj eq | contradiction | exact minusInj (congrArg (fun p : Port d m => p.1) (Sum.inl.inj (Sum.inr.inj eq)))
theorem cutLower {n} (e : Vertex d m ≃ Fin n) (T U : Finset (Fin n)) (hb : Bip (graph e rel) T U) (j : Fin m) : d≤T.card := by
  classical
  have cross {x y : Vertex d m} (ed : rel x y) (hx : e x∉T) (hy : e y∉T) : e x∈U ↔ e y∉U := by
    rcases edgeIn e ir ed with h|h
    · exact hb _ h hx hy
    · have hh:=hb _ h hy hx;dsimp at hh;tauto
  have meet (i : Fin d) : ∃s : Fin 3,e (tri j i s)∈T := by
    by_contra! no
    have ab : rel (tri j i 0) (tri j i 1) := by simp [tri,rel,selV,portV,minusOne]
    have ac : rel (tri j i 0) (tri j i 2) := by simp [tri,rel,selV,portV,minusOne]
    have bc : rel (tri j i 1) (tri j i 2) := rfl
    have p:=cross ab (no 0) (no 1)
    have q:=cross ac (no 0) (no 2)
    have r:=cross bc (no 1) (no 2)
    tauto
  choose s hs using meet
  let f (i : Fin d) : ↥T := ⟨e (tri j i (s i)),hs i⟩
  have inj : Function.Injective f := fun a b eq => disTriangles j (e.injective (congrArg Subtype.val eq))
  simpa using Fintype.card_le_of_injective f inj
end PEqualNP.Outside.L_lib_1553_aux

open PEqualNP.Outside.L_lib_1553_aux in
theorem PEqualNP.Outside.L_lib_1553 : letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let cover := fun {N : Nat} (G : Finset (Fin N × Fin N)) (C : Finset (Fin N)) =>
  ∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C
let opt := fun {N : Nat} (G : Finset (Fin N × Fin N)) (w : Fin N → Nat) (C : Finset (Fin N)) =>
  cover G C ∧ ∀ B, cover G B → C.sum w ≤ B.sum w
let bip := fun {N : Nat} (G : Finset (Fin N × Fin N)) (D S : Finset (Fin N)) =>
  ∀ e ∈ G, e.1 ∉ D → e.2 ∉ D → (e.1 ∈ S ↔ e.2 ∉ S)
let slack := fun {n : Nat} (G : Finset (Fin n × Fin n)) (w : Fin n → Nat)
  (C0 : Finset (Fin n)) (g : Nat) =>
  ∀ y : Fin n → Fin 3, (∀ e ∈ G, 2 ≤ (y e.1).val + (y e.2).val) →
    2*C0.sum w ≤ (∑ v : Fin n, w v * (y v).val) + g
∀ (d m : Nat), (0 < m) →
let b := 2^d
let M := m*b
let n := d+(d+2)*M
let I := Fin b × Fin m × Bool
∃ (G : Finset (Fin n × Fin n)) (w : Fin n → Nat) (D S C0 : Finset (Fin n)) (p : I → Fin n),
  (∀ e ∈ G, e.1<e.2) ∧ D.card=d ∧ bip G D S ∧
  (∀ v, w v = if v ∈ D then M else 1) ∧ Function.Injective p ∧ (∀ i, p i ∉ D) ∧
  opt G w C0 ∧ C0.sum w+m=(d+2)*M ∧
  slack G w C0 (2*(M-m)) ∧ (∑ v : Fin n, w v)+2*(M-m)=2*C0.sum w ∧
  (∀ T U : Finset (Fin n), bip G T U → d ≤ T.card ∧ 2*(M-m) ≤ T.sum w) ∧
  (∃ T U : Finset (Fin n), bip G T U ∧ T.sum w=2*(M-m)) ∧
  ∀ Q : Finset I, ∀ j : Nat,
    (∃ C, cover G C ∧ (∀ i ∈ Q, p i ∈ C) ∧ C.sum w ≤ C0.sum w+j) ↔
    ∃ z : Fin b, (Finset.univ.filter (fun t : Fin m =>
        (z,t,false) ∈ Q ∧ (z,t,true) ∈ Q)).card ≤ j := by
  classical
  intro cov' opt' bip' slack' d m hm b M n I
  have Mpos : m≤M := Nat.le_mul_of_pos_right _ (by dsimp only [b];positivity)
  have cc : Fintype.card (Vertex d m)=n := cardV d m
  let e : Vertex d m ≃ Fin n := Fintype.equivFinOfCardEq cc
  let lab : Fin b ≃ Label d := (Fintype.equivFinOfCardEq (cardLabel d)).symm
  let move : I ≃ Port d m := lab.prodCongr (Equiv.refl _)
  let p (i : I) := e (portV (move i))
  let G := graph e rel
  let D := mark e del
  let S := mark e side
  let w (i : Fin n) := wgt (e.symm i)
  have all : (∑x : Vertex d m,wgt x)=2*(d*M)+2*M := by rw [totalW];change (2*d+2)*M=_;ring
  have total : (∑i : Fin n,w i)=2*(d*M)+2*M := by rw [←e.sum_comp];simpa [w] using all
  have bill (C : Finset (Fin n)) : C.sum w+costs (omitted e C)=2*(d*M)+2*M := (costId e wgt C).trans all
  have cost (X : Vertex d m → Bool) : (complement e X).sum w+costs X=2*(d*M)+2*M := by simpa only [omitted_comp] using bill (complement e X)
  have empt (z : Label d) : blocked (∅ : Finset (Port d m)) z=∅ := by ext;simp [blocked]
  let X0 := policy (∅ : Finset (Port d m)) (botL d)
  let C0 := complement e X0
  have base : C0.sum w+m=d*M+2*M := by
    have pay:=policyCost (∅ : Finset (Port d m)) (botL d);rw [empt] at pay
    change costs X0+0=d*M+m at pay
    have h:=cost X0;change C0.sum w+costs X0=_ at h;omega
  have opt : Opt G w C0 := by
    refine ⟨compCovered _ ir (policyInd _ _),?_⟩;intro C hc
    have ind:=(graphCov e _ ir C).mp hc
    have low:=upper (Q:=∅) ind (by simp [avoids]);rw [empt] at low
    change costs (omitted e C)+0≤d*M+m at low
    have full:=bill C;omega
  have bip : Bip G D S := graphBip e rel del side cross
  have gap : 2*(M-m)+2*((d+1)*M)=2*(C0.sum w) := by rw [Nat.add_mul,Nat.one_mul];omega
  have priceEq : (∑i,w i)+2*(M-m)=2*(C0.sum w) := by rw [total];omega
  have gapBound : Slack G w C0 (2*(M-m)) := by
    intro y hy;have a:=lifts e y hy;change 2*((d+1)*M)≤price w y at a;omega
  refine ⟨G,w,D,S,C0,p,strictGraph _ _,selectorsCount _,bip,?_,?_,?_,opt,?_,gapBound,priceEq,?_,?_,?_⟩
  · intro v;have hh:=baseW e v;change wgt (e.symm v)=_;split_ifs at * <;> assumption
  · intro i j eq;exact move.injective (Sum.inl.inj (Sum.inr.inj (e.injective eq)))
  · intro i;change e (portV (move i))∉mark e del;rw [mem_mark,Equiv.symm_apply_apply];exact Bool.false_ne_true
  · rw [Nat.add_mul];omega
  · intro T U hb
    refine ⟨cutLower e T U hb ⟨0,hm⟩,?_⟩
    have bound:=rounding opt (D:=T) (S:=U) hb (fun _ => 1) (by simp)
    have eq : price w (fun _ => 1)=(∑i,w i) := by simp [price]
    rw [eq] at bound;omega
  · by_cases hd : d=0
    · subst d
      refine ⟨D,S,bip,?_⟩
      have card : D.card=0 := selectorsCount e
      have MM : M=m := by simp [M,b]
      rw [Finset.card_eq_zero.mp card,Finset.sum_empty,MM,Nat.sub_self,Nat.mul_zero]
    · refine ⟨mark e alt,mark e shoreAlt,graphBip e rel alt shoreAlt altCross,?_⟩
      exact (markCost e alt).trans (altCost (Nat.pos_of_ne_zero hd))
  · intro Q j
    let Q' := Q.image move
    have bc (z : Fin b) : (blocked Q' (lab z)).card=(Finset.univ.filter (fun t : Fin m =>
        (z,t,false)∈Q ∧ (z,t,true)∈Q)).card := by
      congr 1;ext t
      have mem (s : Bool) : (lab z,t,s)∈Q' ↔ (z,t,s)∈Q := by
        change move (z,t,s)∈Q.image move ↔ _;simp
      simp only [blocked,Finset.mem_filter,Finset.mem_univ,true_and,mem]
    constructor
    · rintro ⟨C,hc,hpin,hbill⟩
      let X := omitted e C
      have ind : Ind rel X := (graphCov e _ ir C).mp hc
      have off : avoids Q' X := by
        intro a ha;obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp ha
        simpa [X,omitted,p] using hpin u hu
      obtain ⟨z,hz⟩:=lab.surjective (selected X)
      have ub:=upper ind off
      rw [←hz,bc] at ub;change costs X+_≤d*M+m at ub
      have full:=bill C;change C.sum w+costs X=_ at full
      refine ⟨z,?_⟩
      have eq : (Finset.univ.filter (fun t : Fin m => (z,t,false)∈Q ∧ (z,t,true)∈Q)).card≤j := by omega
      convert eq using 1;congr 1;ext;simp only [Finset.mem_filter]
    · rintro ⟨z,hz⟩
      let X := policy Q' (lab z)
      refine ⟨complement e X,compCovered e ir (policyInd _ _),?_,?_⟩
      · intro i hi
        have off:=policyAvoid Q' (lab z) (move i) (Finset.mem_image_of_mem move hi)
        simpa [complement,p,X] using off
      · have pay:=policyCost Q' (lab z);rw [bc] at pay
        change costs X+_ = d*M+m at pay
        have bound : (Finset.univ.filter (fun t : Fin m => (z,t,false)∈Q ∧ (z,t,true)∈Q)).card≤j := by convert hz using 1;congr 1;ext;simp only [Finset.mem_filter]
        have full:=cost X;omega
