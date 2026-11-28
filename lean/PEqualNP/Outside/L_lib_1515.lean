import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1515_aux
abbrev BitState := Fin 5 → Bool
def bitEdge (a b : Fin 5) : Prop := (a=0 ∧ (b=1 ∨ b=3)) ∨ (a=1 ∧ b=2) ∨ (a=3 ∧ b=4)
instance (a b : Fin 5) : Decidable (bitEdge a b) := by unfold bitEdge;infer_instance
def bitInd (q : BitState) : Prop := ∀ a b,bitEdge a b → ¬ (q a=true ∧ q b=true)
instance (q : BitState) : Decidable (bitInd q) := by unfold bitInd;infer_instance
def price (a : Fin 5) : Nat := if a=2 ∨ a=4 then 1 else 2
def value (q : BitState) := ∑ a : Fin 5,if q a then price a else 0
def chosen (b : Bool) (a : Fin 5) := if b then decide (a=0 ∨ a=2 ∨ a=4) else decide (a=1 ∨ a=3)
def shore (a : Fin 5) := decide (a=1 ∨ a=4)
def representative (b left : Bool) : Fin 5 := if b then (if left then 4 else 2) else (if left then 1 else 3)
theorem valueLe : ∀ q : BitState,bitInd q → value q≤4 := by decide +kernel
theorem classify : ∀ q : BitState,bitInd q → value q=4 → q=chosen (q 0) := by decide +kernel
theorem chosenValue : ∀ b,value (chosen b)=4 := by decide +kernel
theorem chosenInd : ∀ b,bitInd (chosen b) := by decide +kernel
theorem hasRep : ∀ b s t,chosen b (representative s t)=true ↔ b=s := by decide +kernel
theorem sideRep : ∀ b t,shore (representative b t)=t := by decide +kernel
theorem bitBip : ∀ a b,bitEdge a b → a≠0 → b≠0 → shore a = !shore b := by decide +kernel
theorem noLoop : ∀ a,¬bitEdge a a := by decide +kernel
end PEqualNP.Outside.L_lib_1515_aux

namespace PEqualNP.Outside.L_lib_1515_aux
open scoped Classical
abbrev Label (d : Nat) := Fin d → Bool
abbrev Vtx (d m : Nat) := (Fin d × Fin 5) ⊕ (Label d × Fin m × Bool)
def edge : Vtx d m → Vtx d m → Prop
  | .inl (i,a),.inl (j,b) => i=j ∧ bitEdge a b
  | .inl (i,a),.inr (l,_,s) => a=representative (!(l i)) (!s)
  | .inr _,.inl _ => False
  | .inr (l,i,s),.inr (k,j,t) => l=k ∧ i=j ∧ s=false ∧ t=true
def deleted : Vtx d m → Bool | .inl (_,a) => decide (a=0) | .inr _ => false
def side : Vtx d m → Bool | .inl (_,a) => shore a | .inr (_,_,s) => s
theorem edgeIrrefl (x : Vtx d m) : ¬edge x x := by
  rcases x with ⟨i,a⟩|⟨l,i,s⟩
  · simp [edge,noLoop]
  · cases s <;> simp [edge]
theorem edgeBip {x y : Vtx d m} (e : edge x y) (hx : deleted x=false) (hy : deleted y=false) :
    side x = !side y := by
  rcases x with ⟨i,a⟩|⟨l,i,s⟩ <;> rcases y with ⟨j,b⟩|⟨k,j,t⟩
  · exact bitBip a b e.2 (by simpa [deleted] using hx) (by simpa [deleted] using hy)
  · exact e ▸ sideRep _ _
  · exact e.elim
  · obtain ⟨_,_,rfl,rfl⟩:=e;rfl
def mult (d m : Nat) := 2*m*2^d+1
def weight : Vtx d m → Nat | .inl (_,a) => mult d m*price a | .inr _ => 1
theorem weightPos (x : Vtx d m) : 0<weight x := by
  rcases x with ⟨i,a⟩|⟨l,i,s⟩
  · apply Nat.mul_pos (Nat.zero_lt_succ _);unfold price;split <;> decide
  · exact Nat.zero_lt_one
def independent (X : Vtx d m → Bool) := ∀ u v,edge u v → ¬ (X u=true ∧ X v=true)
def sel (X : Vtx d m → Bool) (i : Fin d) (a : Fin 5) := X (.inl (i,a))
def pinsOff (X : Vtx d m → Bool) := ∀ l i s,X (.inr (l,i,s))=false
def payoff (X : Vtx d m → Bool) := ∑x,if X x then weight x else 0
def extras (X : Vtx d m → Bool) := ∑ l : Label d,∑ i : Fin m,∑ s : Bool, if X (.inr (l,i,s)) then 1 else 0
theorem splitPay (X : Vtx d m → Bool) :
    payoff X = mult d m * (∑i,value (sel X i)) + extras X := by
  unfold payoff extras value sel
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro a _
  cases h : X (.inl (i,a)) <;> simp [weight,h]
theorem offPay {X : Vtx d m → Bool} (h : pinsOff X) : extras X=0 := by unfold pinsOff at h;simp [extras,h]
theorem maxExtras (X : Vtx d m → Bool) : extras X ≤ 2*m*2^d := by
  have h : extras X ≤ ∑ l : Label d, ∑ i : Fin m,∑ s : Bool, (1 : Nat) := by
    apply Finset.sum_le_sum;intro l _
    apply Finset.sum_le_sum;intro i _
    apply Finset.sum_le_sum;intro s _;split <;> decide
  simpa [Label,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using h
theorem selInd {X : Vtx d m → Bool} (h : independent X) (i) : bitInd (sel X i) :=
  fun a b e => h (.inl (i,a)) (.inl (i,b)) ⟨rfl,e⟩
theorem totalSel {X : Vtx d m → Bool} (h : independent X) : (∑i,value (sel X i))≤d*4 := by
  simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => valueLe (sel X i) (selInd h i))
theorem onlyActive {X : Vtx d m → Bool} (h : independent X) (all : ∀ i,value (sel X i)=4)
    {l : Label d} {j : Fin m} {s : Bool} (active : X (.inr (l,j,s))=true) : l=fun i => sel X i 0 := by
  funext i;by_contra ne
  have cl := classify (sel X i) (selInd h i) (all i)
  have neq : sel X i 0 = !(l i) := by cases a : l i <;> cases b : sel X i 0 <;> simp_all
  have yes : sel X i (representative (!(l i)) (!s))=true := by
    rw [congrFun cl _]; exact (hasRep _ _ _).mpr neq
  exact h _ _ (show edge (.inl (i,representative (!(l i)) (!s))) (.inr (l,j,s)) from rfl) ⟨yes,active⟩
end PEqualNP.Outside.L_lib_1515_aux

namespace PEqualNP.Outside.L_lib_1515_aux
open scoped Classical
def bonus (d m : Nat) := mult d m*(d*4)
theorem collision {X : Vtx d m → Bool} (h : independent X) l j :
    (∑s : Bool, if X (.inr (l,j,s)) then 1 else 0) ≤ 1 := by
  have bad := h (.inr (l,j,false)) (.inr (l,j,true)) ⟨rfl,rfl,rfl,rfl⟩
  rw [Fintype.sum_bool]
  cases a : X (.inr (l,j,false)) <;> cases b : X (.inr (l,j,true)) <;> simp_all
theorem activeExtras {X : Vtx d m → Bool} (h : independent X) (all : ∀i,value (sel X i)=4) : extras X ≤ m := by
  classical
  let l0 : Label d := fun i => sel X i 0
  unfold extras
  rw [Finset.sum_eq_single l0]
  · simpa using Finset.sum_le_sum (s:=Finset.univ) (fun j _ => collision h l0 j)
  · intro l _ ne;apply Finset.sum_eq_zero;intro j _
    apply Finset.sum_eq_zero;intro s _;split
    · rename_i yes;exact (ne (onlyActive h all yes)).elim
    · rfl
  · simp
theorem upperPay {X : Vtx d m → Bool} (h : independent X) : payoff X≤bonus d m+m := by
  classical
  rw [splitPay];unfold bonus
  by_cases all : ∀i,value (sel X i)=4
  · exact Nat.add_le_add (Nat.mul_le_mul_left _ (totalSel h)) (activeExtras h all)
  · obtain ⟨i,hi⟩ := not_forall.mp all
    have small : (∑j,value (sel X j)) < d*4 := by
      have hlt : (∑j,value (sel X j)) < ∑_j : Fin d, 4 :=
        Finset.sum_lt_sum (fun j _ => valueLe _ (selInd h j))
          ⟨i,Finset.mem_univ i,lt_of_le_of_ne (valueLe _ (selInd h i)) hi⟩
      simpa using hlt
    have enough := Nat.mul_le_mul_left (mult d m) small
    have extra : extras X < mult d m := Nat.lt_succ_of_le (maxExtras X)
    rw [Nat.mul_succ] at enough;omega
theorem pinnedBound {X : Vtx d m → Bool} (h : independent X) (off : pinsOff X) : payoff X≤bonus d m := by
  rw [splitPay,offPay off,Nat.add_zero];exact Nat.mul_le_mul_left _ (totalSel h)
def policy (l : Label d) (take : Fin m → Bool → Bool) : Vtx d m → Bool
  | .inl (i,a) => chosen (l i) a
  | .inr (k,j,s) => decide (k=l) && take j s
theorem policyInd (l : Label d) (take : Fin m → Bool → Bool) (one : ∀j,¬(take j false=true ∧ take j true=true)) :
    independent (policy l take) := by
  intro x y e
  rcases x with ⟨i,a⟩|⟨k,i,s⟩ <;> rcases y with ⟨j,b⟩|⟨l',j,t⟩
  · obtain ⟨rfl,ab⟩:=e;exact chosenInd _ _ _ ab
  · intro ⟨yes,hit⟩;simp only [policy,Bool.and_eq_true,decide_eq_true_eq] at hit
    obtain ⟨rfl,_⟩:=hit
    change chosen (l' i) a=true at yes
    rw [show a=representative (!(l' i)) (!t) from e] at yes
    have impossible := (hasRep _ _ _).mp yes;cases h : l' i <;> simp [h] at impossible
  · exact e.elim
  · obtain ⟨rfl,rfl,rfl,rfl⟩:=e
    simp only [policy,Bool.and_eq_true,decide_eq_true_eq]
    exact fun H => one _ ⟨H.1.2,H.2.2⟩
theorem policyPay (l : Label d) (take : Fin m → Bool → Bool) :
    payoff (policy l take)=bonus d m+∑j,∑s : Bool,if take j s then 1 else 0 := by
  classical
  rw [splitPay];congr 1
  · have hv (i) : value (sel (policy l take) i)=4 := chosenValue (l i)
    simp only [hv,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,bonus,Nat.cast_id]
  · unfold extras;rw [Finset.sum_eq_single l]
    · simp [policy]
    · intro k _ ne;simp [policy,ne]
    · simp
end PEqualNP.Outside.L_lib_1515_aux

namespace PEqualNP.Outside.L_lib_1515_aux
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
end PEqualNP.Outside.L_lib_1515_aux

namespace PEqualNP.Outside.L_lib_1515_aux
open scoped Classical
abbrev Node (d m : Nat) := Label d × Fin m × Bool
def selectors (e : Vtx d m ≃ Fin n) := Finset.univ.image (fun i : Fin d => e (.inl (i,0)))
theorem selectorEq (e : Vtx d m ≃ Fin n) : mark e deleted = selectors e := by
  ext x;rw [mem_mark];obtain ⟨v,rfl⟩:=e.surjective x
  rcases v with ⟨i,a⟩|⟨l,i,s⟩ <;> simp [selectors,deleted,eq_comm]
theorem selectorCount (e : Vtx d m ≃ Fin n) : (mark e deleted).card=d := by
  rw [selectorEq,selectors,Finset.card_image_of_injective]
  · simp
  · intro i j h;simpa using e.injective h
def port (e : Vtx d m ≃ Fin n) (u : Node d m) := e (.inr u)
theorem portInj (e : Vtx d m ≃ Fin n) : Function.Injective (port e) := fun _ _ h => Sum.inr.inj (e.injective h)
def flags (e : Vtx d m ≃ Fin n) := Finset.univ.image (fun u : Node d m => (port e u,true))
def pinned (Q : Finset (Fin n × Bool)) (C : Finset (Fin n)) := ∀a∈Q,decide (a.1∈C)=a.2
theorem flagsCount (e : Vtx d m ≃ Fin n) : (flags e).card=2*m*2^d := by
  rw [flags,Finset.card_image_of_injective]
  · simp [Node,Label,Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm]
  · intro i j h;exact portInj e (congrArg Prod.fst h)
theorem flagsRange (e : Vtx d m ≃ Fin n) : ((flags e).image Prod.fst).card=(flags e).card := by
  apply Finset.card_image_iff.mpr
  intro a ha b hb h
  obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp ha;obtain ⟨y,_,rfl⟩:=Finset.mem_image.mp hb
  exact Prod.ext h rfl
theorem flagsOff (e : Vtx d m ≃ Fin n) (C : Finset (Fin n)) : pinned (flags e) C ↔ pinsOff (omitted e C) := by
  constructor
  · intro h l i s
    have hp := h _ (Finset.mem_image_of_mem (fun u : Node d m => (port e u,true)) (Finset.mem_univ (l,i,s)))
    simpa [omitted,port] using (of_decide_eq_true hp)
  · intro h a ha;obtain ⟨⟨l,j,s⟩,_,rfl⟩ := Finset.mem_image.mp ha
    apply decide_eq_true
    simpa [port,omitted] using h l j s
def baseX (d m : Nat) := @policy d m (fun _ => false) (fun _ s => !s)
def offX (d m : Nat) := @policy d m (fun _ => false) (fun _ _ => false)
def freeX (u : Node d m) := policy u.1 (fun j s => decide (j=u.2.1 ∧ s=u.2.2))
theorem baseInd : independent (baseX d m) := policyInd _ _ (by simp)
theorem offInd : independent (offX d m) := policyInd _ _ (by simp)
theorem freeInd (u : Node d m) : independent (freeX u) := by
  apply policyInd;intro j;rcases u with ⟨l,i,s⟩;cases s <;> simp
theorem basePay : payoff (baseX d m)=bonus d m+m := by rw [baseX,policyPay];simp [Fintype.sum_bool]
theorem nonePay : payoff (offX d m)=bonus d m := by rw [offX,policyPay];simp
theorem freePay (u : Node d m) : payoff (freeX u)=bonus d m+1 := by
  rcases u with ⟨l,i,s⟩;rw [freeX,policyPay];congr 1
  rw [Finset.sum_eq_single i]
  · cases s <;> simp [Fintype.sum_bool]
  · intro j _ ne;simp [ne]
  · simp
theorem offTrue : pinsOff (offX d m) := by intro l j s;simp [offX,policy]
theorem freeOnly (u v : Node d m) : freeX u (.inr v)=true ↔ v=u := by
  rcases u with ⟨l,i,s⟩;rcases v with ⟨k,j,t⟩;simp [freeX,policy]
theorem freePinned (e : Vtx d m ≃ Fin n) (u : Node d m) :
    pinned ((flags e).erase (port e u,true)) (complement e (freeX u)) := by
  intro a ha;obtain ⟨ne,mem⟩:=Finset.mem_erase.mp ha
  obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp mem
  have vu : v≠u := by intro h;exact ne (h ▸ rfl)
  have no := (freeOnly u v).not.mpr vu
  simpa [complement,port] using no
end PEqualNP.Outside.L_lib_1515_aux

namespace PEqualNP.Outside.L_lib_1515_aux
open scoped Classical
theorem weighted (d r : Nat) :
    ∃ (n : Nat) (G : Finset (Fin n × Fin n)) (w : Fin n → Nat) (D S C0 : Finset (Fin n)) (Q : Finset (Fin n × Bool)),
    (∀e∈G,e.1<e.2) ∧ (∀v,0<w v) ∧ D.card=d ∧ Bip G D S ∧ Opt G w C0 ∧
    Q.card=2*(r+1)*2^d ∧ (Q.image Prod.fst).card=Q.card ∧
    (∀C,Cov G C → pinned Q C → C0.sum w+(r+1)≤C.sum w) ∧
    (∃C,Cov G C ∧ pinned Q C ∧ C.sum w=C0.sum w+(r+1)) ∧
    ∀a∈Q,∃C,Cov G C ∧ pinned (Q.erase a) C ∧ C.sum w≤C0.sum w+r := by
  classical
  let m := r+1
  let e := Fintype.equivFin (Vtx d m)
  let w := fun i => weight (e.symm i)
  let G := graph e edge
  let C0 := complement e (baseX d m)
  have bill (C) : C.sum w+payoff (omitted e C)=∑x : Vtx d m,weight x := costId e weight C
  have cost (X : Vtx d m → Bool) : (complement e X).sum w+payoff X=∑x : Vtx d m,weight x := by
    simpa only [omitted_comp] using bill (complement e X)
  have basecost : C0.sum w+(bonus d m+m)=∑x : Vtx d m,weight x := by simpa only [C0,basePay] using cost (baseX d m)
  refine ⟨_,G,w,mark e deleted,mark e side,C0,flags e,strictGraph _ _,fun _ => weightPos _,
    selectorCount _,graphBip _ _ _ _ (fun _ _ => edgeBip),⟨compCovered _ edgeIrrefl baseInd,?_⟩,
    flagsCount _,flagsRange _,?_,?_,?_⟩
  · intro C h;have up := upperPay ((graphCov e edge edgeIrrefl C).mp h);have := bill C;omega
  · intro C hc hp
    have upper := pinnedBound ((graphCov e edge edgeIrrefl C).mp hc) ((flagsOff e C).mp hp)
    have := bill C;change C0.sum w+m≤C.sum w;omega
  · let X := offX d m
    refine ⟨complement e X,compCovered _ edgeIrrefl offInd,(flagsOff _ _).mpr ?_,?_⟩
    · rw [omitted_comp];exact offTrue
    · have := cost X;rw [show payoff X=bonus d m from nonePay] at this
      change _=C0.sum w+m;omega
  · intro a ha;obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp ha
    refine ⟨complement e (freeX u),compCovered _ edgeIrrefl (freeInd u),freePinned e u,?_⟩
    have h := cost (freeX u);rw [freePay] at h;dsimp only [m] at basecost h ⊢;omega
end PEqualNP.Outside.L_lib_1515_aux

namespace PEqualNP.Outside.L_lib_1515_aux
open scoped Classical
abbrev Line (m : Nat) := Fin m × Fin 4
def nextV (a b : Fin 4) := b.val=a.val+1
instance (a b : Fin 4) : Decidable (nextV a b) := by unfold nextV;infer_instance
def pathEdge (x y : Line m) := x.1=y.1 ∧ nextV x.2 y.2
def lineOK (q : Fin 4 → Bool) := ∀a b,nextV a b → ¬(q a=true ∧ q b=true)
instance (q : Fin 4 → Bool) : Decidable (lineOK q) := by unfold lineOK;infer_instance
def worth (q : Fin 4 → Bool) := ∑a,if q a then 1 else 0
def leafAt (b : Bool) : Fin 4 := if b then 3 else 0
def pick (mask : Nat) (a : Fin 4) := mask.testBit a.val
def fixLeaf (s : Bool) := if s then pick 10 else pick 5
def lineSide (a : Fin 4) := a.val.testBit 0
theorem nextSide : ∀a b,nextV a b → lineSide a = !lineSide b := by decide +kernel
theorem noNext : ∀a,¬nextV a a := by decide +kernel
theorem smallDeg : ∀ a : Fin 4,(Finset.univ.filter (fun b => nextV a b ∨ nextV b a)).card≤2 := by decide +kernel
theorem lineBound : ∀q,lineOK q → worth q≤2 := by decide +kernel
theorem constrained : ∀q,lineOK q → (∀s,q (leafAt s)=false) → worth q≤1 := by decide +kernel
theorem baseline : lineOK (pick 9) ∧ worth (pick 9)=2 := by decide +kernel
theorem allPinned : lineOK (pick 2) ∧ worth (pick 2)=1 ∧ ∀s,pick 2 (leafAt s)=false := by decide +kernel
theorem released : ∀s,lineOK (fixLeaf s) ∧ worth (fixLeaf s)=2 ∧ ∀t,fixLeaf s (leafAt t)=true ↔ t=s := by decide +kernel
theorem leafInj : Function.Injective leafAt := by intro a b;cases a <;> cases b <;> decide
theorem lineIr (v : Line m) : ¬pathEdge v v := fun h => noNext _ h.2
def site (e : Line m ≃ Fin n) (v : Fin m × Bool) := e (v.1,leafAt v.2)
def leaves (e : Line m ≃ Fin n) := Finset.univ.image (site e)
theorem leafCount (e : Line m ≃ Fin n) : (leaves e).card=2*m := by
  rw [leaves,Finset.card_image_of_injective]
  · simp [Nat.mul_comm]
  · intro i j eq; have h:=e.injective eq;exact Prod.ext (congrArg (fun x : Line m => x.1) h) (leafInj (congrArg (fun x : Line m => x.2) h))
theorem pathOrient (e : Line m ≃ Fin n) : Bip (graph e pathEdge) ∅ (mark e (fun x => lineSide x.2)) := by
  have hz : mark e (fun _ => false)=∅ := by ext;simp [mark]
  rw [←hz];apply graphBip;intro x y h _ _;exact nextSide _ _ h.2
theorem indRow {X : Line m → Bool} (h : Ind pathEdge X) (i) : lineOK (fun a => X (i,a)) :=
  fun a b r => h _ _ ⟨rfl,r⟩
theorem byRows {X : Line m → Bool} (h : ∀i,lineOK (fun a => X (i,a))) : Ind pathEdge X := by
  rintro ⟨i,a⟩ ⟨j,b⟩ ⟨rfl,r⟩;exact h _ _ _ r
theorem readRows (X : Line m → Bool) : gain (fun _ => 1) X = ∑i,worth (fun a => X (i,a)) := by
  unfold gain worth;rw [Fintype.sum_prod_type]
theorem pathMax {X : Line m → Bool} (h : Ind pathEdge X) : gain (fun _ => 1) X ≤ m*2 := by
  rw [readRows];simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => lineBound _ (indRow h i))
theorem pinnedMax {X : Line m → Bool} (h : Ind pathEdge X) (q : ∀i s,X (i,leafAt s)=false) : gain (fun _ => 1) X ≤ m := by
  rw [readRows];simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => constrained _ (indRow h i) (q i))
def simplePolicy (mask : Nat) (v : Line m) := pick mask v.2
def partialPolicy (v : Fin m × Bool) (x : Line m) := if x.1=v.1 then fixLeaf v.2 x.2 else pick 2 x.2
theorem oneInd (v : Fin m × Bool) : Ind pathEdge (partialPolicy v) := by
  apply byRows;intro i;by_cases h : i=v.1
  · simpa only [partialPolicy,h,ite_true] using (released v.2).1
  · simpa only [partialPolicy,h,ite_false] using allPinned.1
theorem oneGain (v : Fin m × Bool) : gain (fun _ => 1) (partialPolicy v)=m+1 := by
  rw [readRows]
  have hr (i) : worth (fun a => partialPolicy v (i,a))=1+(if i=v.1 then 1 else 0) := by
    by_cases h : i=v.1
    · simpa only [partialPolicy,h,ite_true] using (released v.2).2.1
    · simpa only [partialPolicy,h,ite_false,Nat.add_zero] using allPinned.2.1
  simp [hr,Finset.sum_add_distrib]
theorem oneHits (v u : Fin m × Bool) : partialPolicy v (u.1,leafAt u.2)=true ↔ u=v := by
  by_cases h : u.1=v.1
  · simp only [partialPolicy,h,ite_true,(released v.2).2.2,Prod.ext_iff,h,true_and]
  · simp [partialPolicy,h,allPinned.2.2,Prod.ext_iff]
end PEqualNP.Outside.L_lib_1515_aux

namespace PEqualNP.Outside.L_lib_1515_aux
open scoped Classical
theorem maxDegree (e : Line m ≃ Fin n) (v : Fin n) :
    ((graph e pathEdge).filter (fun t => v=t.1 ∨ v=t.2)).card≤2 := by
  classical
  obtain ⟨⟨i,a⟩,rfl⟩ := e.surjective v
  let N := Finset.univ.filter (fun b => nextV a b ∨ nextV b a)
  let mk (b : Fin 4) := (min (e (i,a)) (e (i,b)),max (e (i,a)) (e (i,b)))
  have nbr {j b} (h : pathEdge (i,a) (j,b) ∨ pathEdge (j,b) (i,a)) : j=i ∧ b∈N := by
    rcases h with h|h
    · exact ⟨h.1.symm,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl h.2⟩⟩
    · exact ⟨h.1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr h.2⟩⟩
  apply le_trans (Finset.card_le_card (t:=N.image mk) ?_) (Finset.card_image_le.trans (smallDeg a))
  rintro ⟨x,y⟩ h
  obtain ⟨inside,hx|hy⟩:=Finset.mem_filter.mp h
  · change e (i,a)=x at hx
    subst x
    obtain ⟨⟨j,b⟩,rfl⟩ := e.surjective y
    obtain ⟨_,lt,ed⟩ := Finset.mem_filter.mp inside
    simp only [Equiv.symm_apply_apply] at ed
    obtain ⟨rfl,mem⟩ := nbr ed
    exact Finset.mem_image.mpr ⟨b,mem,by simp only [mk,min_eq_left lt.le,max_eq_right lt.le]⟩
  · change e (i,a)=y at hy
    subst y
    obtain ⟨⟨j,b⟩,rfl⟩ := e.surjective x
    obtain ⟨_,lt,ed⟩ := Finset.mem_filter.mp inside
    simp only [Equiv.symm_apply_apply] at ed
    obtain ⟨rfl,mem⟩ := nbr ed.symm
    exact Finset.mem_image.mpr ⟨b,mem,by simp only [mk,min_eq_right lt.le,max_eq_left lt.le]⟩
end PEqualNP.Outside.L_lib_1515_aux

namespace PEqualNP.Outside.L_lib_1515_aux
open scoped Classical
theorem paths (r : Nat) : let m := r+1
    ∃ (G : Finset (Fin (4*m) × Fin (4*m))) (S Q : Finset (Fin (4*m))),
    (∀e∈G,e.1<e.2) ∧ Bip G ∅ S ∧ (∀ v,(G.filter (fun t => v=t.1 ∨ v=t.2)).card ≤ 2) ∧ Q.card=2*m ∧
    (∃C,Opt G (fun _ => 1) C ∧ C.card=2*m) ∧
    (∀ C,Cov G C → Q⊆C → 3*m≤C.card) ∧
    (∃C,Cov G C ∧ Q⊆C ∧ C.card=3*m) ∧
    ∀ a∈Q,∃C,Cov G C ∧ Q.erase a⊆C ∧ C.card≤2*m+r := by
  classical
  intro m
  let e : Line m ≃ Fin (4*m) := Fintype.equivFinOfCardEq (by simp [Line,Nat.mul_comm])
  let G := graph e pathEdge
  have bill (C) : C.card+gain (fun _ => 1) (omitted e C)=4*m := by simpa [Line,Nat.mul_comm] using costId e (fun _ => 1) C
  have cost (X) : (complement e X).card+gain (fun _ => 1) X=4*m := by simpa only [omitted_comp] using bill (complement e X)
  have pin (C) : leaves e⊆C ↔ ∀i s,omitted e C (i,leafAt s)=false := by
    constructor
    · intro h i s
      have mem := h (Finset.mem_image_of_mem (site e) (Finset.mem_univ (i,s)))
      simpa [site,omitted] using mem
    · rintro h _ hy;obtain ⟨⟨i,s⟩,_,rfl⟩ := Finset.mem_image.mp hy
      simpa [omitted,site] using h i s
  have optimum (C) (h : Cov G C) : 2*m≤C.card := by
    have up := pathMax ((graphCov e _ lineIr _).mp h)
    have := bill C;omega
  refine ⟨G,_,leaves e,strictGraph _ _,pathOrient e,maxDegree e,leafCount e,?_,?_,?_,?_⟩
  · let X : Line m → Bool := simplePolicy 9
    have ok : Ind pathEdge X := by apply byRows;intro i;exact baseline.1
    have eq : gain (fun _ => 1) X=m*2 := by
      rw [readRows];simp only [show ∀i,worth (fun a => X (i,a))=2 from fun _ => baseline.2];simp
    have card : (complement e X).card=2*m := by have := cost X;omega
    refine ⟨complement e X,⟨compCovered _ lineIr ok,?_⟩,card⟩
    intro C h;simpa [card] using optimum C h
  · intro C h hc
    have up := pinnedMax ((graphCov e _ lineIr _).mp h) ((pin C).mp hc)
    have := bill C;omega
  · let X : Line m → Bool := simplePolicy 2
    have ok : Ind pathEdge X := by apply byRows;intro i;exact allPinned.1
    have eq : gain (fun _ => 1) X=m := by
      rw [readRows];simp only [show ∀i,worth (fun a => X (i,a))=1 from fun _ => allPinned.2.1];simp
    refine ⟨complement e X,compCovered _ lineIr ok,(pin _).mpr ?_,?_⟩
    · rw [omitted_comp];intro i s;exact allPinned.2.2 s
    · have := cost X;omega
  · intro a ha;obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp ha
    refine ⟨complement e (partialPolicy v),compCovered _ lineIr (oneInd v),?_,?_⟩
    · intro y hy;obtain ⟨ne,mem⟩:=Finset.mem_erase.mp hy
      obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp mem
      have uv : u≠v := fun eq => ne (congrArg (site e) eq)
      simpa [complement,site] using (oneHits v u).not.mpr uv
    · have h:=cost (partialPolicy v);rw [oneGain] at h;dsimp only [m] at *;omega
end PEqualNP.Outside.L_lib_1515_aux

namespace PEqualNP.Outside.L_lib_1515_aux
noncomputable def fixedImage {α β : Type*} (f : α → β) (A : Finset α) := @Finset.image α β (Classical.decEq β) f A
theorem imageUnique {α β : Type*} (d : DecidableEq β) (f : α → β) (A : Finset α) :
    @Finset.image α β d f A=fixedImage f A := by ext;simp only [fixedImage,Finset.mem_image]
noncomputable def fixedErase {α : Type*} (A : Finset α) (a : α) := @Finset.erase α (Classical.decEq α) A a
theorem eraseUnique {α : Type*} (d : DecidableEq α) (A : Finset α) (a : α) :
    @Finset.erase α d A a=fixedErase A a := by ext;simp only [fixedErase,Finset.mem_erase]
noncomputable def fixedFilter {α : Type*} (P : α → Prop) (A : Finset α) := @Finset.filter α P (fun _ => Classical.propDecidable _) A
theorem filterUnique {α : Type*} (P : α → Prop) (d : DecidablePred P) (A : Finset α) :
    @Finset.filter α P d A=fixedFilter P A := by ext;simp only [fixedFilter,Finset.mem_filter]
noncomputable def sameDecision (P : Prop) := @decide P (Classical.propDecidable P)
theorem decUnique (P : Prop) (d : Decidable P) : @decide P d=sameDecision P := by unfold sameDecision;congr 1
end PEqualNP.Outside.L_lib_1515_aux
open PEqualNP.Outside.L_lib_1515_aux in
theorem PEqualNP.Outside.L_lib_1515 : letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let cover := fun {N : Nat} (G : Finset (Fin N × Fin N)) (C : Finset (Fin N)) =>
  ∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C
let opt := fun {N : Nat} (G : Finset (Fin N × Fin N)) (w : Fin N → Nat) (C : Finset (Fin N)) =>
  cover G C ∧ ∀ B, cover G B → C.sum w ≤ B.sum w
let bip := fun {N : Nat} (G : Finset (Fin N × Fin N)) (D S : Finset (Fin N)) =>
  ∀ e ∈ G, e.1 ∉ D → e.2 ∉ D → (e.1 ∈ S ↔ e.2 ∉ S)
let view := fun {k N : Nat} (p : Fin k → Fin N) (C : Finset (Fin N)) =>
  Finset.univ.filter (fun i => p i ∈ C)
let pins := fun {n : Nat} (Q : Finset (Fin n × Bool)) (C : Finset (Fin n)) =>
  ∀ a ∈ Q, decide (a.1 ∈ C)=a.2
∀ d r : Nat,
let m := r+1
(∃ (n : Nat) (G : Finset (Fin n × Fin n)) (w : Fin n → Nat) (D S C0 : Finset (Fin n))
   (Q : Finset (Fin n × Bool)),
   (∀ e ∈ G, e.1<e.2) ∧ (∀ v, 0<w v) ∧ D.card=d ∧ bip G D S ∧ opt G w C0 ∧
   Q.card=2*m*2^d ∧ (Q.image Prod.fst).card=Q.card ∧
   (∀ C, cover G C → pins Q C → C0.sum w+m ≤ C.sum w) ∧
   (∃ C, cover G C ∧ pins Q C ∧ C.sum w=C0.sum w+m) ∧
   ∀ a ∈ Q, ∃ C, cover G C ∧ pins (Q.erase a) C ∧ C.sum w ≤ C0.sum w+r) ∧
∃ (G : Finset (Fin (4*m) × Fin (4*m))) (S Q : Finset (Fin (4*m))),
  (∀ e ∈ G, e.1<e.2) ∧ bip G ∅ S ∧
  (∀ v, (G.filter (fun e => e.1=v ∨ e.2=v)).card ≤ 2) ∧ Q.card=2*m ∧
  (∃ C, opt G (fun _ => 1) C ∧ C.card=2*m) ∧
  (∀ C, cover G C → Q ⊆ C → 3*m ≤ C.card) ∧
  (∃ C, cover G C ∧ Q ⊆ C ∧ C.card=3*m) ∧
  ∀ a ∈ Q, ∃ C, cover G C ∧ Q.erase a ⊆ C ∧ C.card ≤ 2*m+r := by
  classical
  intro cover' opt' bip' view' pins' d r m
  constructor
  · simpa only [m,bip',Bip,opt',Opt,cover',Cov,pins',pinned,decUnique,imageUnique,eraseUnique] using weighted d r
  · simpa only [m,bip',Bip,opt',Opt,cover',Cov,eraseUnique,filterUnique,eq_comm] using paths r
