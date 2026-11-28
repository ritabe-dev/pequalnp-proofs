import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1492_aux
open scoped Classical
abbrev Edges (n : ℕ) := Finset (Fin n × Fin n)
def pairs (S : Finset (Fin n)) : Edges n := (S ×ˢ S).filter (fun e => e.1<e.2)
def clique (G : Edges n) (S : Finset (Fin n)) := ∀a∈S,∀b∈S,a<b → (a,b)∈G
theorem pairsCard (S : Finset (Fin n)) : (pairs S).card=S.card.choose 2 := Finset.card_product_filter_lt
theorem subPairs (G : Edges n) (S : Finset (Fin n)) : pairs S⊆G ↔ clique G S := by
  constructor
  · intro h a ha b hb lt; exact h (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩,lt⟩)
  · intro h e he; obtain ⟨ab,lt⟩ := Finset.mem_filter.mp he
    exact h _ (Finset.mem_product.mp ab).1 _ (Finset.mem_product.mp ab).2 lt
noncomputable def omegaN (G : Edges n) := (Finset.univ : Finset (Finset (Fin n))).sup (fun S => if clique G S then S.card else 0)
theorem attained (G : Edges n) : ∃ S,clique G S ∧ S.card=omegaN G := by
  classical
  obtain ⟨S,_,h⟩ := Finset.exists_mem_eq_sup _ (Finset.univ_nonempty : (Finset.univ : Finset (Finset (Fin n))).Nonempty)
    (fun S => if clique G S then S.card else 0)
  by_cases c : clique G S
  · exact ⟨S,c,by simpa [omegaN,c] using h.symm⟩
  · exact ⟨∅,by simp [clique],by simpa [omegaN,c] using h.symm⟩
theorem cliqueBound (G : Edges n) {S} (c : clique G S) : S.card ≤ omegaN G := by
  simpa [c,omegaN] using Finset.le_sup (s:=(Finset.univ : Finset (Finset (Fin n)))) (f:=fun T => if clique G T then T.card else 0) (Finset.mem_univ S)
theorem smallClique (G : Edges n) {r} (le : r ≤ omegaN G) : ∃ S,clique G S ∧ S.card=r := by
  obtain ⟨A,hA,ca⟩ := attained G
  obtain ⟨S,sub,cs⟩ := Finset.exists_subset_card_eq (ca ▸ le : r ≤ A.card)
  exact ⟨S,fun a ha b hb => hA a (sub ha) b (sub hb),cs⟩
def priceCost (n p s : ℕ) := p*(n-s)+s.choose 2
theorem diff {s n : ℕ} (p : ℕ) (lt : s<n) : priceCost n p (s+1)+p=priceCost n p s+s := by
  have h : n-s=(n-(s+1))+1 := by omega
  unfold priceCost; rw [h,Nat.mul_add,Nat.mul_one,Nat.choose_succ_succ,Nat.choose_one_right]; change p*(n-(s+1))+(s+s.choose 2)+p=(p*(n-(s+1))+p)+s.choose 2+s;omega
theorem down {a b n p : ℕ} (ab : a ≤ b) (nb : b ≤ n) (pb : b ≤ p) : priceCost n p b+(b-a) ≤ priceCost n p a := by
  induction b,ab using Nat.le_induction with
  | base => simp
  | succ i ai ih =>
    have h := ih (by omega) (by omega)
    have e := diff p (show i<n by omega)
    omega
theorem up {a b n p : ℕ} (ab : a ≤ b) (bn : b ≤ n) (pa : p ≤ a) : priceCost n p a  ≤  priceCost n p b := by
  induction b,ab using Nat.le_induction with
  | base => rfl
  | succ i ai ih =>
    have h := ih (by omega);have e := diff p (show i<n by omega);omega
theorem leastCost {n p c s : ℕ} (sc : s ≤ c) (cn : c ≤ n) :
    priceCost n p (min p c)  ≤  priceCost n p s := by
  by_cases h : s ≤ min p c
  · have q := down h (show min p c ≤ n by omega) (min_le_left _ _);omega
  · have e : min p c=p := by omega
    rw [e];apply up <;> omega
end PEqualNP.Outside.L_lib_1492_aux

namespace PEqualNP.Outside.L_lib_1492_aux
open scoped Classical
abbrev Blocks (n p : ℕ) := Fin n → Finset (Fin p)
def passes (X : Blocks n p) (E : Edges n) := ∀a b : Fin n,a<b → X a=Finset.univ ∨ X b=Finset.univ ∨ (a,b)∈E
def feasible (G : Edges n) (p cap : ℕ) := ∃ (X : Blocks n p) (E : Edges n),E⊆G ∧ (∑a,(X a).card)+E.card ≤ cap ∧ passes X E
theorem omegaLe (G : Edges n) : omegaN G ≤ n := by
  obtain ⟨S,_,c⟩ := attained G;rw [←c]; simpa using Finset.card_le_univ S
theorem total {S : Finset (Fin n)} (p : ℕ) :
    (∑a : Fin n,(if a∈S then 0 else p))=p*(n-S.card) := by
  classical
  have h (a : Fin n) : (if a∈S then 0 else p) = if a∈Sᶜ then p else 0 := by by_cases a∈S <;> simp [*]
  simp only [h,←Finset.sum_filter]
  rw [show Finset.univ.filter (fun a => a∈Sᶜ) = Sᶜ from by ext; simp]
  simp [Finset.card_compl,Nat.mul_comm]
theorem exactCost (G : Edges n) (p cap : ℕ) :
    feasible G p cap ↔ priceCost n p (min p (omegaN G)) ≤ cap := by
  classical
  constructor
  · rintro ⟨X,E,eg,budget,ok⟩
    let S := Finset.univ.filter (fun a => X a≠Finset.univ)
    have sm (a) : a∈S ↔ X a≠Finset.univ := by simp [S]
    have seen : pairs S⊆E := (subPairs _ _).mpr (by
      intro a ha b hb lt; rcases ok a b lt with u|v|e
      · exact ((sm a).mp ha u).elim
      · exact ((sm b).mp hb v).elim
      · exact e)
    have cl := (subPairs _ _).mp (seen.trans eg)
    have lower : p*(n-S.card) ≤ ∑a,(X a).card := by
      rw [←total (S:=S)]; apply Finset.sum_le_sum
      intro a _; by_cases u : a∈S
      · simp [u]
      · have e : X a=Finset.univ := by simpa only [sm,not_not] using u
        simp [u,e]
    have count := Finset.card_le_card seen; rw [pairsCard] at count
    exact (leastCost (cliqueBound G cl) (omegaLe G)).trans ((Nat.add_le_add lower count).trans budget)
  · intro enough
    obtain ⟨S,c,cs⟩ := smallClique G (min_le_right p (omegaN G))
    let X (a : Fin n) : Finset (Fin p) := if a∈S then ∅ else Finset.univ
    have count (a : Fin n) : (X a).card=if a∈S then 0 else p := by by_cases a∈S <;> simp [X, *]
    refine ⟨X,pairs S,(subPairs _ _).mpr c,?_,?_⟩
    · simpa only [count,total,pairsCard,cs,priceCost] using enough
    · intro a b lt; by_cases ha : a∈S <;> by_cases hb : b∈S
      · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩,lt⟩))
      · exact Or.inr (Or.inl (by simp [X,hb]))
      · exact Or.inl (by simp [X,ha])
      · exact Or.inl (by simp [X,ha])
theorem completeWithin (S : Finset (Fin n)) (ne : S.Nonempty) : omegaN (pairs S)=S.card := by
  apply le_antisymm _ (cliqueBound _ ((subPairs _ _).mp (le_refl _)))
  obtain ⟨T,c,ct⟩ := attained (pairs S)
  rw [←ct]; by_contra! large
  have sz := Finset.card_pos.mpr ne
  have lt : 1<T.card := by omega
  have sub : T⊆S := by
    intro a ha
    obtain ⟨b,hb,diff⟩ := Finset.exists_mem_ne (s:=T) lt a
    rcases lt_or_gt_of_ne diff with ba|ab
    · exact (Finset.mem_product.mp (Finset.mem_filter.mp (c b hb a ha ba)).1).2
    · exact (Finset.mem_product.mp (Finset.mem_filter.mp (c a ha b hb ab)).1).1
  exact (Nat.not_le_of_lt large) (Finset.card_le_card sub)
theorem threshold (n p t : ℕ) (two : 2 ≤ t) (tn : t ≤ n) :
    (∀G : Edges n,feasible G p (priceCost n p t) ↔ t ≤ omegaN G) ↔ t ≤ p := by
  classical
  constructor
  · intro h;by_contra! low
    have small : t-1 ≤ (Finset.univ : Finset (Fin n)).card := by simp;omega
    obtain ⟨S,_,cs⟩ := Finset.exists_subset_card_eq small
    have ne : S.Nonempty := Finset.card_pos.mp (by omega)
    have om := completeWithin S ne;rw [cs] at om
    have pe : min p (omegaN (pairs S))=p := by omega
    have fit := (exactCost (pairs S) p (priceCost n p t)).mpr (by rw [pe]; exact up low.le tn (le_refl p))
    have ht := (h (pairs S)).mp fit;omega
  · intro tp G; rw [exactCost]
    constructor
    · intro bound; by_contra! lo
      have e : min p (omegaN G)=omegaN G := by omega
      rw [e] at bound; have x := down lo.le tn tp;omega
    · intro yes; exact leastCost yes (omegaLe G)
end PEqualNP.Outside.L_lib_1492_aux

namespace PEqualNP.Outside.L_lib_1492_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
variable {α : Type}
abbrev Gates := List Gate
def run (gs : Gates) (xs : List Bool) := (Circuit.mk gs 0).wires xs
theorem runLen (gs : Gates) (xs) : (run gs xs).length=xs.length+gs.length := by
  induction gs generalizing xs with
  | nil => simp [run,Circuit.wires]
  | cons g gs ih => change (run gs (xs++[_])).length=_; rw [ih];simp;omega
theorem appendRun (gs tail : Gates) (xs) : run (gs++tail) xs=run tail (run gs xs) := by simp [run,Circuit.wires,List.foldl_append]
theorem kept (gs : Gates) (xs : List Bool) (i) (hi : i<xs.length) : (run gs xs).getD i false=xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih => change (run gs (xs++[_])).getD i false=_;rw [ih _ (by simp;omega),List.getD_append _ _ _ _ hi]
def physical (m : ℕ) (gs : Gates) := ∀ u<gs.length,
  let g := gs.getD u ⟨.or,[]⟩
  (g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2 ∧ ∀ i∈g.inputs,i < m+u
def flat (inputs : List (α → Bool)) (x : α) := inputs.map (fun f => f x)
def holds (inputs : List (α → Bool)) (gs : Gates) (f : α → Bool) := ∃ i, i < inputs.length+gs.length ∧
  ∀ x, (run gs (flat inputs x)).getD i false=f x
theorem via {inputs : List (α → Bool)} {gs hs : Gates} {f : α → Bool}
    (pre : gs <+: hs) (wf : holds inputs gs f) : holds inputs hs f := by
  obtain ⟨tail,rfl⟩ := pre; obtain ⟨i,hi,h⟩ := wf
  exact ⟨i,by simp;omega,fun x => by rw [appendRun,kept _ _ _ (by simpa [runLen,flat] using hi),h]⟩
theorem rawWire (inputs : List (α → Bool)) (f : α → Bool) (m : f∈inputs) : holds inputs [] f := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp m
  exact ⟨i,by simpa using hi,fun x => by simp [run,Circuit.wires,flat,List.getD_eq_getElem?_getD,hi,eq]⟩
def comb (c a b : Bool) := if c then a && b else a || b
theorem appendOne (inputs : List (α → Bool)) (gs : Gates) (ok : physical inputs.length gs)
    {f g : α → Bool} (wf : holds inputs gs f) (wg : holds inputs gs g) (c : Bool) :
    ∃ hs : Gates, gs <+: hs ∧ hs.length=gs.length+1 ∧ physical inputs.length hs ∧ holds inputs hs (fun x => comb c (f x) (g x)) := by
  obtain ⟨i,hi,fi⟩ := wf; obtain ⟨j,hj,gj⟩ := wg
  let gate : Gate := ⟨if c then .and else .or,[i,j]⟩
  refine ⟨gs++[gate],⟨_,rfl⟩,by simp,?_,inputs.length+gs.length,by simp,?_⟩
  · intro u hu
    by_cases lt : u<gs.length
    · rw [List.getD_append _ _ _ _ lt];exact ok u lt
    · have eq : u=gs.length := by simp at hu;omega
      subst u; rw [List.getD_append_right _ _ _ _ le_rfl]; cases c <;> simp [gate,hi,hj]
  · intro x
    rw [appendRun]
    let ws := run gs (flat inputs x)
    have len : ws.length=inputs.length+gs.length := by simp [ws,runLen,flat]
    change (ws++[_]).getD _ false=_
    rw [←len,List.getD_append_right _ _ _ _ le_rfl,Nat.sub_self,List.getD_cons_zero]
    have fi' := fi x; have gj' := gj x
    simp only [List.getD_eq_getElem?_getD] at fi' gj'
    cases c <;> simp [gate,GateOp.eval,List.map,fi',gj',comb]
end PEqualNP.Outside.L_lib_1492_aux

namespace PEqualNP.Outside.L_lib_1492_aux
variable {α β : Type}
open scoped Classical
theorem buildAll (inputs : List (α → Bool)) (gs : Gates) (hp : physical inputs.length gs)
    (unit : holds inputs gs (fun _ => true)) (atom : β → α → Bool)
    (lst : List β) (atoms : ∀i∈lst,holds inputs gs (atom i)) :
    ∃hs, gs <+: hs ∧ hs.length=gs.length+lst.length ∧ physical inputs.length hs ∧
      holds inputs hs (fun x => lst.all (fun i => atom i x)) := by
  induction lst with
  | nil => exact ⟨gs,⟨[], by simp⟩,by simp,hp,unit⟩
  | cons i l ih =>
    obtain ⟨a,pre,len,ok,old⟩ := ih (fun j hj => atoms j (by simp [hj]))
    obtain ⟨hs,pre',cnt,last,h⟩ := appendOne inputs a ok (via pre (atoms i (by simp))) old true
    exact ⟨hs,pre.trans pre',by simp [cnt,len,Nat.add_assoc],last,h⟩
theorem buildMany (inputs : List (α → Bool)) (f : β → α → Bool) (p : ℕ)
    (base : Gates) (make : ∀ (i : β) gs,base <+: gs → physical inputs.length gs → ∃ hs,gs <+: hs ∧ hs.length=gs.length+p ∧
      physical inputs.length hs ∧ holds inputs hs (f i))
    (lst : List β) :
    ∀gs,base <+: gs → physical inputs.length gs → ∃hs, gs <+: hs ∧ hs.length=gs.length+lst.length*p ∧
      physical inputs.length hs ∧ ∀i∈lst,holds inputs hs (f i) := by
  induction lst with
  | nil => intro gs pre0 hp; exact ⟨gs,⟨[], by simp⟩,by simp,hp,by simp⟩
  | cons i l ih =>
    intro gs pre0 hp
    obtain ⟨a,pre,len,ok,old⟩ := ih gs pre0 hp
    obtain ⟨hs,pre',cnt,last,h⟩ := make i a (pre0.trans pre) ok
    refine ⟨hs,pre.trans pre',by simp [cnt,len,Nat.succ_mul,Nat.add_assoc],last,?_⟩
    intro j hj; rcases List.mem_cons.mp hj with rfl|inside
    · exact h
    · exact via pre' (old j inside)
end PEqualNP.Outside.L_lib_1492_aux

namespace PEqualNP.Outside.L_lib_1492_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped Classical
abbrev Sample (n p : Nat) := Blocks n p × Edges n
def bit (a : Fin n) (j : Fin p) (x : Sample n p) := decide (j∈x.1 a)
def edge (a b : Fin n) (x : Sample n p) := decide ((a,b)∈x.2)
def bank (n p : Nat) : List (Sample n p → Bool) :=
  (List.ofFn (fun a : Fin n => List.ofFn (fun j : Fin p => bit a j))).flatten ++
  (List.ofFn (fun a : Fin n => List.ofFn (fun b : Fin n => edge a b))).flatten ++ [fun _ => false, fun _ => true]
def full (a : Fin n) (x : Sample n p) := (List.finRange p).all (fun j => bit a j x)
def clause (ab : Fin n × Fin n) (x : Sample n p) := comb false (comb false (full ab.1 x) (full ab.2 x)) (edge ab.1 ab.2 x)
theorem bankLen (n p : Nat) : (bank n p).length = n*p+n*n+2 := by
  simp [bank,List.length_flatten,List.map_ofFn,Function.comp_def,List.ofFn_const,Nat.add_assoc]
theorem allBit (a : Fin n) (j : Fin p) (gs : Gates) : holds (bank n p) gs (bit a j) := by
  apply via List.nil_prefix; apply rawWire
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_flatten.mpr
  exact ⟨_,List.mem_ofFn.mpr ⟨a,rfl⟩,List.mem_ofFn.mpr ⟨j,rfl⟩⟩
theorem allEdge (a b : Fin n) (p : Nat) (gs : Gates) : holds (bank n p) gs (edge a b) := by
  apply via List.nil_prefix; apply rawWire
  apply List.mem_append_left; apply List.mem_append_right; apply List.mem_flatten.mpr
  exact ⟨_,List.mem_ofFn.mpr ⟨a,rfl⟩,List.mem_ofFn.mpr ⟨b,rfl⟩⟩
theorem allTrue (n p : Nat) (gs : Gates) : holds (bank n p) gs (fun _ => true) := by
  apply via List.nil_prefix; apply rawWire; apply List.mem_append_right; simp
theorem fullOK (a : Fin n) (x : Sample n p) : full a x=true ↔ x.1 a=Finset.univ := by
  simp [full,bit,List.all_eq_true,Finset.eq_univ_iff_forall]
theorem circuitList (n p : Nat) :
    ∃gs : Gates, gs.length = n*p+3*(n.choose 2) ∧ physical (bank n p).length gs ∧
      ∃out, out < (bank n p).length+gs.length ∧ ∀x : Sample n p,
        (run gs (flat (bank n p) x)).getD out false=true ↔ passes x.1 x.2 := by
  let ins := bank n p
  obtain ⟨g,_,vg,legal,vertex⟩ := buildMany ins (full (n:=n) (p:=p)) p []
    (fun a gs _ hp => by
      unfold full
      simpa only [List.length_finRange] using buildAll ins gs hp (allTrue n p gs) (bit a) (List.finRange p) (fun j _ => allBit a j gs))
    (List.finRange n) [] (⟨[], by simp⟩) (by simp [physical])
  simp only [List.length_nil,List.length_finRange,Nat.zero_add] at vg
  let es := (pairs (Finset.univ : Finset (Fin n))).toList
  have ec : es.length=n.choose 2 := by simp [es,pairsCard]
  have member (a b : Fin n) : (a,b)∈es ↔ a<b := by simp [es,pairs]
  obtain ⟨g',_,vg',legal',clauses⟩ := buildMany ins (clause (n:=n) (p:=p)) 2 g
    (fun ab gs pre hp => by
      obtain ⟨s,pre',len,ok,both⟩ := appendOne ins gs hp (via pre (vertex ab.1 (by simp))) (via pre (vertex ab.2 (by simp))) false
      obtain ⟨t,pre'',len',ok',final⟩ := appendOne ins s ok both (allEdge ab.1 ab.2 p s) false
      exact ⟨t,pre'.trans pre'',by omega,ok',final⟩)
    es g (⟨[], by simp⟩) legal
  obtain ⟨gs,_,len,final,idx,hi,hval⟩ := buildAll ins g' legal' (allTrue n p g') clause es clauses
  refine ⟨gs,by omega,final,idx,hi,?_⟩
  intro x;rw [hval,List.all_eq_true]
  constructor
  · intro h a b lt
    simpa [clause,comb,edge,fullOK,or_assoc] using h (a,b) ((member a b).mpr lt)
  · intro h ⟨a,b⟩ inside
    simpa [clause,comb,edge,fullOK,or_assoc] using h a b ((member a b).mp inside)
end PEqualNP.Outside.L_lib_1492_aux

namespace PEqualNP.Outside.L_lib_1492_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem circuitProof (n p : Nat) : ∃ D : Circuit,
    (FanInTwo D ∧ NestedCover.ReadsBack (n*p+n*n+2) D ∧ D.output < n*p+n*n+2+D.size) ∧
    PEqualNP.NotBracket.notCount D=0 ∧ D.size ≤ n*p+3*n.choose 2+1 ∧
    ∀x : Sample n p, D.eval (flat (bank n p) x)=true ↔ passes x.1 x.2 := by
  obtain ⟨gs,count,law,out,hi,ev⟩ := circuitList n p
  rw [bankLen] at law hi
  have gate (g : Gate) (hg : g∈gs) : (g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2 := by
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hg
    have got := law i hi
    dsimp only at got
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some,he] at got
    exact ⟨got.1,got.2.1⟩
  refine ⟨⟨gs,out⟩,⟨?_,?_,hi⟩,?_,by change gs.length ≤ _; omega,ev⟩
  · intro g hg; obtain ⟨op,len⟩ := gate g hg; refine ⟨?_,len.le⟩; rcases op with op|op <;> simp [op]
  · intro i hi j hj; exact (law i hi).2.2 j hj
  · unfold PEqualNP.NotBracket.notCount
    rw [List.filter_eq_nil_iff.mpr]; rfl
    intro g hg; rcases (gate g hg).1 with w|w <;> simp [w]
noncomputable def truth (q : Prop) := @decide q (Classical.propDecidable q)
theorem normalTruth (q : Prop) (d : Decidable q) : @decide q d=truth q := by unfold truth; congr 1
end PEqualNP.Outside.L_lib_1492_aux

open PEqualNP.Outside.L_lib_1492_aux in
theorem PEqualNP.Outside.L_lib_1492 : letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let valid := fun (h : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.FanInTwo D ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (h+2) D ∧ D.output < h+2+D.size
let pos := fun (h : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => valid h D ∧ PEqualNP.NotBracket.notCount D=0
∀ (n price : Nat),
  let input := fun (X : Fin n → Finset (Fin price)) (E : Finset (Fin n × Fin n)) =>
    (List.ofFn (fun a : Fin n => List.ofFn (fun j : Fin price => decide (j ∈ X a)))).flatten ++
    (List.ofFn (fun a : Fin n => List.ofFn (fun b : Fin n => decide ((a,b) ∈ E)))).flatten ++ [false,true]
  let clq := fun (G : Finset (Fin n × Fin n)) (S : Finset (Fin n)) =>
    ∀ a ∈ S, ∀ b ∈ S, a<b → (a,b) ∈ G
  let omega := fun G => (Finset.univ : Finset (Finset (Fin n))).sup
    (fun S => if clq G S then S.card else 0)
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, pos (n*price+n*n) D ∧ D.size ≤ n*price+3*(Nat.choose n 2)+1 ∧
    (∀ X E, D.eval (input X E)=true ↔
      ∀ a b : Fin n, a<b → X a=Finset.univ ∨ X b=Finset.univ ∨ (a,b) ∈ E) ∧
    let feasible := fun (G : Finset (Fin n × Fin n)) (cap : Nat) =>
      ∃ (X : Fin n → Finset (Fin price)) (E : Finset (Fin n × Fin n)), E ⊆ G ∧
        (Finset.univ.sum (fun a : Fin n => (X a).card))+E.card ≤ cap ∧ D.eval (input X E)=true
    (∀ G cap, let r := min price (omega G)
              feasible G cap ↔ price*(n-r)+Nat.choose r 2 ≤ cap) ∧
    ∀ t : Nat, 2 ≤ t → t ≤ n →
      ((∀ G, feasible G (price*(n-t)+Nat.choose t 2) ↔ t ≤ omega G) ↔ t ≤ price) := by
  classical
  intro valid pos n p input clq om
  obtain ⟨D,legal,positive,cost,h⟩ := circuitProof n p
  have inputEq (X : Blocks n p) (E : Edges n) : input X E=flat (bank n p) (X,E) := by
    simp [input,flat,bank,List.map_flatten,List.map_ofFn,Function.comp_def,bit,edge,normalTruth]
  have accepted (X : Blocks n p) (E : Edges n) : D.eval (input X E)=true ↔ passes X E := by
    rw [inputEq]; exact h (X,E)
  have omEq (G : Edges n) : om G=omegaN G := by
    unfold om omegaN
    congr 1
  refine ⟨D,⟨legal,positive⟩,cost,accepted,?_⟩
  intro fit
  have fits (G : Edges n) (cap : Nat) : fit G cap ↔ feasible G p cap := by
    simp only [fit,feasible,accepted]
  constructor
  · intro G cap; rw [fits,omEq]; exact exactCost G p cap
  · intro t ht tn; simpa only [fits,omEq,priceCost] using threshold n p t ht tn
