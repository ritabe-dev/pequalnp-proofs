import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1586_aux
open scoped Classical
abbrev Bits (m : Nat) := Finset (Fin m)
abbrev Bank (m : Nat) := Finset (Bits m)
def seed (m : Nat) : Bank m := insert ∅ (Finset.univ.image fun i => {i})
theorem rawMem (i : Fin m) : ({i} : Bits m)∈seed m := by simp [seed]
inductive Chain {m : Nat} (initial : Bank m) : Nat → Bank m → Prop
  | start : Chain initial 0 initial
  | step : Chain initial n B → a∈B → b∈B → Chain initial (n+1) (insert (a∪b) B)
theorem grow {I B : Bank m} (ch : Chain I n B) : I⊆B := by induction ch with
  | start => exact Finset.Subset.rfl
  | step _ _ _ ih => exact ih.trans (Finset.subset_insert ..)
theorem replay {I B I' : Bank m} (ch : Chain I n B) (sub : I⊆I') :
    ∃B',Chain I' n B' ∧ B⊆B' := by
  induction ch with
  | start => exact ⟨_,.start,sub⟩
  | @step n bank a b _ ha hb ih =>
    obtain ⟨z,cc,hz⟩:=ih
    exact ⟨_,.step cc (hz ha) (hz hb),Finset.insert_subset_insert _ hz⟩
theorem splice {I B D : Bank m} (first : Chain I n B) (next : Chain B t D) : Chain I (n+t) D := by
  induction next with
  | start => exact first
  | step _ ha hb ih => exact .step ih ha hb
def Has (B : Bank m) (targets : Fin n → Bits m) := ∀j,(targets j).Nonempty → targets j∈B
def Budget (targets : Fin n → Bits m) (s : Nat) := ∃ r ≤ s,∃B,Chain (seed m) r B ∧ Has B targets
theorem collect {I : Bank m} (T : Finset (Bits m)) (sub : T⊆I) (ne : T.Nonempty) :
    ∃B,Chain I (T.card-1) B ∧ T.biUnion id∈B := by
  classical
  induction T using Finset.induction_on with
  | empty => simp at ne
  | @insert A T fr ih =>
    have ha : A∈I := sub (Finset.mem_insert_self ..)
    by_cases em:T=∅
    · subst T;simpa using (show ∃B,Chain I 0 B ∧ A∈B from ⟨I,.start,ha⟩)
    · obtain ⟨B,ch,h⟩:=ih (fun x hx => sub (Finset.mem_insert_of_mem hx)) (Finset.nonempty_iff_ne_empty.mpr em)
      have a:=grow ch ha
      have eq : (insert A T).card-1=(T.card-1)+1 := by rw [Finset.card_insert_of_notMem fr];have p:=Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr em);omega
      rw [eq,Finset.biUnion_insert];exact ⟨_,.step ch a h,Finset.mem_insert_self ..⟩
end PEqualNP.Outside.L_lib_1586_aux

namespace PEqualNP.Outside.L_lib_1586_aux
open scoped Classical
inductive Ledger {m : Nat} (I : Bank m) : List (Bits m) → Bank m → Prop
  | nil : Ledger I [] I
  | cons : Ledger I log B → a∈B → b∈B → Ledger I ((a∪b)::log) (insert (a∪b) B)
theorem ledgerOfChain {I B : Bank m} (ch : Chain I n B) : ∃log,Ledger I log B ∧ log.length=n := by
  induction ch with
  | start => exact ⟨[],.nil,rfl⟩
  | step _ ha hb ih => obtain ⟨log,l,rfl⟩:=ih;exact ⟨_,.cons l ha hb,rfl⟩
theorem extractLeaves {I B : Bank m} (ch : Chain I n B) (D : Bank m) (sub : D⊆B) :
    ∃T : Bank m,T⊆I ∧ T.biUnion id=D.biUnion id ∧ T.card ≤ D.card+n := by
  classical
  induction ch generalizing D with
  | start => exact ⟨D,sub,rfl,by omega⟩
  | @step r B a b _ ha hb ih =>
    by_cases active : a∪b∈D
    · let R := D.erase (a∪b)
      let prev := insert a (insert b R)
      have shrink : R⊆B := by
        intro z hz;obtain ⟨ne,mem⟩:=Finset.mem_erase.mp hz
        exact (Finset.mem_insert.mp (sub mem)).resolve_left ne
      have incl : prev⊆B := Finset.insert_subset_iff.mpr ⟨ha,Finset.insert_subset_iff.mpr ⟨hb,shrink⟩⟩
      obtain ⟨T,ti,eq,sz⟩:=ih _ incl
      have same : prev.biUnion id=D.biUnion id := by
        have old : insert (a∪b) R=D := Finset.insert_erase active
        conv_rhs => rw [←old,Finset.biUnion_insert]
        simp [prev,Finset.union_assoc]
      have c1:=Finset.card_insert_le a (insert b R);have c2:=Finset.card_insert_le b R
      have c3 : R.card+1=D.card := Finset.card_erase_add_one active
      exact ⟨T,ti,eq.trans same,by dsimp only [prev] at sz;omega⟩
    · have ss : D⊆B := by
        intro z hz;rcases Finset.mem_insert.mp (sub hz) with rfl|h
        · exact (active hz).elim
        · exact h
      obtain ⟨T,sub,eq,sz⟩:=ih _ ss
      exact ⟨T,sub,eq,by omega⟩
theorem restrictLedger {I B : Bank m} (lg : Ledger I log B) (E : Bank m)
    (use paid : Bits m → Prop) (hered : ∀{A B},A⊆B → use B → use A)
    (base : ∀A∈I,use A → A∈E) (free : ∀A∈B,use A → ¬paid A → A∈E) :
    ∃r ≤ (log.filter (fun A => decide (paid A))).length,∃Z,Chain E r Z ∧ ∀A∈B,use A → A∈Z := by
  classical
  induction lg with
  | nil => exact ⟨0,by simp,E,.start,base⟩
  | @cons log B a b lg ha hb ih =>
    obtain ⟨r,cap,Z,ch,known⟩:=ih (fun A h => free A (Finset.mem_insert_of_mem h))
    by_cases h : use (a∪b) ∧ paid (a∪b)
    · have aa:=known _ ha (hered Finset.subset_union_left h.1)
      have bb:=known _ hb (hered Finset.subset_union_right h.1)
      refine ⟨r+1,by simpa [h.2] using cap,_,.step ch aa bb,?_⟩
      intro A mem hu;rcases Finset.mem_insert.mp mem with rfl|mem
      · exact Finset.mem_insert_self .. 
      · exact Finset.mem_insert_of_mem (known _ mem hu)
    · refine ⟨r,?_,Z,ch,?_⟩
      · by_cases paid' : paid (a∪b) <;> simp [paid'] <;> omega
      · intro A mem hu;rcases Finset.mem_insert.mp mem with rfl|mem
        · exact grow ch (free _ (Finset.mem_insert_self ..) hu (fun p => h ⟨hu,p⟩))
        · exact known _ mem hu
end PEqualNP.Outside.L_lib_1586_aux

namespace PEqualNP.Outside.L_lib_1586_aux
open scoped Classical
def Coherent (S : Fin n → Bits m) (col : Fin n → Fin m → Fin k) :=
  ∀j l,j≠l → ∀x y,x≠y → x∈S j → y∈S j → x∈S l → y∈S l →
    col j x=col j y ∧ col j x=col l x ∧ col j x=col l y
def Alone (S : Fin n → Bits m) (j : Fin n) (A : Bits m) := 1<A.card ∧ A⊆S j ∧ ∀l,l≠j → ¬A⊆S l
def Common (S : Fin n → Bits m) (col : Fin n → Fin m → Fin k) (d : Fin k) (A : Bits m) :=
  ∃j l,j≠l ∧ A⊆S j ∧ A⊆S l ∧ ∀i∈A,col j i=d
def BigCommon (S : Fin n → Bits m) (col : Fin n → Fin m → Fin k) (d : Fin k) (A : Bits m) := 1<A.card ∧ Common S col d A
theorem smallSeed {A : Bits m} (small : A.card≤1) : A∈seed m := by
  by_cases em : A=∅
  · simp [em,seed]
  · have p:=Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr em)
    obtain ⟨i,rfl⟩:=Finset.card_eq_one.mp (by omega : A.card=1);exact rawMem i
theorem seedSmall {A : Bits m} (h : A∈seed m) : A.card≤1 := by
  rcases Finset.mem_insert.mp h with rfl|h
  · simp
  · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp h;simp
theorem commonDown {col : Fin n → Fin m → Fin k} {S d A B} (sub : A⊆B) (c : Common S col d B) : Common S col d A := by
  obtain ⟨j,l,ne,p,q,same⟩:=c;exact ⟨j,l,ne,sub.trans p,sub.trans q,fun i h => same _ (sub h)⟩
theorem otherOwner {S : Fin n → Bits m} {col : Fin n → Fin m → Fin k} (coh : Coherent S col)
    {A : Bits m} (big : 1<A.card) {j l} (ne : j≠l) (a : A⊆S j) (b : A⊆S l) {x y} (hx : x∈A) (hy : y∈A) :
    col j x=col l y := by
  by_cases eq:x=y
  · subst y;obtain ⟨t,ht,nt⟩:=Finset.exists_mem_ne (s:=A) big x
    exact (coh j l ne x t nt.symm (a hx) (a ht) (b hx) (b ht)).2.1
  · exact (coh j l ne x y eq (a hx) (a hy) (b hx) (b hy)).2.2
theorem ownerColor {S : Fin n → Bits m} {col : Fin n → Fin m → Fin k} (coh : Coherent S col)
    {A : Bits m} {j} (sub : A⊆S j) {d} (bc : BigCommon S col d A) : ∀i∈A,col j i=d := by
  obtain ⟨big,p,q,pq,sp,sq,same⟩:=bc
  intro i hi;by_cases eq:j=p
  · exact eq ▸ same i hi
  · exact (otherOwner coh big eq sub sp hi hi).trans (same i hi)
theorem palette {S : Fin n → Bits m} {col : Fin n → Fin m → Fin k} (coh : Coherent S col)
    {A : Bits m} {j} (inside : A⊆S j) (nonempty : A.Nonempty) (outside : ¬Alone S j A) :
    ∃d,(∀i∈A,col j i=d) ∧ (A∈seed m ∨ BigCommon S col d A) := by
  obtain ⟨i,hi⟩:=nonempty
  by_cases small:A.card≤1
  · refine ⟨col j i,?_,Or.inl (smallSeed small)⟩
    intro t ht;rw [Finset.card_le_one.mp small t ht i hi]
  · have big : 1<A.card := by omega
    have ex : ∃l,l≠j ∧ A⊆S l := by by_contra! h;exact outside ⟨big,inside,h⟩
    obtain ⟨l,ne,sl⟩:=ex
    have same (t) (ht : t∈A) : col j t=col l i := otherOwner coh big ne.symm inside sl ht hi
    exact ⟨_,same,Or.inr ⟨big,j,l,ne.symm,inside,sl,same⟩⟩
theorem paidUniq {S : Fin n → Bits m} {col : Fin n → Fin m → Fin k} (coh : Coherent S col) (A : Bits m) :
    Set.Subsingleton {tag : Fin k ⊕ Fin n | Sum.elim (fun d => BigCommon S col d A) (fun j => Alone S j A) tag} := by
  intro u hu v hv
  cases u with
  | inl d => cases v with
    | inl e =>
      change BigCommon S col d A at hu;change BigCommon S col e A at hv
      obtain ⟨j,l,ne,sub,_,same⟩:=hu.2
      obtain ⟨i,hi⟩:=Finset.card_pos.mp (by have h:=hu.1;omega : 0<A.card)
      exact congrArg Sum.inl ((same i hi).symm.trans (ownerColor coh sub hv i hi))
    | inr j =>
      obtain ⟨_,p,q,ne,sp,sq,_⟩:=hu
      change Alone S j A at hv
      by_cases e:p=j
      · exact (hv.2.2 q (by simpa [e] using ne.symm) sq).elim
      · exact (hv.2.2 p e sp).elim
  | inr j => cases v with
    | inr l =>
      change Alone S j A at hu;change Alone S l A at hv
      by_contra ne;exact hu.2.2 l (fun e => ne (e ▸ rfl)) hv.2.1
    | inl d =>
      obtain ⟨_,p,q,ne,sp,sq,_⟩:=hv;change Alone S j A at hu
      by_cases e:p=j
      · exact (hu.2.2 q (by simpa [e] using ne.symm) sq).elim
      · exact (hu.2.2 p e sp).elim
end PEqualNP.Outside.L_lib_1586_aux

namespace PEqualNP.Outside.L_lib_1586_aux
open scoped Classical
noncomputable def charge (log : List (Bits m)) (p : Bits m → Prop) := (log.filter (fun A => decide (p A))).length
theorem sharedBuild {S : Fin n → Bits m} (col : Fin n → Fin m → Fin k) {B} (lg : Ledger (seed m) log B) (d : Fin k) :
    ∃r ≤ charge log (BigCommon S col d),∃Z,Chain (seed m) r Z ∧ ∀A∈B,Common S col d A → A∈Z := by
  exact restrictLedger lg _ _ _ (fun sub c => commonDown sub c) (fun _ h _ => h) (fun A _ c h => smallSeed (by by_contra! big;exact h ⟨big,c⟩))
theorem leavesOfRow {S : Fin n → Bits m} {B} (lg : Ledger (seed m) log B) (targets : Has B S) (j : Fin n) :
    ∃T : Bank m,T.biUnion id=S j ∧ T.card ≤ charge log (Alone S j)+1 ∧
      ∀A∈T,A.Nonempty ∧ A⊆S j ∧ ¬Alone S j A ∧ (A∈seed m ∨ A∈B) := by
  classical
  by_cases em:S j=∅
  · exact ⟨∅,by simp [em],by simp,by simp⟩
  let E:=seed m ∪ B.filter (fun A => A⊆S j ∧ ¬Alone S j A)
  have substep {A V : Bits m} (av : A⊆V) (vs : V⊆S j) : A⊆S j := av.trans vs
  obtain ⟨r,cap,Z,ch,available⟩:=restrictLedger lg E (fun A => A⊆S j) (Alone S j) substep (fun _ h _ => Finset.mem_union_left _ h)
    (fun A mem inside no => Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨mem,inside,no⟩))
  have sIn:=available _ (targets j (Finset.nonempty_iff_ne_empty.mpr em)) Finset.Subset.rfl
  obtain ⟨T,sub,cover,sz⟩:=extractLeaves ch {S j} (Finset.singleton_subset_iff.mpr sIn)
  simp only [Finset.singleton_biUnion,id_eq,Finset.card_singleton] at cover sz
  refine ⟨T.erase ∅,?_,?_,?_⟩
  · rw [←cover];ext i;simp only [Finset.mem_biUnion,id_eq,Finset.mem_erase];constructor
    · rintro ⟨a,⟨_,h⟩,i⟩;exact ⟨a,h,i⟩
    · rintro ⟨a,t,i⟩;exact ⟨a,⟨Finset.nonempty_iff_ne_empty.mp ⟨_,i⟩,t⟩,i⟩
  · have s:=Finset.card_le_card (Finset.erase_subset ∅ T);change r≤charge log _ at cap;omega
  · intro A h;obtain ⟨ne,t⟩:=Finset.mem_erase.mp h
    have inside : A⊆S j := by intro i hi;rw [←cover];exact Finset.mem_biUnion.mpr ⟨A,t,hi⟩
    rcases Finset.mem_union.mp (sub t) with basic|accepted
    · exact ⟨Finset.nonempty_iff_ne_empty.mpr ne,inside,fun h => (Nat.not_lt_of_ge (seedSmall basic)) h.1,Or.inl basic⟩
    · obtain ⟨mem,_,no⟩:=Finset.mem_filter.mp accepted
      exact ⟨Finset.nonempty_iff_ne_empty.mpr ne,inside,no,Or.inr mem⟩
theorem spend {α : Type} [Fintype α] (log : List (Bits m)) (pay : α → Bits m → Prop)
    (unique : ∀A,Set.Subsingleton {i | pay i A}) : (∑i,charge log (pay i)) ≤ log.length := by
  classical
  induction log with
  | nil => simp [charge]
  | cons A log ih =>
    have add i : charge (A::log) (pay i)=charge log (pay i)+(if pay i A then 1 else 0) := by by_cases h:pay i A <;> simp [charge,h]
    have c : ((Finset.univ : Finset α).filter (fun i => pay i A)).card ≤ 1 := by
      apply Finset.card_le_one.mpr;intro i hi j hj
      exact unique A (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
    simp only [add,Finset.sum_add_distrib,List.length_cons]
    have e : (∑i : α,if pay i A then 1 else 0)=((Finset.univ : Finset α).filter (fun i => pay i A)).card := by simp
    rw [e];omega
end PEqualNP.Outside.L_lib_1586_aux

namespace PEqualNP.Outside.L_lib_1586_aux
open scoped Classical
def piece (S : Fin n → Bits m) (col : Fin n → Fin m → Fin k) (d : Fin k) (j : Fin n) := (S j).filter (fun x => col j x=d)
def overhead (S : Fin n → Bits m) (col : Fin n → Fin m → Fin k) (j : Fin n) := ((S j).image (col j)).card-1
theorem rowBuckets {S : Fin n → Bits m} {col : Fin n → Fin m → Fin k} (coh : Coherent S col)
    {B} (lg : Ledger (seed m) log B) (has : Has B S) (j : Fin n) :
    ∃U : Fin k → Bank m,(∀d,(U d).biUnion id=piece S col d j) ∧
      (∀d,∀A∈U d,A∈seed m ∨ (A∈B ∧ Common S col d A)) ∧
      (∑d,((U d).card-1))+overhead S col j ≤ charge log (Alone S j) := by
  classical
  obtain ⟨T,un,cap,props⟩:=leavesOfRow lg has j
  have assign (a : ↥T) := palette coh (props a a.property).2.1 (props a a.property).1 (props a a.property).2.2.1
  choose tag mono valid using assign
  let V (d : Fin k) := Finset.univ.filter (fun a : ↥T => tag a=d)
  let U (d : Fin k) := (V d).image Subtype.val
  have uc d : (U d).card=(V d).card := Finset.card_image_of_injective _ Subtype.val_injective
  have existsTag (x : Fin m) (hx : x∈S j) : ∃a : ↥T,x∈a.val := by
    rw [←un] at hx;obtain ⟨a,h,mem⟩:=Finset.mem_biUnion.mp hx;exact ⟨⟨a,h⟩,mem⟩
  have live d : (V d).Nonempty ↔ d∈(S j).image (col j) := by
    constructor
    · rintro ⟨a,h⟩;obtain ⟨x,hx⟩:=(props _ a.property).1
      exact Finset.mem_image.mpr ⟨x,(props _ a.property).2.1 hx,(mono a x hx).trans (Finset.mem_filter.mp h).2⟩
    · intro h;obtain ⟨x,mem,rfl⟩:=Finset.mem_image.mp h
      obtain ⟨a,xa⟩:=existsTag x mem;exact ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(mono a x xa).symm⟩⟩
  refine ⟨U,?_,?_,?_⟩
  · intro d;ext x;constructor
    · intro h;obtain ⟨A,mem,hx⟩:=Finset.mem_biUnion.mp h
      obtain ⟨a,va,rfl⟩:=Finset.mem_image.mp mem
      exact Finset.mem_filter.mpr ⟨(props _ a.property).2.1 hx,(mono a _ hx).trans (Finset.mem_filter.mp va).2⟩
    · intro h;obtain ⟨mem,e⟩:=Finset.mem_filter.mp h
      obtain ⟨a,xa⟩:=existsTag x mem
      have va : a∈V d := by simp [V,←mono a _ xa,e]
      exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_image_of_mem _ va,xa⟩
  · intro d A mem;obtain ⟨a,va,rfl⟩:=Finset.mem_image.mp mem
    have eq: tag a=d := (Finset.mem_filter.mp va).2
    rcases valid a with raw|big
    · exact Or.inl raw
    · rcases (props _ a.property).2.2.2 with raw|inside
      · exact Or.inl raw
      · exact Or.inr ⟨inside,eq ▸ big.2⟩
  · let colors:=(S j).image (col j)
    have total : (∑d,(V d).card)=T.card := by
      simpa [V] using Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset ↥T) (Finset.univ : Finset (Fin k)) tag
    have subtract d : (V d).card-1+(if d∈colors then 1 else 0)=(V d).card := by
      by_cases h:d∈colors
      · have p:=Finset.card_pos.mpr ((live d).mpr h);simp [h];omega
      · have e:=Finset.not_nonempty_iff_eq_empty.mp (fun p => h ((live d).mp p));simp [e,h]
    have equation:=Finset.sum_congr (rfl : (Finset.univ : Finset (Fin k))=Finset.univ) (fun d _ => subtract d)
    rw [Finset.sum_add_distrib,total] at equation
    have ce : (∑d : Fin k,if d∈colors then 1 else 0)=colors.card := by simp
    rw [ce] at equation
    simp only [uc];change _+ (colors.card-1) ≤ _
    by_cases em:colors=∅
    · have te : T.card=0 := by
        by_contra! pos;obtain ⟨a,ha⟩:=Finset.card_pos.mp (Nat.pos_of_ne_zero pos)
        have v : (⟨a,ha⟩ : ↥T)∈V (tag ⟨a,ha⟩) := by simp [V]
        have z:tag ⟨a,ha⟩∈colors := (live _).mp ⟨_,v⟩
        simp [em] at z
      simp [em] at equation ⊢;omega
    · have positive:=Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr em);omega
end PEqualNP.Outside.L_lib_1586_aux

namespace PEqualNP.Outside.L_lib_1586_aux
open scoped Classical
theorem batch {α : Type} [Fintype α] (I : Bank m) (cost : α → Nat) (want : α → Bank m → Prop)
    (mono : ∀i,∀{B D : Bank m},B⊆D → want i B → want i D)
    (job : ∀i,∃r≤cost i,∃B,Chain I r B ∧ want i B) :
    ∃r≤∑i,cost i,∃B,Chain I r B ∧ ∀i,want i B := by
  classical
  have aux (T : Finset α) : ∃r≤T.sum cost,∃B,Chain I r B ∧ ∀i∈T,want i B := by
    induction T using Finset.induction_on with
    | empty => exact ⟨0,by simp,I,.start,by simp⟩
    | @insert i T new ih =>
      obtain ⟨r,cap,B,ch,all⟩:=ih;obtain ⟨u,sz,V,ci,wi⟩:=job i
      obtain ⟨D,extend,sub⟩:=replay ci (grow ch)
      refine ⟨r+u,by rw [Finset.sum_insert new,Nat.add_comm (cost i)];exact Nat.add_le_add cap sz,D,splice ch extend,?_⟩
      intro j hj;rcases Finset.mem_insert.mp hj with rfl|hj
      · exact mono _ sub wi
      · exact mono _ (grow extend) (all _ hj)
  simpa using aux Finset.univ
theorem joinRows {S : Fin n → Bits m} (I : Bank m) (U : Fin n → Bank m)
    (want : ∀j,(U j).biUnion id=S j) (haveAll : ∀j,U j⊆I) :
    ∃r ≤ ∑j,((U j).card-1),∃B,Chain I r B ∧ Has B S := by
  apply batch I _ (fun j B => (S j).Nonempty → S j∈B) (fun _ {_ _} sub wi ne => sub (wi ne))
  intro j
  by_cases ne:(U j).Nonempty
  · obtain ⟨B,ch,h⟩:=collect (U j) (haveAll j) ne;exact ⟨_,le_rfl,B,ch,fun _ => want j ▸ h⟩
  · have em:=Finset.not_nonempty_iff_eq_empty.mp ne
    have e : S j=∅ := by rw [←want,em];simp
    exact ⟨0,Nat.zero_le _,I,.start,by simp [e]⟩
theorem splitBudget {S : Fin n → Bits m} {col : Fin n → Fin m → Fin k} (coh : Coherent S col)
    (ok : Budget S s) : ∃b : Fin k → Nat,(∀d,Budget (piece S col d) (b d)) ∧
      (∑d,b d)+(∑j,overhead S col j) ≤ s := by
  obtain ⟨r,cap,B,ch,has⟩:=ok
  obtain ⟨log,lg,length⟩:=ledgerOfChain ch
  choose U cover valid localCost using fun j => rowBuckets coh lg has j
  let common d := charge log (BigCommon S col d)
  let rest d := ∑j,((U j d).card-1)
  refine ⟨fun d => common d+rest d,?_,?_⟩
  · intro d
    obtain ⟨u,uc,Z,shared,known⟩:=sharedBuild (S:=S) col lg d
    have sub j : U j d⊆Z := by
      intro A h;rcases valid j d A h with raw|⟨mem,cm⟩
      · exact grow shared raw
      · exact known A mem cm
    obtain ⟨v,vc,W,cw,hw⟩:=joinRows Z (fun j => U j d) (fun j => cover j d) sub
    exact ⟨u+v,Nat.add_le_add uc vc,W,splice shared cw,hw⟩
  · let pay (t : Fin k ⊕ Fin n) A := Sum.elim (fun d => BigCommon S col d A) (fun j => Alone S j A) t
    have total:=spend log pay (paidUniq coh)
    rw [Fintype.sum_sum_type,length] at total
    have priv:=Finset.sum_le_sum (s:=Finset.univ) (fun j _ => localCost j)
    rw [Finset.sum_add_distrib] at priv
    have switch : (∑d,rest d)=∑j,∑d,((U j d).card-1) := Finset.sum_comm
    rw [Finset.sum_add_distrib,switch]
    change (∑d,common d)+(∑j,charge log (Alone S j)) ≤ r at total
    omega
end PEqualNP.Outside.L_lib_1586_aux

namespace PEqualNP.Outside.L_lib_1586_aux
open scoped Classical
theorem stitchBudget {S : Fin n → Bits m} {col : Fin n → Fin m → Fin k} (b : Fin k → Nat)
    (ok : ∀d,Budget (piece S col d) (b d)) (sz : (∑d,b d)+(∑j,overhead S col j) ≤ s) : Budget S s := by
  classical
  obtain ⟨r,cap,B,ch,known⟩:=batch (seed m) b (fun d B => Has B (piece S col d)) (fun _ {_ _} sub w j ne => sub (w j ne)) ok
  let U (j : Fin n) := ((S j).image (col j)).image (fun d => piece S col d j)
  have q j : (U j).biUnion id=S j := by
    ext i;constructor
    · intro h;obtain ⟨A,a,mem⟩:=Finset.mem_biUnion.mp h
      obtain ⟨d,_,rfl⟩:=Finset.mem_image.mp a;exact (Finset.mem_filter.mp mem).1
    · intro mem
      have hc:=Finset.mem_image_of_mem (col j) mem
      exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_image_of_mem _ hc,Finset.mem_filter.mpr ⟨mem,rfl⟩⟩
  have included j : U j⊆B := by
    intro A ha;obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp ha
    obtain ⟨i,mem,eq⟩:=Finset.mem_image.mp hd
    exact known d j ⟨i,Finset.mem_filter.mpr ⟨mem,eq⟩⟩
  obtain ⟨v,cv,Z,more,all⟩:=joinRows B U q included
  have c j : (U j).card-1 ≤ overhead S col j := Nat.sub_le_sub_right Finset.card_image_le 1
  have total:=Finset.sum_le_sum (s:=Finset.univ) (fun j _ => c j)
  exact ⟨r+v,by omega,Z,splice ch more,all⟩
end PEqualNP.Outside.L_lib_1586_aux

namespace PEqualNP.Outside.L_lib_1586_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
def sample (i : Fin m) (A : Bits m) := decide (i∈A)
def readInput (i : Fin m) := List.ofFn (fun u : Fin m => decide (u=i))
def tick (w : List Bool) (g : Gate) := w++[g.op.eval (g.inputs.map fun j => w.getD j false)]
def legal (g : Gate) := g.op=.or ∧ g.inputs.length≤2
def Fits (S : Fin n → Bits m) (s : Nat) :=
  ∃ C : Circuit,C.size ≤ s ∧ ReadsBack m C ∧ (∀g∈C.gates,legal g) ∧
    ∀j,(S j).Nonempty → ∃w < m+C.size,∀i : Fin m,({C with output:=w} : Circuit).eval (readInput i)=sample i (S j)
def Acc (r : Nat) (values : Fin m → List Bool) :=
  ∃u≤r,∃B : Bank m,Chain (seed m) u B ∧ ∃names : List (Bits m),
    (∀A∈names,A∈B) ∧ ∅∈B ∧ ∀i,values i=names.map (sample i)
theorem rawAcc (m) : Acc 0 (readInput (m:=m)) := by
  let names := List.ofFn (fun i : Fin m => ({i} : Bits m))
  refine ⟨0,le_rfl,seed m,.start,names,?_,by simp [seed],?_⟩
  · intro A h;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp h;exact rawMem i
  · intro i;simp only [readInput,names,List.map_ofFn];congr 1;funext u
    simp [sample,Function.comp_def,eq_comm]
theorem getSample (names : List (Bits m)) (j : Nat) (i : Fin m) :
    (names.map (sample i)).getD j false=sample i (names.getD j ∅) := by
  simpa only [sample,Finset.notMem_empty,decide_false] using List.getD_map names (∅ : Bits m) (n:=j) (sample i)
theorem stepAcc {v : Fin m → List Bool} (ac : Acc r v) (g : Gate) (leg : legal g) : Acc (r+1) (fun i => tick (v i) g) := by
  obtain ⟨u,cap,B,ch,names,known,emp,eq⟩:=ac
  let read (j : Nat) := names.getD j ∅
  have present (j) : read j∈B := by
    unfold read;by_cases h:j<names.length
    · simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h] using known _ (List.getElem_mem h)
    · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : names.length≤j),emp]
  have val j i : (v i).getD j false=sample i (read j) := by rw [eq,getSample]
  have out (D : Bank m) (a : Bits m) (r' : Nat) (cc : Chain (seed m) r' D) (bound : r'≤r+1) (sub : B⊆D) (mem : a∈D)
      (e : ∀i,g.op.eval (g.inputs.map fun j => (v i).getD j false)=sample i a) : Acc (r+1) (fun i => tick (v i) g) := by
    refine ⟨r',bound,D,cc,names++[a],?_,sub emp,?_⟩
    · intro z h;rcases List.mem_append.mp h with h|h
      · exact sub (known _ h)
      · simpa only [List.mem_singleton] using (show z∈D from (List.mem_singleton.mp h) ▸ mem)
    · intro i;simp only [tick,List.map_append,List.map_cons,List.map_nil];rw [e i,eq i]
  rcases g with ⟨op,js⟩
  obtain ⟨opEq,arity⟩:=leg;change op=.or at opEq;subst op;change js.length≤2 at arity
  cases js with
  | nil => exact out _ ∅ u ch (by omega) Finset.Subset.rfl emp (by simp [GateOp.eval,sample])
  | cons a js => cases js with
    | nil => exact out _ _ u ch (by omega) Finset.Subset.rfl (present a) (by intro i;simpa [GateOp.eval] using val a i)
    | cons b xs => cases xs with
      | cons c tail => simp at arity
      | nil =>
        apply out _ _ (u+1) (.step ch (present a) (present b)) (by omega) (Finset.subset_insert ..) (Finset.mem_insert_self ..)
        intro i;simp only [List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false,val]
        simp [sample]
theorem readFits {S : Fin n → Bits m} (ok : Fits S s) : Budget S s := by
  obtain ⟨C,cap,_,leg,outs⟩:=ok
  have loop (gs : List Gate) {v : Fin m → List Bool} {r} (ac : Acc r v) (l : ∀g∈gs,legal g) :
      Acc (r+gs.length) (fun i => gs.foldl tick (v i)) := by
    induction gs generalizing v r with
    | nil => simpa using ac
    | cons g gs ih =>
      have next:=ih (stepAcc ac g (l _ (by simp))) (fun j h => l j (by simp [h]))
      simpa [Nat.add_assoc,Nat.add_comm 1] using next
  obtain ⟨u,b,B,ch,ns,h,empty,eq⟩:=loop C.gates (rawAcc m) leg
  refine ⟨u,by change C.gates.length ≤ s at cap;omega,B,ch,?_⟩
  intro j ne;obtain ⟨w,_,out⟩:=outs j ne
  have read (i : Fin m) : sample i (ns.getD w ∅)=sample i (S j) := by
    rw [←getSample,←eq];exact out i
  have same : ns.getD w ∅=S j := by ext i;simpa [sample] using congrArg (fun b : Bool => b=true) (read i) |>.to_iff
  rw [←same];by_cases len:w<ns.length
  · simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem len] using h _ (List.getElem_mem len)
  · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : ns.length≤w),empty]
end PEqualNP.Outside.L_lib_1586_aux

namespace PEqualNP.Outside.L_lib_1586_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
def testRun (gs : List Gate) (i : Fin m) := gs.foldl tick (readInput i)
def Seen (gs : List Gate) (A : Bits m) := ∃j < m+gs.length,∀i : Fin m,(testRun gs i).getD j false=sample i A
def Good (m : Nat) (gs : List Gate) := (∀g∈gs,legal g) ∧ ReadsBack m ⟨gs,0⟩
theorem runLen (gs : List Gate) (i : Fin m) : (testRun gs i).length=m+gs.length := by
  have aux (l : List Gate) (w : List Bool) : (l.foldl tick w).length=w.length+l.length := by
    induction l generalizing w with
    | nil => simp
    | cons g l ih => simp [ih,tick];omega
  simp [testRun,aux,readInput]
theorem extendRun (gs : List Gate) (g : Gate) (i : Fin m) : testRun (gs++[g]) i=tick (testRun gs i) g := by simp [testRun]
theorem extendSeen {A : Bits m} {gs} (a : Seen gs A) (g : Gate) : Seen (gs++[g]) A := by
  obtain ⟨j,hj,e⟩:=a
  refine ⟨j,by simp;omega,?_⟩
  intro i;rw [extendRun];unfold tick;rw [List.getD_append _ _ _ _ (by rw [runLen];exact hj),e]
theorem joinGate {A B : Bits m} {gs} (ok : Good m gs) (left : Seen gs A) (right : Seen gs B) :
    ∃g, Good m (gs++[g]) ∧ Seen (gs++[g]) (A∪B) := by
  obtain ⟨a,ha,ea⟩:=left;obtain ⟨b,hb,eb⟩:=right
  let g : Gate := ⟨.or,[a,b]⟩
  refine ⟨g,⟨?_,?_⟩,m+gs.length,by simp,?_⟩
  · intro z hz;rcases List.mem_append.mp hz with h|h
    · exact ok.1 z h
    · have e : z=g := by simpa using h
      simp [e,g,legal]
  · intro j hj i hi;change i∈((gs++[g]).getD j _).inputs at hi
    by_cases old:j<gs.length
    · rw [List.getD_append _ _ _ _ old] at hi;exact ok.2 j old i hi
    · have eq:j=gs.length := by simp at hj;omega
      subst j;have mem : i=a ∨ i=b := by simpa [g] using hi
      rcases mem with rfl|rfl <;> assumption
  · intro i;rw [extendRun];unfold tick
    rw [←runLen gs i,List.getD_append_right _ _ _ _ le_rfl,Nat.sub_self]
    change ((testRun gs i).getD a false || ((testRun gs i).getD b false || false))=sample i (A∪B)
    rw [ea,eb];simp [sample]
theorem emit {B : Bank m} (ch : Chain (seed m) r B) :
    ∃gs : List Gate,gs.length≤r ∧ Good m gs ∧ ∀A∈B,A.Nonempty → Seen gs A := by
  induction ch with
  | start =>
    refine ⟨[],by simp,by simp [Good,ReadsBack],?_⟩
    intro A mem ne;rcases Finset.mem_insert.mp mem with rfl|mem
    · simp at ne
    · obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp mem
      refine ⟨a.val,by simp,?_⟩
      intro i;simp [testRun,readInput,sample,eq_comm]
  | @step r bank a b cc ha hb ih =>
    obtain ⟨gs,cap,ok,seen⟩:=ih
    by_cases easy : a=∅ ∨ b=∅
    · refine ⟨gs,by omega,ok,?_⟩
      intro A mem ne;rcases Finset.mem_insert.mp mem with rfl|mem
      · rcases easy with e|e
        · simpa [e] using seen _ hb (by simpa [e] using ne)
        · simpa [e] using seen _ ha (by simpa [e] using ne)
      · exact seen A mem ne
    · obtain ⟨g,next,out⟩:=joinGate ok (seen _ ha (Finset.nonempty_iff_ne_empty.mpr (fun e => easy (Or.inl e)))) (seen _ hb (Finset.nonempty_iff_ne_empty.mpr (fun e => easy (Or.inr e))))
      refine ⟨gs++[g],by simp;omega,next,?_⟩
      intro A mem ne;rcases Finset.mem_insert.mp mem with rfl|mem
      · exact out
      · exact extendSeen (seen A mem ne) g
theorem writeFits {S : Fin n → Bits m} (ok : Budget S s) : Fits S s := by
  obtain ⟨r,cap,B,ch,has⟩:=ok;obtain ⟨gs,b,good,seen⟩:=emit ch
  refine ⟨⟨gs,0⟩,b.trans cap,good.2,good.1,?_⟩
  intro j ne;exact seen _ (has j ne) ne
end PEqualNP.Outside.L_lib_1586_aux

open PEqualNP.Outside.L_lib_1586_aux in
theorem PEqualNP.Outside.L_lib_1586 : (
  let fits := fun {m n : Nat} (S : Fin n → Finset (Fin m)) (s : Nat) =>
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ s ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack m C ∧
      (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2) ∧
      ∀ j : Fin n, (S j).Nonempty → ∃ w < m + C.size, ∀ i : Fin m,
        ({C with output := w} : PEqualNP.CircuitLowerBounds.Circuit).eval
          (List.ofFn (fun u : Fin m => decide (u = i))) = decide (i ∈ S j)
  ∀ (m n k : Nat) (S : Fin n → Finset (Fin m)) (color : Fin n → Fin m → Fin k),
    (∀ j l : Fin n, j ≠ l → ∀ x y : Fin m, x ≠ y →
      x ∈ S j → y ∈ S j → x ∈ S l → y ∈ S l →
      color j x = color j y ∧ color j x = color l x ∧ color j x = color l y) →
    ∀ s : Nat, fits S s ↔
      ∃ b : Fin k → Nat,
        (∀ d : Fin k, fits (fun j => (S j).filter (fun i => color j i = d)) (b d)) ∧
        (∑ d, b d) + (∑ j, (((S j).image (color j)).card - 1)) ≤ s
) := by
  intro fits m n k S color coherent s
  have conv {m n : Nat} (T : Fin n → Bits m) (b : Nat) : fits T b ↔ Budget T b := by
    change Fits T b ↔ Budget T b
    exact ⟨readFits,writeFits⟩
  constructor
  · intro f;obtain ⟨b,each,cost⟩:=splitBudget (col:=color) coherent ((conv _ _).mp f)
    exact ⟨b,fun d => (conv _ _).mpr (each d),cost⟩
  · rintro ⟨b,each,cost⟩
    exact (conv _ _).mpr (stitchBudget (S:=S) (col:=color) b (fun d => (conv _ _).mp (each d)) cost)
