import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1680_aux
open scoped Classical
abbrev SetN (p : Nat) := Finset (Fin p)
abbrev Edges (p t : Nat) := Finset (Fin p × Fin t)
def hit (G : Edges n n) (C : SetN n) := ∀e∈G,e.1∈C ∨ e.2∈C
def joined (G : Edges n n) (s : Fin p → Fin n) (w : Fin n → Nat) (A : Edges p t) (F : Edges t t) (b : Nat) :=
  ∃C I,hit G C ∧ hit F I ∧ (∀e∈A,s e.1∈C ∨ e.2∈I) ∧ C.sum w+I.card ≤ b
def ideal (q : Nat) (G : Edges n n) (s : Fin p → Fin n) (w : Fin n → Nat) (b : Nat) :=
  (∃C,hit G C ∧ (∀i,s i∈C) ∧ C.sum w ≤ b) ∨ ∃C,hit G C ∧ C.sum w+q ≤ b
def eligible (q : Nat) (G : Edges n n) (s : Fin p → Fin n) (w : Fin n → Nat) :=
  (∀e∈G,e.1<e.2) ∧ Function.Injective s ∧ ∀i,w (s i)=q
def fits (q : Nat) (A : Edges p t) (F : Edges t t) (i : Fin p) (b : Nat) :=
  ∃C L : SetN p,∃I : SetN t,hit F I ∧ (∀j,j≠i → j∈C ∨ j∈L) ∧ (∀e∈A,e.1∈C ∨ e.2∈I) ∧
    C.card*q+L.card*q+I.card ≤ (p-1)*q+b
def safe (q : Nat) (A : Edges p t) (F : Edges t t) (r : Nat) :=
  ∀n (G : Edges n n) (s : Fin p → Fin n) (w : Fin n → Nat),eligible q G s w → ∀b,joined G s w A F b → ideal q G s w (b+r)
def left (i : Fin p) : Fin (p+p) := i.castAdd p
def right (i : Fin p) : Fin (p+p) := i.natAdd p
theorem leftInj (p) : Function.Injective (@left p) := fun _ _ e => Fin.ext (congrArg (fun x : Fin (p+p) => x.val) e)
theorem rightInj (p) : Function.Injective (@right p) := by intro a b e;have h:=congrArg Fin.val e;change p+a.val=p+b.val at h;exact Fin.ext (by omega)
theorem before (i j : Fin p) : left i < right j := by change i.val<p+j.val;omega
def others (i : Fin p) := Finset.univ.erase i
theorem othersCard (i : Fin p) : (others i).card=p-1 := by simp [others]
def testGraph (i : Fin p) : Edges (p+p) (p+p) := (others i).image (fun j => (left j,right j))
def tester (C L : SetN p) := C.image left ∪ L.image right
theorem inLeft (C L : SetN p) (a : Fin p) : left a∈tester C L ↔ a∈C := by simp [tester,(leftInj p).eq_iff,fun i => (before a i).ne.symm]
theorem inRight (C L : SetN p) (a : Fin p) : right a∈tester C L ↔ a∈L := by simp [tester,(rightInj p).eq_iff,fun i => (before i a).ne]
theorem testerSize (C L : SetN p) : (tester C L).card=C.card+L.card := by
  have dis : Disjoint (C.image left) (L.image right) := by
    apply Finset.disjoint_left.mpr;intro x h g;obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp h;obtain ⟨j,_,eq⟩:=Finset.mem_image.mp g;exact (before i j).ne eq.symm
  rw [tester,Finset.card_union_of_disjoint dis,Finset.card_image_of_injective _ (leftInj _),Finset.card_image_of_injective _ (rightInj _)]
theorem testHit (i : Fin p) {T : SetN (p+p)} (h : hit (testGraph i) T) : p-1 ≤ T.card := by
  classical
  let pick j:=if left j∈T then left j else right j
  have inject : Function.Injective pick := by
    intro a b e;dsimp only [pick] at e;split at e <;> split at e
    · exact leftInj _ e
    · exact ((before a b).ne e).elim
    · exact ((before b a).ne e.symm).elim
    · exact rightInj _ e
  have sub : (others i).image pick⊆T := by
    intro x hx;obtain ⟨j,jh,rfl⟩:=Finset.mem_image.mp hx
    have yes:=h (left j,right j) (Finset.mem_image_of_mem _ jh);dsimp only [pick];split <;> tauto
  have d:=Finset.card_le_card sub;simpa [Finset.card_image_of_injective _ inject,othersCard] using d
theorem safePrice {A : Edges p t} {F : Edges t t} (v : Fin p → Nat) (price : ∀i b,fits q A F i b ↔ v i ≤ b) :
    safe q A F r ↔ ∀i,q ≤ v i+r := by
  classical
  constructor
  · intro good i;obtain ⟨C,L,I,hitF,cover,bridge,bill⟩:=(price i _).mpr le_rfl
    let w:=fun _ : Fin (p+p) => q
    have eligible' : eligible q (testGraph i) left w := by
      refine ⟨?_,leftInj _,fun _ => rfl⟩;intro e he;obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp he;exact before _ _
    have can : joined (testGraph i) left w A F ((p-1)*q+v i) := by
      refine ⟨tester C L,I,?_,hitF,?_,?_⟩
      · intro e he;obtain ⟨j,jh,rfl⟩:=Finset.mem_image.mp he
        exact (cover j (Finset.mem_erase.mp jh).1).imp ((inLeft ..).mpr) ((inRight ..).mpr)
      · exact fun e he => (bridge e he).imp ((inLeft ..).mpr) id
      · simpa [w,testerSize,Nat.add_mul] using bill
    rcases good _ _ _ _ eligible' _ can with ⟨T,_,all,cap⟩|⟨T,ht,cap⟩
    · have sub : Finset.univ.image (@left p)⊆T := by intro x hx;obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hx;exact all j
      have sz:=Finset.card_le_card sub;rw [Finset.card_image_of_injective _ (leftInj p),Finset.card_univ,Fintype.card_fin] at sz
      have mul:=Nat.mul_le_mul_right q sz;simp [w] at cap
      have one : p=p-1+1 := by have h:=i.isLt;omega
      conv at mul => lhs;rw [one,Nat.add_mul,one_mul]
      omega
    · have mul:=Nat.mul_le_mul_right q (testHit i ht);simp [w] at cap;omega
  · intro bound n G s w _ b joined';obtain ⟨C,I,hitG,hitF,bridge,cap⟩:=joined'
    by_cases all:∀i,s i∈C
    · exact Or.inl ⟨C,hitG,all,by omega⟩
    · obtain ⟨i,miss⟩:=not_forall.mp all
      have probe : fits q A F i I.card := by
        refine ⟨others i,∅,I,hitF,fun j diff => Or.inl (Finset.mem_erase.mpr ⟨diff,Finset.mem_univ _⟩),?_,?_⟩
        · intro e he;by_cases eq:e.1=i
          · exact Or.inr ((bridge e he).resolve_left (eq.symm ▸ miss))
          · exact Or.inl (Finset.mem_erase.mpr ⟨eq,Finset.mem_univ _⟩)
        · simp [othersCard]
      have low:=(price i _).mp probe;have h:=bound i;exact Or.inr ⟨C,hitG,by omega⟩
end PEqualNP.Outside.L_lib_1680_aux

namespace PEqualNP.Outside.L_lib_1680_aux
open scoped Classical
theorem realize (v : Fin p → Nat) (cap : ∀i,v i ≤ q) : ∃(n : Nat) (A : Edges p n) (F : Edges n n),
    (∀e∈F,e.1<e.2) ∧ ∀i b,fits q A F i b ↔ v i ≤ b := by
  classical
  let pin (i : Fin p) (j : Fin (v i)) : Fin (p*q) := finProdFinEquiv (i,j.castLE (cap i))
  let stars (i : Fin p) := Finset.univ.image (pin i)
  let A : Edges p (p*q):=Finset.univ.filter (fun z => z.2∈stars z.1)
  have size (i : Fin p) : (stars i).card=v i := by
    have inj : Function.Injective (pin i) := by
      intro x y eq;have e:=finProdFinEquiv.injective eq
      exact Fin.ext (congrArg (fun z : Fin p × Fin q => z.2.val) e)
    simp [stars,Finset.card_image_of_injective _ inj]
  refine ⟨p*q,A,∅,by simp,?_⟩;intro i b;constructor
  · rintro ⟨C,L,I,_,cover,bridge,paid⟩
    have rest : others i⊆C∪L := by intro j hj;exact Finset.mem_union.mpr (cover j (Finset.mem_erase.mp hj).1)
    have co:=(Finset.card_le_card rest).trans (Finset.card_union_le ..);rw [othersCard] at co
    by_cases ic:i∈C
    · have full : C∪L=Finset.univ := by
        apply Finset.eq_univ_of_forall;intro j;by_cases eq:j=i
        · exact eq.symm ▸ Finset.mem_union_left _ ic
        · exact rest (Finset.mem_erase.mpr ⟨eq,Finset.mem_univ _⟩)
      have d:=Finset.card_union_le C L;rw [full,Finset.card_univ,Fintype.card_fin] at d
      have mul:=Nat.mul_le_mul_right q d
      have h : p=p-1+1 := by have lt:=i.isLt;omega
      conv at mul => lhs;rw [h,Nat.add_mul,one_mul]
      rw [Nat.add_mul] at mul;have hi:=cap i;omega
    · have sub : stars i⊆I := by intro j hj;exact (bridge (i,j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)).resolve_left ic
      have n:=Finset.card_le_card sub;rw [size] at n
      have h:=Nat.mul_le_mul_right q co;rw [Nat.add_mul] at h;omega
  · intro vsmall;refine ⟨others i,∅,stars i,by simp [hit],?_,?_,?_⟩
    · intro j ne;exact Or.inl (Finset.mem_erase.mpr ⟨ne,Finset.mem_univ _⟩)
    · intro e he;by_cases eq:e.1=i
      · exact Or.inr (eq ▸ (Finset.mem_filter.mp he).2)
      · exact Or.inl (Finset.mem_erase.mpr ⟨eq,Finset.mem_univ _⟩)
    · simp [othersCard,size,vsmall]
end PEqualNP.Outside.L_lib_1680_aux

namespace PEqualNP.Outside.L_lib_1680_aux
open scoped Classical
def tally (S : Fin t → Fin p) (i : Fin p) := (Finset.univ.filter (fun j => S j=i)).card
def prefixCount (S : Fin t → Fin p) (order : Equiv.Perm (Fin p)) (j : Fin p) :=
  (Finset.univ.filter (fun a : Fin p => a ≤ j)).sum (fun a => tally S (order a))
def width (e : Nat) (S : Fin t → Fin p) (order : Equiv.Perm (Fin p)) :=
  ∑j : Fin p,(e+1-prefixCount S order j)
def errors (x : Fin t → Nat) (S : Fin t → Fin p) (v : Fin p → Nat) := (Finset.univ.filter (fun j => x j<v (S j))).card
def maxReport (S : Fin t → Fin p) (x : Fin t → Nat) (i) := (Finset.univ.filter (fun j => S j=i)).sup x
theorem readLe (S : Fin t → Fin p) (x : Fin t → Nat) (j) : x j ≤ maxReport S x (S j) :=
  Finset.le_sup (s:=Finset.univ.filter (fun k => S k=S j)) (f:=x) (by simp)
theorem maxLe (S : Fin t → Fin p) (x : Fin t → Nat) (v : Fin p → Nat) (le : ∀j,x j ≤ v (S j)) (i) : maxReport S x i ≤ v i := by
  apply Finset.sup_le;intro j h;simpa [(Finset.mem_filter.mp h).2] using le j
theorem total (S : Fin t → Fin p) : ∑i,tally S i=t := by
  simpa [tally] using Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin t)) (Finset.univ : Finset (Fin p)) S
theorem allocate {p b : Nat} (hp : 0<p) (load : Fin p → Nat) (limit : ∑i,load i ≤ b) :
    ∃ask : Fin b → Fin p,∀i,load i ≤ tally ask i := by
  classical
  let T:=Σi : Fin p,Fin (load i)
  have small : Fintype.card T ≤ Fintype.card (Fin b) := by simpa [T,Fintype.card_sigma] using limit
  let f (a : T) : Fin b:=(Fintype.equivFin T a).castLE (by simpa using small)
  have fi : Function.Injective f := by intro a z eq;apply (Fintype.equivFin T).injective;exact Fin.ext (congrArg (fun j : Fin b => j.val) eq)
  let ask (j : Fin b) := if h:∃a:T,f a=j then (Classical.choose h).1 else (⟨0,hp⟩ : Fin p)
  have atCode (a : T) : ask (f a)=a.1 := by
    have h : ∃x:T,f x=f a := ⟨a,rfl⟩
    simp only [ask,dif_pos h];exact congrArg Sigma.fst (fi (Classical.choose_spec h))
  refine ⟨ask,?_⟩;intro i
  let index (j : Fin (load i)) := f ⟨i,j⟩
  have inj : Function.Injective index := by intro a b eq;have h:=fi eq;exact eq_of_heq (Sigma.mk.inj h).2
  have sub : Finset.univ.image index ⊆ Finset.univ.filter (fun j => ask j=i) := by
    intro z hz;obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hz;exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,atCode ⟨i,a⟩⟩
  simpa [Finset.card_image_of_injective _ inj,tally] using Finset.card_le_card sub
theorem prefixSize (S : Fin t → Fin p) (o : Equiv.Perm (Fin p)) (j : Fin p) :
    prefixCount S o j=(Finset.univ.filter (fun a => o.symm (S a) ≤ j)).card := by
  let U:=Finset.univ.filter (fun i : Fin p => i ≤ j)
  have eq (i : Fin p) : tally S (o i)=(Finset.univ.filter (fun a => o.symm (S a)=i)).card := by
    apply congrArg Finset.card;ext; simp [o.symm_apply_eq]
  unfold prefixCount;simp_rw [eq];rw [Finset.sum_card_fiberwise_eq_card_filter];simp
end PEqualNP.Outside.L_lib_1680_aux

namespace PEqualNP.Outside.L_lib_1680_aux
open scoped Classical
def Game (restrict : Prop) (q e : Nat) (S : Fin t → Fin p) (b : Nat) :=
  ∃(ask : (Fin t → Nat) → Fin b → Fin p) (dec : (Fin t → Nat) → (Fin b → Nat) → Nat),
    ∀v : Fin p → Nat,(restrict → ∀i,v i ≤ q) → ∀x y,
    (∀j,x j ≤ v (S j)) → (∀j,y j ≤ v (ask x j)) →
    errors x S v+errors y (ask x) v ≤ e → ∀r,dec x y ≤ r ↔ ∀i,q ≤ v i+r
theorem decode (q e : Nat) (S : Fin t → Fin p) (hp : 0<p) (limit : ∀o,width e S o ≤ b) : Game False q e S b := by
  classical
  let order (x : Fin t → Nat) := Tuple.sort (maxReport S x)
  let load x (j : Fin p) := e+1-prefixCount S (order x) j
  choose rank enough using fun x => allocate hp (load x) (limit (order x))
  let ask x a:=order x (rank x a)
  let seen x y i:=max (maxReport S x i) (maxReport (ask x) y i)
  let dec x y := Finset.univ.sup (fun i : Fin p => q-seen x y i)
  refine ⟨ask,dec,?_⟩
  intro v _ x y low lo2 budget r
  have decodeEq : dec x y ≤ r ↔ ∀i,q ≤ seen x y i+r := by simp [dec,Finset.sup_le_iff,Nat.sub_le_iff_le_add,Nat.add_comm]
  rw [decodeEq];constructor
  · intro all i;have a:=maxLe S x v low i;have b:=maxLe (ask x) y v lo2 i;have h:=all i;dsimp only [seen] at h;omega
  · intro bound i;by_contra! bad
    let j:=(order x).symm i
    have mapped : order x j=i := (order x).apply_symm_apply _
    have tooLow (z) : seen x y i < v z := by have g:=bound z;omega
    have first : prefixCount S (order x) j ≤ errors x S v := by
      rw [prefixSize];apply Finset.card_le_card;intro a ha
      have earlier:=(Finset.mem_filter.mp ha).2
      have mono:=(Tuple.monotone_sort (maxReport S x)) earlier
      change maxReport S x ((order x) ((order x).symm (S a))) ≤ maxReport S x ((order x) j) at mono
      rw [Equiv.apply_symm_apply,mapped] at mono
      have le:=readLe S x a;have less:=tooLow (S a)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by dsimp [seen] at less;omega⟩
    have second : tally (rank x) j ≤ errors y (ask x) v := by
      apply Finset.card_le_card;intro a ha;have eq:=(Finset.mem_filter.mp ha).2
      have output : ask x a=i := (congrArg (order x) eq).trans mapped
      have le:=readLe (ask x) y a;have less:=tooLow i;rw [output] at le
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [output];dsimp [seen] at less;omega⟩
    have gap:=enough x j;dsimp [load] at gap;omega
end PEqualNP.Outside.L_lib_1680_aux

namespace PEqualNP.Outside.L_lib_1680_aux
open scoped Classical
theorem adversary (q e : Nat) (S : Fin t → Fin p) (pq : p ≤ q) (game : Game True q e S b) (o : Equiv.Perm (Fin p)) : width e S o ≤ b := by
  classical
  obtain ⟨ask,dec,ok⟩:=game
  let rank (i : Fin p):=o.symm i
  let x (u : Fin t):=(rank (S u)).val
  let Q:=ask x
  have bill (j : Fin p) : e+1-prefixCount S o j ≤ tally Q (o j) := by
    by_contra! short
    let v (i : Fin p):=if rank i<j then q else (rank i).val
    let w (i : Fin p):=if rank i ≤ j then q else (rank i).val
    let y (a : Fin b):=v (Q a)
    have hi (i) : v i ≤ q := by have lt:=(rank i).isLt;dsimp [v];split <;> omega
    have hw (i) : w i ≤ q := by have lt:=(rank i).isLt;dsimp [w];split <;> omega
    have vw (i) : v i ≤ w i := by
      by_cases l:rank i<j
      · simp [v,w,l,l.le]
      · by_cases r:rank i ≤ j
        · have lt:=(rank i).isLt;simp [v,w,l,r];omega
        · simp [v,w,l,r]
    have xl (a) : x a ≤ v (S a) := by have lt:=(rank (S a)).isLt;dsimp [x,v];split <;> omega
    have first : errors x S w ≤ prefixCount S o j := by
      rw [prefixSize];apply Finset.card_le_card;intro a ha
      have err:=(Finset.mem_filter.mp ha).2
      apply Finset.mem_filter.mpr;refine ⟨Finset.mem_univ _,?_⟩
      by_contra no;have h : ¬rank (S a) ≤ j := no;simp [w,h,x] at err
    have second : errors y Q w ≤ tally Q (o j) := by
      apply Finset.card_le_card;intro a ha;have err:=(Finset.mem_filter.mp ha).2
      have eq : rank (Q a)=j := by
        rcases lt_trichotomy (rank (Q a)) j with lt|eq|gt
        · simp [y,v,w,lt,lt.le] at err
        · exact eq
        · simp [y,v,w,not_lt_of_gt gt,not_le_of_gt gt] at err
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,o.symm_apply_eq.mp eq⟩
    have lowFirst : errors x S v ≤ errors x S w := by
      apply Finset.card_le_card;intro a ha;exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_lt_of_le (Finset.mem_filter.mp ha).2 (vw _)⟩
    have lowSecond : errors y Q v=0 := by simp [errors,y]
    have budget : errors x S w+errors y Q w ≤ e := by omega
    let r:=q-(j.val+1)
    have lv:=ok v (fun _ => hi) x y xl (fun _ => le_rfl) (by change errors x S v+errors y Q v ≤ e;omega) r
    have hv:=ok w (fun _ => hw) x y (fun a => (xl a).trans (vw _)) (fun a => vw (Q a)) budget r
    have pass : dec x y ≤ r := hv.mpr (by
      intro i;have lim:=j.isLt;by_cases small:rank i ≤ j
      · simp [w,small]
      · have gt : j.val<(rank i).val := not_le.mp small;dsimp [w,r];rw [if_neg small];omega)
    have bad:=(lv.mp pass) (o j);have lim:=j.isLt
    simp [v,rank,r] at bad;omega
  unfold width
  have cost:=Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin p))) (fun j _ => bill j)
  have eq : (∑j,tally Q (o j))=b := (Equiv.sum_comp o (tally Q)).trans (total Q)
  omega
end PEqualNP.Outside.L_lib_1680_aux

namespace PEqualNP.Outside.L_lib_1680_aux
open scoped Classical
def initial (j : Fin p) := Finset.univ.filter (fun i : Fin p => i ≤ j)
theorem initialSize (j : Fin p) : (initial j).card=j.val+1 := by
  have eq : initial j=Finset.Iic j := by ext;simp [initial]
  rw [eq,Fin.card_Iic]
def fairSum (p t j : Nat) := (j+1)*(t/p)+((j+1)-(p-t%p))
def fairWidth (p t e : Nat) := ∑j : Fin p,(e+1-fairSum p t j.val)
theorem sortedBound (S : Fin t → Fin p) (hp : 0<p) (j : Fin p) :
    prefixCount S (Tuple.sort (tally S)) j ≤ fairSum p t j.val := by
  classical
  let o:=Tuple.sort (tally S)
  let f a:=tally S (o a)
  let T:=initial j
  have mo : Monotone f := Tuple.monotone_sort (tally S)
  have sz : T.card=j.val+1 := initialSize _
  let d:=t/p;let r:=t%p;let l:=j.val+1
  have jr : l ≤ p := j.isLt
  have rem : r<p := Nat.mod_lt _ hp
  have div : r+p*d=t := Nat.mod_add_div t p
  have full : ∑i,f i=t := (Equiv.sum_comp o (tally S)).trans (total S)
  have split : (∑i∈T,f i)+(∑i∈Tᶜ,f i)=t := (Finset.sum_add_sum_compl T f).trans full
  change (∑i∈T,f i) ≤ l*d+(l-(p-r))
  by_cases cheap:f j ≤ d
  · have bound:=Finset.sum_le_sum (s:=T) (g:=fun _ => d) (fun i hi => (mo (Finset.mem_filter.mp hi).2).trans cheap)
    simpa [sz,l] using (show (∑i∈T,f i) ≤ T.card*d+(l-(p-r)) from bound.trans (by simp))
  · have high (i) (hi : i∈Tᶜ) : d+1 ≤ f i := by
      have earlier : ¬i ≤ j := by simpa [T,initial] using hi
      exact (Nat.lt_of_not_ge cheap).trans_le (mo (le_of_not_ge earlier))
    have sum:=Finset.sum_le_sum (s:=Tᶜ) (f:=fun _ => d+1) high
    have cs : Tᶜ.card=p-l := by rw [Finset.card_compl,Fintype.card_fin,sz]
    simp only [Finset.sum_const,nsmul_eq_mul,cs,Nat.mul_add,mul_one] at sum
    have sumClean : (p-l)*d+(p-l) ≤ ∑i∈Tᶜ,f i := by simpa using sum
    clear sum
    have parts : (p-l)*d+l*d=p*d := by rw [←Nat.add_mul,Nat.sub_add_cancel jr]
    omega
theorem balanced (hp : 0<p) (t : Nat) : ∃S : Fin t → Fin p,∀o j,fairSum p t j.val ≤ prefixCount S o j := by
  classical
  let d:=t/p;let r:=t%p;let cut:=p-r
  let lo:=Finset.univ.filter (fun i : Fin p => i.val<cut)
  have maxcut : cut ≤ p := Nat.sub_le .. 
  have ls : lo.card=cut := by
    let f (i : Fin cut) : Fin p:=i.castLE maxcut
    have inj : Function.Injective f := fun _ _ eq => Fin.ext (congrArg (fun z : Fin p => z.val) eq)
    have eq : Finset.univ.image f=lo := by
      ext i;constructor
      · intro h;obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp h;exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,x.isLt⟩
      · intro h;exact Finset.mem_image.mpr ⟨⟨i.val,(Finset.mem_filter.mp h).2⟩,Finset.mem_univ _,Fin.ext rfl⟩
    rw [←eq,Finset.card_image_of_injective _ inj,Finset.card_univ,Fintype.card_fin]
  let load (i : Fin p):=d+(if i∉lo then 1 else 0)
  have sum (V : Finset (Fin p)) : (∑i∈V,load i)=V.card*d+(V \ lo).card := by
    dsimp only [load];rw [Finset.sum_add_distrib,Finset.sum_boole];simp only [Finset.sum_const,nsmul_eq_mul,Finset.filter_notMem_eq_sdiff];rfl
  have rem : r<p := Nat.mod_lt _ hp
  have div : r+p*d=t := Nat.mod_add_div t p
  have totalLoad : (∑i,load i)=t := by
    rw [sum,Finset.card_univ,Fintype.card_fin,←Finset.compl_eq_univ_sdiff,Finset.card_compl,ls,Fintype.card_fin]
    dsimp [cut];omega
  obtain ⟨S,enough⟩:=allocate hp load totalLoad.le
  refine ⟨S,?_⟩;intro o j
  let T:=initial j;let V:=T.image o
  have sz : V.card=j.val+1 := by dsimp [V,T];rw [Finset.card_image_of_injective _ o.injective,initialSize]
  have bound : (∑i∈V,load i) ≤ prefixCount S o j := by
    dsimp [V];rw [Finset.sum_image (fun _ _ _ _ h => o.injective h)]
    exact Finset.sum_le_sum (fun i _ => enough (o i))
  have cap : V.card-lo.card ≤ (V \ lo).card := Finset.le_card_sdiff ..
  rw [sum,sz] at bound;rw [sz,ls] at cap;change (j.val+1)*d+((j.val+1)-cut) ≤ _;omega
end PEqualNP.Outside.L_lib_1680_aux

namespace PEqualNP.Outside.L_lib_1680_aux
noncomputable def fixedFilter {α : Type*} (P : α → Prop) (A : Finset α) := @Finset.filter α P (fun _ => Classical.propDecidable _) A
theorem filterUnique {α : Type*} (P : α → Prop) (d : DecidablePred P) (A : Finset α) :
    @Finset.filter α P d A=fixedFilter P A := by ext;simp only [fixedFilter,Finset.mem_filter]
end PEqualNP.Outside.L_lib_1680_aux
open PEqualNP.Outside.L_lib_1680_aux in
theorem PEqualNP.Outside.L_lib_1680 : (
  letI : ∀ a : Prop, Decidable a := Classical.propDecidable
  let hit := fun {n : Nat} (G : Finset (Fin n × Fin n)) (C : Finset (Fin n)) =>
    ∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C
  ∀ (p q : Nat), 0 < q →
  let joined := fun {n t : Nat} (G : Finset (Fin n × Fin n)) (s : Fin p → Fin n)
      (w : Fin n → Nat) (A : Finset (Fin p × Fin t)) (F : Finset (Fin t × Fin t)) (b : Nat) =>
    ∃ C I, hit G C ∧ hit F I ∧ (∀ e ∈ A, s e.1 ∈ C ∨ e.2 ∈ I) ∧ C.sum w+I.card ≤ b
  let ideal := fun {n : Nat} (G : Finset (Fin n × Fin n)) (s : Fin p → Fin n)
      (w : Fin n → Nat) (b : Nat) =>
    (∃ C, hit G C ∧ (∀ i, s i ∈ C) ∧ C.sum w ≤ b) ∨
    (∃ C, hit G C ∧ C.sum w+q ≤ b)
  let eligible := fun {n : Nat} (G : Finset (Fin n × Fin n)) (s : Fin p → Fin n)
      (w : Fin n → Nat) (a : Fin p → Nat) =>
    (∀ e ∈ G, e.1 < e.2) ∧ Function.Injective s ∧ ∀ i, w (s i)=a i
  let maskRead := fun {t : Nat} (a : Fin p → Nat) (X : Finset (Fin p))
      (A : Finset (Fin p × Fin t)) (F : Finset (Fin t × Fin t)) (b : Nat) =>
    ∃ C L : Finset (Fin p), ∃ I : Finset (Fin t), hit F I ∧
      (∀ i, i ∉ X → i ∈ C ∨ i ∈ L) ∧ (∀ e ∈ A, e.1 ∈ C ∨ e.2 ∈ I) ∧
      C.sum a + L.sum a + I.card ≤ b
  0 < p → p ≤ q →
  let a := fun (_ : Fin p) => q
  let fits := fun {t : Nat} (A : Finset (Fin p × Fin t)) (F : Finset (Fin t × Fin t))
      (X : Finset (Fin p)) (b : Nat) =>
    maskRead a X A F ((Finset.univ \ X).sum a+b)
  let safeAt := fun {t : Nat} (A : Finset (Fin p × Fin t)) (F : Finset (Fin t × Fin t)) (r : Nat) =>
    ∀ (n : Nat) (G : Finset (Fin n × Fin n)) (s : Fin p → Fin n) (w : Fin n → Nat),
      eligible G s w a → ∀ b, joined G s w A F b → ideal G s w (b+r)
  ∀ (e t b : Nat),
  let recovers := fun (S : Fin t → Fin p) =>
    ∃ (ask : (Fin t → Nat) → Fin b → Fin p)
      (dec : (Fin t → Nat) → (Fin b → Nat) → Nat),
      ∀ (n : Nat) (A : Finset (Fin p × Fin n)) (F : Finset (Fin n × Fin n)),
        (∀ edge ∈ F, edge.1 < edge.2) →
        ∀ (v : Fin p → Nat), (∀ i c, fits A F {i} c ↔ v i ≤ c) →
        ∀ (x : Fin t → Nat) (y : Fin b → Nat),
          (∀ j, x j ≤ v (S j)) → (∀ j, y j ≤ v (ask x j)) →
          (Finset.univ.filter (fun j => x j < v (S j))).card +
            (Finset.univ.filter (fun j => y j < v (ask x j))).card ≤ e →
          ∀ r, dec x y ≤ r ↔ safeAt A F r
  let count := fun (S : Fin t → Fin p) (i : Fin p) =>
    (Finset.univ.filter (fun j => S j = i)).card
  (∀ S : Fin t → Fin p, recovers S ↔
    ∀ order : Equiv.Perm (Fin p),
      (∑ j : Fin p, (e+1 - (Finset.univ.filter (fun i : Fin p => i ≤ j)).sum
        (fun i => count S (order i)))) ≤ b) ∧
  ((∃ S : Fin t → Fin p, recovers S) ↔
    (∑ j : Fin p, (e+1 - ((j.val+1)*(t/p) + ((j.val+1) - (p - t % p))))) ≤ b)
) := by
  intro hit' p q hq joined' ideal' eligible' read hp pq a fits' safe' e t b recovers count
  have priceEq {n} (A : Edges p n) (F : Edges n n) (i : Fin p) (c : Nat) :
      fits' A F {i} c ↔ fits q A F i c := by
    simp only [fits',read,a,fits,Finset.sum_const,nsmul_eq_mul,Finset.mem_singleton,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin,Finset.card_singleton]
    rfl
  have safeEq {n} (A : Edges p n) (F : Edges n n) (r : Nat) : safe' A F r ↔ safe q A F r := Iff.rfl
  have combine (S : Fin t → Fin p) : recovers S ↔ ∀o,width e S o ≤ b := by
    constructor
    · rintro ⟨ask,dec,works⟩
      apply adversary q e S pq
      refine ⟨ask,dec,?_⟩
      intro v cap x y xl yl err r
      obtain ⟨n,A,F,edges,price⟩:=realize v (cap trivial)
      have declared i c := (priceEq A F i c).trans (price i c)
      have h:=works n A F edges v declared x y xl yl (by simpa only [errors,filterUnique] using err) r
      exact h.trans ((safeEq ..).trans (safePrice v price))
    · intro bound
      obtain ⟨ask,dec,works⟩:=decode q e S hp bound
      refine ⟨ask,dec,?_⟩
      intro n A F _ v declared x y xl yl err r
      have price i c := (priceEq A F i c).symm.trans (declared i c)
      exact (works v (fun z => z.elim) x y xl yl (by simpa only [errors,filterUnique] using err) r).trans ((safePrice v price).symm.trans (safeEq ..).symm)
  refine ⟨?_,?_⟩
  · intro S;simpa only [width,prefixCount,count,tally,filterUnique] using combine S
  · change (∃ S,recovers S) ↔ fairWidth p t e ≤ b
    constructor
    · rintro ⟨S,h⟩
      have bound:=(combine S).mp h (Tuple.sort (tally S))
      apply Nat.le_trans _ bound
      exact Finset.sum_le_sum (fun j _ => Nat.sub_le_sub_left (sortedBound S hp j) _)
    · intro budget;obtain ⟨S,good⟩:=balanced hp t
      refine ⟨S,(combine S).mpr (fun o => Nat.le_trans ?_ budget)⟩
      exact Finset.sum_le_sum (fun j _ => Nat.sub_le_sub_left (good o j) _)
