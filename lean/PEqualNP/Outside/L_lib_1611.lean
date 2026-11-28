import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1611_aux
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
end PEqualNP.Outside.L_lib_1611_aux

namespace PEqualNP.Outside.L_lib_1611_aux
open scoped Classical
def Separated (P : Bank m) := ∀A∈P,∀B∈P,A≠B → Disjoint A B
def credit (P : Bank m) := ∑A∈P,(A.card-1)
theorem mergeBlocks {P : Bank m} (sep : Separated P) {X Y} (hx : X∈P) (hy : Y∈P)
    (ne : X≠Y) (nx : X.Nonempty) (ny : Y.Nonempty) :
    ∃Q : Bank m,Separated Q ∧ credit Q≤credit P+1 ∧ X∪Y∈Q ∧ ∀A∈P,∃B∈Q,A⊆B := by
  classical
  let R := (P.erase X).erase Y
  have y : Y∈P.erase X := Finset.mem_erase.mpr ⟨ne.symm,hy⟩
  have pr {A} (a : A∈R) : A∈P := (Finset.mem_erase.mp (Finset.mem_erase.mp a).2).2
  have dis {A} (a : A∈R) : Disjoint (X∪Y) A := by
    obtain ⟨ay,h⟩:=Finset.mem_erase.mp a;obtain ⟨ax,ap⟩:=Finset.mem_erase.mp h
    exact Finset.disjoint_union_left.mpr ⟨sep X hx A ap ax.symm,sep Y hy A ap ay.symm⟩
  have fresh : X∪Y∉R := by
    intro mem;have d:=dis mem;obtain ⟨i,hi⟩:=nx
    exact Finset.disjoint_left.mp d (Finset.mem_union_left _ hi) (Finset.mem_union_left _ hi)
  refine ⟨insert (X∪Y) R,?_,?_,Finset.mem_insert_self ..,?_⟩
  · intro A a B b ab;rcases Finset.mem_insert.mp a with rfl|a
    · rcases Finset.mem_insert.mp b with rfl|b
      · exact (ab rfl).elim
      · exact dis b
    · rcases Finset.mem_insert.mp b with rfl|b
      · exact (dis a).symm
      · exact sep A (pr a) B (pr b) ab
  · have xy:=sep X hx Y hy ne
    have a:=Finset.sum_erase_add P (fun A : Bits m => A.card-1) hx
    have b:=Finset.sum_erase_add (P.erase X) (fun A : Bits m => A.card-1) y
    unfold credit;rw [Finset.sum_insert fresh,Finset.card_union_of_disjoint xy]
    change R.sum (fun A => A.card-1)+(Y.card-1)=_ at b
    have px:=Finset.card_pos.mpr nx;have py:=Finset.card_pos.mpr ny;omega
  · intro A h
    by_cases ax:A=X
    · exact ⟨_,Finset.mem_insert_self ..,ax ▸ Finset.subset_union_left⟩
    by_cases ay:A=Y
    · exact ⟨_,Finset.mem_insert_self ..,ay ▸ Finset.subset_union_right⟩
    exact ⟨A,Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨ay,Finset.mem_erase.mpr ⟨ax,h⟩⟩),Finset.Subset.rfl⟩
theorem forest {B : Bank m} (ch : Chain (seed m) r B) :
    ∃P : Bank m,Separated P ∧ credit P≤r ∧ ∀A∈B,A.Nonempty → ∃T∈P,A⊆T := by
  induction ch with
  | start =>
    let P : Bank m:=Finset.univ.image fun i => {i}
    refine ⟨P,?_,?_,?_⟩
    · intro A a B b ne
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp a;obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp b
      simpa using (show i≠j from fun e => ne (e ▸ rfl))
    · unfold credit;have e : ∀A∈P,A.card-1=0 := by intro A h;obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp h;simp
      rw [Finset.sum_eq_zero e]
    · intro A mem non;rcases Finset.mem_insert.mp mem with rfl|a
      · simp at non
      · exact ⟨A,a,Finset.Subset.rfl⟩
  | @step r B a b ch ha hb ih =>
    obtain ⟨P,sep,cap,old⟩:=ih
    have stay (h : (a∪b).Nonempty → ∃Z∈P,a∪b⊆Z) :
        ∃Q : Bank m,Separated Q ∧ credit Q≤r+1 ∧ ∀A∈insert (a∪b) B,A.Nonempty → ∃Z∈Q,A⊆Z := by
      refine ⟨P,sep,by omega,?_⟩
      intro A mem;rcases Finset.mem_insert.mp mem with rfl|mem
      · exact h
      · exact old _ mem
    by_cases aa:a.Nonempty
    · by_cases bb:b.Nonempty
      · obtain ⟨X,x,ax⟩:=old _ ha aa;obtain ⟨Y,y,by'⟩:=old _ hb bb
        by_cases e:X=Y
        · exact stay (fun _ => ⟨Y,y,Finset.union_subset (e ▸ ax) by'⟩)
        obtain ⟨Q,sq,cq,xy,lift⟩:=mergeBlocks sep x y e (aa.mono ax) (bb.mono by')
        refine ⟨Q,sq,by omega,?_⟩
        intro A mem non;rcases Finset.mem_insert.mp mem with rfl|mem
        · exact ⟨_,xy,Finset.union_subset_union ax by'⟩
        · obtain ⟨T,t,at'⟩:=old A mem non;obtain ⟨V,v,tv⟩:=lift T t
          exact ⟨V,v,at'.trans tv⟩
      · have em:=Finset.not_nonempty_iff_eq_empty.mp bb;apply stay;simpa [em] using old _ ha
    · have em:=Finset.not_nonempty_iff_eq_empty.mp aa;apply stay;simpa [em] using old _ hb
end PEqualNP.Outside.L_lib_1611_aux

namespace PEqualNP.Outside.L_lib_1611_aux
open scoped Classical
theorem pairBound {B : Bank m} (ch : Chain (seed m) r B) {A H} (a : A∈B) (b : H∈B)
    (aa : A.Nonempty) (bb : H.Nonempty) : (A∪H).card ≤ r+1+(if Disjoint A H then 1 else 0) := by
  obtain ⟨P,sep,cap,all⟩:=forest ch
  obtain ⟨X,x,ax⟩:=all A a aa;obtain ⟨Y,y,by'⟩:=all H b bb
  by_cases e:X=Y
  · have sub:=Finset.card_le_card (Finset.union_subset (e ▸ ax) by')
    have val : Y.card-1≤credit P := Finset.single_le_sum (f:=fun T : Bits m => T.card-1) (fun _ _ => Nat.zero_le _) y
    split <;> omega
  · have dis:=sep X x Y y e
    have d : Disjoint A H := dis.mono ax by'
    rw [if_pos d]
    have small : ({X,Y} : Bank m)⊆P := Finset.insert_subset_iff.mpr ⟨x,Finset.singleton_subset_iff.mpr y⟩
    have val:=Finset.sum_le_sum_of_subset_of_nonneg (f:=fun T : Bits m => T.card-1) small (fun _ _ _ => Nat.zero_le _)
    have nxy : X∉({Y} : Bank m) := by simp [e]
    simp only [Finset.sum_insert nxy,Finset.sum_singleton] at val
    change _ ≤ credit P at val
    have sub:=Finset.card_le_card (Finset.union_subset_union ax by')
    rw [Finset.card_union_of_disjoint dis] at sub;omega
theorem rawGroup {I : Bank m} (base : seed m⊆I) (A : Bits m) (ne : A.Nonempty) :
    ∃B,Chain I (A.card-1) B ∧ A∈B := by
  let T:=A.image (fun i => ({i} : Bits m))
  have s : T⊆I := by intro Z z;obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp z;exact base (rawMem i)
  obtain ⟨B,ch,has⟩:=collect T s (ne.image _)
  have eq : T.biUnion id=A := by ext i;simp [T]
  have card : T.card=A.card := Finset.card_image_of_injective _ (fun _ _ h => Finset.singleton_inj.mp h)
  exact ⟨B,card ▸ ch,eq ▸ has⟩
theorem extendGroup {I : Bank m} (base : seed m⊆I) {A : Bits m} (a : A∈I) (T : Bits m) :
    ∃B,Chain I T.card B ∧ A∪T∈B := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨I,by simpa using (Chain.start (initial:=I)),by simpa using a⟩
  | @insert i T fresh ih =>
    obtain ⟨B,ch,mem⟩:=ih
    have raw:=grow ch (base (rawMem i))
    rw [Finset.card_insert_of_notMem fresh]
    have eq : (A∪T)∪{i}=A∪insert i T := by ext;simp
    exact ⟨_,.step ch mem raw,eq ▸ Finset.mem_insert_self ..⟩
theorem buildPair (A H : Bits m) (aa : A.Nonempty) (bb : H.Nonempty) (bound :
    (A∪H).card ≤ s+(if Disjoint A H then 1 else 0)) :
    ∃r,r+1 ≤ s ∧ ∃B,Chain (seed m) r B ∧ A∈B ∧ H∈B := by
  by_cases d:Disjoint A H
  · obtain ⟨I,ci,a⟩:=rawGroup Finset.Subset.rfl A aa
    obtain ⟨B,ch,b⟩:=rawGroup (grow ci) H bb
    rw [if_pos d,Finset.card_union_of_disjoint d] at bound
    have p:=Finset.card_pos.mpr aa;have q:=Finset.card_pos.mpr bb
    exact ⟨_,by omega,B,splice ci ch,grow ch a,b⟩
  · let Z:=A∩H
    have ne : Z.Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp d
    obtain ⟨I,ci,z⟩:=rawGroup Finset.Subset.rfl Z ne
    obtain ⟨J,cj,aa'⟩:=extendGroup (grow ci) z (A\Z)
    obtain ⟨B,cb,bb'⟩:=extendGroup (grow (splice ci cj)) (grow cj z) (H\Z)
    have za : Z⊆A := Finset.inter_subset_left
    have zb : Z⊆H := Finset.inter_subset_right
    have ac : Z∪(A\Z)=A := by ext i;simp;grind
    have bc : Z∪(H\Z)=H := by ext i;simp;grind
    rw [ac] at aa';rw [bc] at bb'
    have card:=Finset.card_union_add_card_inter A H
    have u:=Finset.card_le_card za;have v:=Finset.card_le_card zb;have pos:=Finset.card_pos.mpr ne
    rw [if_neg d] at bound
    change _+Z.card=_ at card
    refine ⟨_,?_,B,splice (splice ci cj) cb,grow cb aa',bb'⟩
    rw [Finset.card_sdiff_of_subset za,Finset.card_sdiff_of_subset zb];omega
end PEqualNP.Outside.L_lib_1611_aux

namespace PEqualNP.Outside.L_lib_1611_aux
open scoped Classical
abbrev Cell (m n : Nat) := Fin m × Fin n
def left (n : Nat) (i : Fin m) : Fin (m+n) := i.castAdd n
def right (m : Nat) (j : Fin n) : Fin (m+n) := j.natAdd m
theorem separate (i : Fin m) (j : Fin n) : left n i≠right m j := by
  intro e;have h:=congrArg Fin.val e;change i.val=m+j.val at h;omega
theorem leftInj (m n : Nat) : Function.Injective (left (m:=m) n) := by intro i j e;apply Fin.ext;exact congrArg (fun z : Fin (m+n) => z.val) e
theorem rightInj (m n : Nat) : Function.Injective (right (n:=n) m) := by
  intro i j e;apply Fin.ext;have h:=congrArg Fin.val e;change m+i.val=m+j.val at h;omega
def pack (R : Bits m) (K : Bits n) := R.image (left n) ∪ K.image (right m)
theorem inLeft (R : Bits m) (K : Bits n) (i : Fin m) : left n i ∈ pack R K ↔ i∈R := by
  simp [pack,(leftInj m n).eq_iff,fun j => (separate i j).symm]
theorem inRight (R : Bits m) (K : Bits n) (i : Fin n) : right m i ∈ pack R K ↔ i∈K := by
  simp [pack,(rightInj m n).eq_iff,fun j => separate j i]
theorem packCard (R : Bits m) (K : Bits n) : (pack R K).card=R.card+K.card := by
  unfold pack;rw [Finset.card_union_of_disjoint,Finset.card_image_of_injective _ (leftInj m n),Finset.card_image_of_injective _ (rightInj m n)]
  apply Finset.disjoint_left.mpr;intro u h e;obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp h
  obtain ⟨j,_,eq⟩:=Finset.mem_image.mp e;exact separate i j eq.symm
theorem allNames (v : Fin (m+n)) : (∃i,v=left n i) ∨ (∃j,v=right m j) := by
  refine Fin.addCases (fun i => Or.inl ⟨i,rfl⟩) (fun j => Or.inr ⟨j,rfl⟩) v
def On (A : Bits (m+n)) (e : Cell m n) := left n e.1∈A ∨ right m e.2∈A
def Both (A H : Bits (m+n)) (e : Cell m n) := On A e ∧ On H e
def Plan (D : Finset (Cell m n)) (t : Cell m n → Bool) (s : Nat) :=
  ∃A H : Bits (m+n),A.Nonempty ∧ H.Nonempty ∧ (A∪H).card ≤ s+(if Disjoint A H then 1 else 0) ∧
    ∀e∈D,t e=true ↔ Both A H e
def active (D : Finset (Cell m n)) (t : Cell m n → Bool) (R : Bits m) (K : Bits n) :=
  D.filter (fun e => t e=true ∧ e.1∉R ∧ e.2∉K)
def Criterion (D : Finset (Cell m n)) (t : Cell m n → Bool) (s : Nat) :=
  ∃R : Bits m,∃K : Bits n,(∀e∈D,e.1∈R ∨ e.2∈K → t e=true) ∧
    let P:=active D t R K
    let X:=P.image Prod.fst
    let Y:=P.image Prod.snd
    (∃x : Fin m → Bool,∃y : Fin n → Bool,∀e∈D,e.1∈X → e.2∈Y → (x e.1 ^^ y e.2)=t e) ∧
      R.card+K.card+X.card+Y.card ≤ s+(if R=∅ ∧ K=∅ then 1 else 0)
end PEqualNP.Outside.L_lib_1611_aux

namespace PEqualNP.Outside.L_lib_1611_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
noncomputable def sample (x : Fin m → Bool) (A : Bits m) := decide (∃i∈A,x i=true)
theorem sampleUnion (x : Fin m → Bool) (A B : Bits m) : (sample x A || sample x B)=sample x (A∪B) := by
  apply Bool.eq_iff_iff.mpr;simp only [Bool.or_eq_true,sample,decide_eq_true_eq,Finset.mem_union];grind
def readInput (x : Fin m → Bool) := List.ofFn x
def tick (w : List Bool) (g : Gate) := w++[g.op.eval (g.inputs.map fun j => w.getD j false)]
def legal (g : Gate) := g.op=.or ∧ g.inputs.length≤2
def Acc (r : Nat) (values : (Fin m → Bool) → List Bool) :=
  ∃u≤r,∃B : Bank m,Chain (seed m) u B ∧ ∃names : List (Bits m),
    (∀A∈names,A∈B) ∧ ∅∈B ∧ ∀i,values i=names.map (sample i)
theorem rawAcc (m) : Acc 0 (readInput (m:=m)) := by
  let names := List.ofFn (fun i : Fin m => ({i} : Bits m))
  refine ⟨0,le_rfl,seed m,.start,names,?_,by simp [seed],?_⟩
  · intro A h;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp h;exact rawMem i
  · intro i;simp only [readInput,names,List.map_ofFn];congr 1;funext u
    simp [sample,Function.comp_def]
theorem getSample (names : List (Bits m)) (j : Nat) (i : Fin m → Bool) :
    (names.map (sample i)).getD j false=sample i (names.getD j ∅) := by
  have f : sample i ∅=false := by simp [sample]
  rw [←f];exact List.getD_map ..
theorem stepAcc {v : (Fin m → Bool) → List Bool} (ac : Acc r v) (g : Gate) (leg : legal g) : Acc (r+1) (fun i => tick (v i) g) := by
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
        exact sampleUnion ..
theorem allWires (C : Circuit) (m : Nat) (leg : ∀g∈C.gates,legal g) :
    Acc C.size (fun x : Fin m → Bool => C.wires (readInput x)) := by
  have loop (gs : List Gate) {v : (Fin m → Bool) → List Bool} {r} (ac : Acc r v) (l : ∀g∈gs,legal g) :
      Acc (r+gs.length) (fun i => gs.foldl tick (v i)) := by
    induction gs generalizing v r with
    | nil => simpa using ac
    | cons g gs ih =>
      have next:=ih (stepAcc ac g (l _ (by simp))) (fun j h => l j (by simp [h]))
      simpa [Nat.add_assoc,Nat.add_comm 1] using next
  change Acc C.gates.length (fun x => C.gates.foldl tick (readInput x))
  simpa only [Nat.zero_add] using loop C.gates (rawAcc m) leg
end PEqualNP.Outside.L_lib_1611_aux

namespace PEqualNP.Outside.L_lib_1611_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
def testRun (gs : List Gate) (i : Fin m → Bool) := gs.foldl tick (readInput i)
def Seen (gs : List Gate) (A : Bits m) := ∃j < m+gs.length,∀i : Fin m → Bool,(testRun gs i).getD j false=sample i A
def Good (m : Nat) (gs : List Gate) := (∀g∈gs,g.op=.or ∧ g.inputs.length=2) ∧ ReadsBack m ⟨gs,0⟩
theorem runLen (gs : List Gate) (i : Fin m → Bool) : (testRun gs i).length=m+gs.length := by
  have aux (l : List Gate) (w : List Bool) : (l.foldl tick w).length=w.length+l.length := by
    induction l generalizing w with
    | nil => simp
    | cons g l ih => simp [ih,tick];omega
  simp [testRun,aux,readInput]
theorem extendRun (gs : List Gate) (g : Gate) (i : Fin m → Bool) : testRun (gs++[g]) i=tick (testRun gs i) g := by simp [testRun]
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
    rw [ea,eb];simpa using sampleUnion i A B
theorem emit {B : Bank m} (ch : Chain (seed m) r B) :
    ∃gs : List Gate,gs.length≤r ∧ Good m gs ∧ ∀A∈B,A.Nonempty → Seen gs A := by
  induction ch with
  | start =>
    refine ⟨[],by simp,by simp [Good,ReadsBack],?_⟩
    intro A mem ne;rcases Finset.mem_insert.mp mem with rfl|mem
    · simp at ne
    · obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp mem
      refine ⟨a.val,by simp,?_⟩
      intro i;simp [testRun,readInput,sample]
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
end PEqualNP.Outside.L_lib_1611_aux

namespace PEqualNP.Outside.L_lib_1611_aux
open scoped Classical
theorem planCriterion {D : Finset (Cell m n)} {t : Cell m n → Bool} (ok : Plan D t s) : Criterion D t s := by
  classical
  obtain ⟨A,H,_,_,cap,eval⟩:=ok
  let R:=Finset.univ.filter (fun i => left n i∈A ∧ left n i∈H)
  let K:=Finset.univ.filter (fun j => right m j∈A ∧ right m j∈H)
  let P:=active D t R K
  let X:=P.image Prod.fst
  let Y:=P.image Prod.snd
  have rr (i) : i∈R ↔ left n i∈A ∧ left n i∈H := by simp [R]
  have kk (j) : j∈K ↔ right m j∈A ∧ right m j∈H := by simp [K]
  have props (e) (h : e∈P) : Both A H e ∧ e.1∉R ∧ e.2∉K := by
    obtain ⟨d,on,r,k⟩:=Finset.mem_filter.mp h;exact ⟨(eval _ d).mp on,r,k⟩
  have xp i (hi : i∈X) : i∉R ∧ (left n i∈A ∨ left n i∈H) := by
    obtain ⟨e,mem,rfl⟩:=Finset.mem_image.mp hi;obtain ⟨on,r,k⟩:=props _ mem
    refine ⟨r,?_⟩;rw [kk] at k;unfold Both On at on;tauto
  have yp j (hj : j∈Y) : j∉K ∧ (right m j∈A ∨ right m j∈H) := by
    obtain ⟨e,mem,rfl⟩:=Finset.mem_image.mp hj;obtain ⟨on,r,k⟩:=props _ mem
    refine ⟨k,?_⟩;rw [rr] at r;unfold Both On at on;tauto
  refine ⟨R,K,?_,⟨fun i => decide (left n i∈A),fun j => decide (right m j∈A),?_⟩,?_⟩
  · intro e d h;apply (eval _ d).mpr;rcases h with h|h
    · obtain ⟨a,b⟩:=(rr _).mp h;exact ⟨Or.inl a,Or.inl b⟩
    · obtain ⟨a,b⟩:=(kk _).mp h;exact ⟨Or.inr a,Or.inr b⟩
  · intro e d x y;obtain ⟨nx,xc⟩:=xp _ x;obtain ⟨ny,yc⟩:=yp _ y
    rw [rr] at nx;rw [kk] at ny
    apply Bool.eq_iff_iff.mpr;rw [eval _ d];unfold Both On
    by_cases a:left n e.1∈A <;> by_cases b:right m e.2∈A <;> simp [a,b] at * <;> tauto
  · have sub : pack (R∪X) (K∪Y)⊆A∪H := by
      intro i hi;rcases allNames i with ⟨j,rfl⟩|⟨j,rfl⟩
      · rcases Finset.mem_union.mp ((inLeft ..).mp hi) with h|h
        · exact Finset.mem_union_left _ ((rr _).mp h).1
        · exact Finset.mem_union.mpr (xp _ h).2
      · rcases Finset.mem_union.mp ((inRight ..).mp hi) with h|h
        · exact Finset.mem_union_left _ ((kk _).mp h).1
        · exact Finset.mem_union.mpr (yp _ h).2
    have rx : Disjoint R X := Finset.disjoint_left.mpr (fun _ a b => (xp _ b).1 a)
    have ky : Disjoint K Y := Finset.disjoint_left.mpr (fun _ a b => (yp _ b).1 a)
    have bound:=Finset.card_le_card sub
    rw [packCard,Finset.card_union_of_disjoint rx,Finset.card_union_of_disjoint ky] at bound
    have eq : Disjoint A H ↔ R=∅ ∧ K=∅ := by
      rw [Finset.disjoint_left];constructor
      · intro d;constructor
        · apply Finset.eq_empty_iff_forall_notMem.mpr;intro i h;exact d ((rr i).mp h).1 ((rr i).mp h).2
        · apply Finset.eq_empty_iff_forall_notMem.mpr;intro j h;exact d ((kk j).mp h).1 ((kk j).mp h).2
      · rintro ⟨r,k⟩ i a b;rcases allNames i with ⟨i,rfl⟩|⟨j,rfl⟩
        · have v:=(rr i).mpr ⟨a,b⟩;simp [r] at v
        · have v:=(kk j).mpr ⟨a,b⟩;simp [k] at v
    rw [if_congr eq rfl rfl] at cap
    change R.card+K.card+X.card+Y.card ≤ _;omega
end PEqualNP.Outside.L_lib_1611_aux

namespace PEqualNP.Outside.L_lib_1611_aux
open scoped Classical
theorem criterionPlan {D : Finset (Cell m n)} {t : Cell m n → Bool}
    (pos : ∃e∈D,t e=true) (ok : Criterion D t s) : Plan D t s := by
  classical
  obtain ⟨R,K,line,⟨x,y,parity⟩,cap⟩:=ok
  let P:=active D t R K
  let X:=P.image Prod.fst
  let Y:=P.image Prod.snd
  let A:=pack (R∪X.filter (fun i => x i=true)) (K∪Y.filter (fun j => y j=true))
  let H:=pack (R∪X.filter (fun i => x i=false)) (K∪Y.filter (fun j => y j=false))
  have lA i : left n i∈A ↔ i∈R ∨ (i∈X ∧ x i=true) := by simp [A,inLeft]
  have rA j : right m j∈A ↔ j∈K ∨ (j∈Y ∧ y j=true) := by simp [A,inRight]
  have lH i : left n i∈H ↔ i∈R ∨ (i∈X ∧ x i=false) := by simp [H,inLeft]
  have rH j : right m j∈H ↔ j∈K ∨ (j∈Y ∧ y j=false) := by simp [H,inRight]
  have ev (e) (d : e∈D) : t e=true ↔ Both A H e := by
    unfold Both On;rw [lA,lH,rA,rH]
    by_cases h : e.1∈R ∨ e.2∈K
    · rw [line e d h];tauto
    have posXY (on : t e=true) : e.1∈X ∧ e.2∈Y := by
      have p : e∈P := Finset.mem_filter.mpr ⟨d,on,fun r => h (Or.inl r),fun k => h (Or.inr k)⟩
      exact ⟨Finset.mem_image_of_mem _ p,Finset.mem_image_of_mem _ p⟩
    have par (a : e.1∈X) (b : e.2∈Y) := parity e d a b
    cases xx:x e.1 <;> cases yy:y e.2 <;> simp [xx,yy] at par ⊢ <;> grind
  obtain ⟨e,de,on⟩:=pos
  have witness:= (ev e de).mp on
  have existsName (Z : Bits (m+n)) (h : On Z e) : Z.Nonempty := h.elim (fun z => ⟨_,z⟩) (fun z => ⟨_,z⟩)
  refine ⟨A,H,existsName _ witness.1,existsName _ witness.2,?_,ev⟩
  have sub : A∪H⊆pack (R∪X) (K∪Y) := by
    intro i h;rcases allNames i with ⟨j,rfl⟩|⟨j,rfl⟩
    · simp only [Finset.mem_union,lA,lH,inLeft] at h ⊢;tauto
    · simp only [Finset.mem_union,rA,rH,inRight] at h ⊢;tauto
  have bound:=Finset.card_le_card sub;rw [packCard] at bound
  have ra:=Finset.card_union_le R X;have ka:=Finset.card_union_le K Y
  change R.card+K.card+X.card+Y.card ≤ s+(if R=∅ ∧ K=∅ then 1 else 0) at cap
  by_cases em:R=∅ ∧ K=∅
  · have dis : Disjoint A H := by
      apply Finset.disjoint_left.mpr;intro i a b;rcases allNames i with ⟨j,rfl⟩|⟨j,rfl⟩
      · rw [lA] at a;rw [lH] at b;simp [em.1] at a b;grind
      · rw [rA] at a;rw [rH] at b;simp [em.2] at a b;grind
    rw [if_pos dis];rw [if_pos em] at cap;omega
  · rw [if_neg em] at cap;split <;> omega
end PEqualNP.Outside.L_lib_1611_aux

namespace PEqualNP.Outside.L_lib_1611_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
def probe (e : Cell m n) (i : Fin (m+n)) := decide (i=left n e.1 ∨ i=right m e.2)
theorem probeInput (e : Cell m n) : readInput (probe e)=PEqualNP.Represents.oneEach e.1 e.2 := by
  unfold readInput PEqualNP.Represents.oneEach;rw [List.ofFn_add]
  congr 1
  · apply congrArg List.ofFn;funext i;change decide (left n i=left n e.1 ∨ left n i=right m e.2)=_
    simp [(leftInj m n).eq_iff,separate]
  · apply congrArg List.ofFn;funext j;change decide (right m j=left n e.1 ∨ right m j=right m e.2)=_
    simp [(rightInj m n).eq_iff,(separate e.1 j).symm]
theorem probeOn (e : Cell m n) (A : Bits (m+n)) : sample (probe e) A=true ↔ On A e := by
  simp only [sample,probe,decide_eq_true_eq,On];grind
def Fits (D : Finset (Cell m n)) (t : Cell m n → Bool) (s : Nat) :=
  ∃ (C : Circuit) (u v : Nat), ReadsBack (m+n) C ∧ (∀g∈C.gates,g.op=.or ∧ g.inputs.length=2) ∧
    u < m+n+C.size ∧ v < m+n+C.size ∧ C.size+1 ≤ s ∧
    ∀e∈D,(({C with output:=u} : Circuit).eval (PEqualNP.Represents.oneEach e.1 e.2) &&
      ({C with output:=v} : Circuit).eval (PEqualNP.Represents.oneEach e.1 e.2))=t e
theorem readPair {D : Finset (Cell m n)} {t : Cell m n → Bool} (pos : ∃e∈D,t e=true)
    (ok : Fits D t s) : Plan D t s := by
  obtain ⟨C,u,v,_,leg,_,_,cost,out⟩:=ok
  obtain ⟨r,cap,B,ch,names,known,empty,eq⟩:=allWires C (m+n) (fun g h => ⟨(leg _ h).1,(leg _ h).2.le⟩)
  let get (j : Nat) := names.getD j ∅
  have mem j : get j∈B := by
    unfold get;by_cases len:j<names.length
    · simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem len] using known _ (List.getElem_mem len)
    · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : names.length≤j),empty]
  have read (j : Nat) (e : Cell m n) : ({C with output:=j} : Circuit).eval (PEqualNP.Represents.oneEach e.1 e.2)=sample (probe e) (get j) := by
    rw [←probeInput e];change (C.wires (readInput (probe e))).getD j false=_
    have ex : C.wires (readInput (probe e))=names.map (sample (probe e)) := eq (probe e);rw [ex,getSample]
  have ev (e) (he : e∈D) : t e=true ↔ Both (get u) (get v) e := by
    rw [←out e he,read,read];exact Bool.and_eq_true_iff.trans (and_congr (probeOn _ _) (probeOn _ _))
  obtain ⟨e,he,on⟩:=pos;obtain ⟨a,b⟩:=(ev e he).mp on
  have ne (Z : Bits (m+n)) (z : On Z e) : Z.Nonempty := z.elim (fun h => ⟨_,h⟩) (fun h => ⟨_,h⟩)
  have ca:=pairBound ch (mem u) (mem v) (ne _ a) (ne _ b)
  exact ⟨get u,get v,ne _ a,ne _ b,by omega,ev⟩
theorem writePair {D : Finset (Cell m n)} {t : Cell m n → Bool} (plan : Plan D t s) : Fits D t s := by
  obtain ⟨A,H,aa,hh,cap,ev⟩:=plan
  obtain ⟨r,cost,B,ch,a,h⟩:=buildPair A H aa hh cap
  obtain ⟨gs,sz,good,all⟩:=emit ch
  obtain ⟨u,hu,eu⟩:=all A a aa;obtain ⟨v,hv,eh⟩:=all H h hh
  refine ⟨⟨gs,0⟩,u,v,good.2,good.1,hu,hv,by change gs.length+1 ≤ s;omega,?_⟩
  intro e de;rw [←probeInput e]
  change ((testRun gs (probe e)).getD u false && (testRun gs (probe e)).getD v false)=t e
  rw [eu,eh];apply Bool.eq_iff_iff.mpr;exact Bool.and_eq_true_iff.trans ((and_congr (probeOn _ _) (probeOn _ _)).trans (ev e de).symm)
end PEqualNP.Outside.L_lib_1611_aux

open PEqualNP.Outside.L_lib_1611_aux in
theorem PEqualNP.Outside.L_lib_1611 : (
  let fits := fun {m n : Nat} (D : Finset (Fin m × Fin n))
      (t : Fin m × Fin n → Bool) (s : Nat) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : Nat),
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (m+n) C ∧
      (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length = 2) ∧
      u < m+n+C.size ∧ v < m+n+C.size ∧ C.size+1 ≤ s ∧
      ∀ e ∈ D,
        (({C with output := u} : PEqualNP.CircuitLowerBounds.Circuit).eval
          (PEqualNP.Represents.oneEach e.1 e.2) &&
         ({C with output := v} : PEqualNP.CircuitLowerBounds.Circuit).eval
          (PEqualNP.Represents.oneEach e.1 e.2)) = t e
  ∀ (m n : Nat) (D : Finset (Fin m × Fin n)) (t : Fin m × Fin n → Bool),
    (∃ e ∈ D, t e = true) → ∀ s : Nat, fits D t s ↔
      ∃ (R : Finset (Fin m)) (K : Finset (Fin n)),
        (∀ e ∈ D, e.1 ∈ R ∨ e.2 ∈ K → t e = true) ∧
        let P := D.filter (fun e => t e = true ∧ e.1 ∉ R ∧ e.2 ∉ K)
        let X := P.image Prod.fst
        let Y := P.image Prod.snd
        (∃ (x : Fin m → Bool) (y : Fin n → Bool),
          ∀ e ∈ D, e.1 ∈ X → e.2 ∈ Y → (x e.1 ^^ y e.2) = t e) ∧
        R.card + K.card + X.card + Y.card ≤ s + (if R = ∅ ∧ K = ∅ then 1 else 0)
) := by
  intro fits m n D t pos s
  change Fits D t s ↔ Criterion D t s
  exact ⟨fun h => planCriterion (readPair pos h),fun h => writePair (criterionPlan pos h)⟩
