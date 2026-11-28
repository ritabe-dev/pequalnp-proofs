import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1673_aux
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
end PEqualNP.Outside.L_lib_1673_aux
namespace PEqualNP.Outside.L_lib_1673_aux
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
end PEqualNP.Outside.L_lib_1673_aux
namespace PEqualNP.Outside.L_lib_1673_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
def extend (f : List α → Gate → α) (w : List α) (g : Gate) := w++[f w g]
def run (f : List α → Gate → α) (w : List α) (gs : List Gate) := gs.foldl (extend f) w
theorem appendRun (f : List α → Gate → α) (w) (gs more : List Gate) : run f w (gs++more)=run f (run f w gs) more := by simp [run]
theorem runLength (f : List α → Gate → α) (w) (gs : List Gate) : (run f w gs).length=w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih => change (run f (extend f w g) gs).length=_;rw [ih];simp [extend];omega
theorem kept (f : List α → Gate → α) (w) (gs : List Gate) (d : α) {i} (h : i<w.length) :
    (run f w gs).getD i d=w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run f (extend f w g) gs).getD i d=_
    rw [ih (extend f w g) (by simp [extend];omega)];exact List.getD_append _ _ _ _ h
theorem atGate (f : List α → Gate → α) (w) (C : Circuit) (d : α) {j} (hj : j<C.size) :
    (run f w C.gates).getD (w.length+j) d=f (run f w (C.gates.take j)) (gateAt C j) := by
  have len : (C.gates.take j).length=j := by simp [List.length_take,show j≤C.gates.length from hj.le]
  have decomp : C.gates=(C.gates.take j++[gateAt C j])++C.gates.drop (j+1) := by
    change j<C.gates.length at hj
    have e : gateAt C j=C.gates[j] := by simp [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
    rw [e,←List.take_succ_eq_append_getElem (l:=C.gates) (i:=j) hj,List.take_append_drop]
  conv_lhs => rw [decomp,appendRun]
  rw [kept _ _ _ _ (by simp [runLength,len])]
  rw [appendRun];change ((run f w (C.gates.take j))++[_]).getD _ d=_
  have p : (run f w (C.gates.take j)).length=w.length+j := by rw [runLength,len]
  rw [←p,List.getD_append_right _ _ _ _ le_rfl,Nat.sub_self];rfl
theorem atParent (f : List α → Gate → α) (w) (C : Circuit) (d : α) {j i} (hj : j≤C.size) (lt : i<w.length+j) :
    (run f w (C.gates.take j)).getD i d=(run f w C.gates).getD i d := by
  conv_rhs => rw [←List.take_append_drop j C.gates,appendRun]
  symm;apply kept;rw [runLength,List.length_take,Nat.min_eq_left (show j≤C.gates.length from hj)];exact lt
def opEval (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)
def worth (C : Circuit) (x : List Bool) (i : Nat) := (C.wires x).getD i false
theorem worthInput (C : Circuit) (x : List Bool) {i} (h : i<x.length) : worth C x i=x.getD i false := kept opEval x C.gates false h
theorem worthGate (C : Circuit) (x : List Bool) (back : ReadsBack x.length C) {j} (hj : j<C.size)
    {a b} (parents : (gateAt C j).inputs=[a,b]) :
    worth C x (x.length+j)=(gateAt C j).op.eval [worth C x a,worth C x b] := by
  change (run opEval x C.gates).getD _ false=_
  rw [atGate _ _ _ _ hj];unfold opEval
  simp only [parents,List.map_cons,List.map_nil];rw [atParent _ _ _ _ hj.le (back j hj a (by simp [parents])),atParent _ _ _ _ hj.le (back j hj b (by simp [parents]))];rfl
theorem pairInputs {l : List Nat} (sz : l.length=2) : ∃a b,l=[a,b] := by
  cases l with
  | nil => simp at sz
  | cons a l => cases l with
    | nil => simp at sz
    | cons b l => cases l <;> simp_all
end PEqualNP.Outside.L_lib_1673_aux
namespace PEqualNP.Outside.L_lib_1673_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
def rawList (t : Nat) := List.ofFn (fun i : Fin t => ({i} : Bits t))
def unionOp (w : List (Bits t)) (g : Gate) := w.getD (g.inputs.getD 0 0) ∅ ∪ w.getD (g.inputs.getD 1 0) ∅
def deps (t : Nat) (C : Circuit) (i : Nat) : Bits t := (run unionOp (rawList t) C.gates).getD i ∅
theorem rawDep (t : Nat) (C : Circuit) (i : Fin t) : deps t C i={i} := by
  unfold deps;rw [kept _ _ _ _ (by simp [rawList])];simp [rawList]
theorem gateDep (t : Nat) (C : Circuit) (back : ReadsBack t C) {j} (h : j<C.size) {a b}
    (eq : (gateAt C j).inputs=[a,b]) : deps t C (t+j)=deps t C a∪deps t C b := by
  have l : (rawList t).length=t := by simp [rawList]
  unfold deps;have hgate:=atGate unionOp (rawList t) C (∅ : Bits t) h;rw [l] at hgate;rw [hgate]
  simp only [unionOp,eq];change (run unionOp (rawList t) (C.gates.take j)).getD a ∅ ∪ (run unionOp (rawList t) (C.gates.take j)).getD b ∅=_
  rw [atParent _ _ _ _ h.le (by rw [l];apply back j h a; simp [eq]),atParent _ _ _ _ h.le (by rw [l];apply back j h b;simp [eq])]
def probe (e : Cell m n) (i : Fin (m+n)) := decide (i=left n e.1 ∨ i=right m e.2)
theorem probeInput (e : Cell m n) : List.ofFn (probe e)=PEqualNP.Represents.oneEach e.1 e.2 := by
  unfold PEqualNP.Represents.oneEach;rw [List.ofFn_add]
  congr 1
  · apply congrArg List.ofFn;funext i;change decide (left n i=left n e.1 ∨ left n i=right m e.2)=_
    simp [(leftInj m n).eq_iff,separate]
  · apply congrArg List.ofFn;funext j;change decide (right m j=left n e.1 ∨ right m j=right m e.2)=_
    simp [(rightInj m n).eq_iff,(separate e.1 j).symm]
end PEqualNP.Outside.L_lib_1673_aux
namespace PEqualNP.Outside.L_lib_1673_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
def gatesOK (raw p q : Nat) (C : Circuit) := ∀j<C.size,
  let g:=gateAt C j
  g.inputs.length=2 ∧ (if j<p then g.op=.or else if j<p+q then g.op=.and ∧ ∀i∈g.inputs,i<raw+p
  else g.op=.or ∧ ∀i∈g.inputs,raw+p ≤ i)
def Layer (P Z : Finset (Cell m n)) (k : Nat) := ∃(C : Circuit) (p q : Nat),0<q ∧ q ≤ k ∧ p+q ≤ C.size ∧
  m+n+p ≤ C.output ∧ C.output < m+n+C.size ∧ ReadsBack (m+n) C ∧ gatesOK (m+n) p q C ∧
  (∀e∈P,C.eval (PEqualNP.Represents.oneEach e.1 e.2)=true) ∧ ∀e∈Z,C.eval (PEqualNP.Represents.oneEach e.1 e.2)=false
def Family (P Z : Finset (Cell m n)) (k : Nat) := ∃q,0<q ∧ q ≤ k ∧ ∃A B : Fin q → Bits (m+n),
  (∀t,(A t).Nonempty ∧ (B t).Nonempty) ∧ (∀e∈P,∃t,Both (A t) (B t) e) ∧ ∀e∈Z,∀t,¬Both (A t) (B t) e
def val (C : Circuit) (e : Cell m n) (j : Nat) := worth C (List.ofFn (probe e)) j
theorem valueGate (C : Circuit) (e : Cell m n) (back : ReadsBack (m+n) C) {j} (hj : j<C.size) {a b} (pp : (gateAt C j).inputs=[a,b]) :
    val C e (m+n+j)=(gateAt C j).op.eval [val C e a,val C e b] := by
  have hh : ReadsBack (List.ofFn (probe e)).length C := by simpa using back
  simpa only [List.length_ofFn,val] using worthGate C (List.ofFn (probe e)) hh hj pp
theorem prefixValue (C : Circuit) (back : ReadsBack (m+n) C) (ok : gatesOK (m+n) p q C) (first : p ≤ C.size) (e : Cell m n) :
    ∀i,i < m+n+p → (val C e i=true ↔ On (deps (m+n) C i) e) := by
  intro i;induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro small
    by_cases raw:i < m+n
    · let u : Fin (m+n) := ⟨i,raw⟩
      have a:=rawDep (m+n) C u
      have b:=worthInput C (List.ofFn (probe e)) (i:=i) (by simp [raw])
      change deps (m+n) C i={u} at a
      unfold val;rw [a,b];have get : (List.ofFn (probe e)).getD i false=probe e u := by simp [List.getD_eq_getElem?_getD,raw,u]
      rw [get];simp only [probe,decide_eq_true_eq,On,Finset.mem_singleton];grind
    · let j:=i-(m+n)
      have eq : m+n+j=i := by dsimp [j];omega
      have early : j<p := by omega
      have hj : j<C.size := by omega
      obtain ⟨sz,typ⟩:=ok j hj
      have op : (gateAt C j).op=.or := by simpa [early] using typ
      obtain ⟨a,b,parents⟩:=pairInputs sz
      have ha:=back j hj a (by simp [parents]);have hb:=back j hj b (by simp [parents])
      have av:=ih a (by omega) (by omega);have bv:=ih b (by omega) (by omega)
      rw [←eq,gateDep _ _ back hj parents,valueGate C e back hj parents,op]
      simp only [GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false,Bool.or_eq_true,av,bv,On,Finset.mem_union];tauto
end PEqualNP.Outside.L_lib_1673_aux
namespace PEqualNP.Outside.L_lib_1673_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
noncomputable def sample (x : Fin m → Bool) (A : Bits m) := decide (∃i∈A,x i=true)
theorem sampleUnion (x : Fin m → Bool) (A B : Bits m) : (sample x A || sample x B)=sample x (A∪B) := by
  apply Bool.eq_iff_iff.mpr;simp only [Bool.or_eq_true,sample,decide_eq_true_eq,Finset.mem_union];grind
def readInput (x : Fin m → Bool) := List.ofFn x
def tick (w : List Bool) (g : Gate) := w++[g.op.eval (g.inputs.map fun j => w.getD j false)]
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
      simp [e,g]
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
theorem rawGroup {I : Bank m} (base : seed m⊆I) (A : Bits m) (ne : A.Nonempty) :
    ∃B,Chain I (A.card-1) B ∧ A∈B := by
  let T:=A.image (fun i => ({i} : Bits m))
  have s : T⊆I := by intro Z z;obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp z;exact base (rawMem i)
  obtain ⟨B,ch,has⟩:=collect T s (ne.image _)
  have eq : T.biUnion id=A := by ext i;simp [T]
  have card : T.card=A.card := Finset.card_image_of_injective _ (fun _ _ h => Finset.singleton_inj.mp h)
  exact ⟨B,card ▸ ch,eq ▸ has⟩
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
end PEqualNP.Outside.L_lib_1673_aux
namespace PEqualNP.Outside.L_lib_1673_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
def acc (base q i : Nat) := if i=0 then base else base+q+i-1
def middle (u v : Fin q → Nat) := List.ofFn (fun t => (⟨.and,[u t,v t]⟩ : Gate))
def suffix (base q : Nat) := List.ofFn (fun t : Fin (q-1) => (⟨.or,[acc base q t.val,base+(t.val+1)]⟩ : Gate))
def program (raw : Nat) (gs : List Gate) (u v : Fin q → Nat) : Circuit :=
  ⟨(gs++middle u v)++suffix (raw+gs.length) q,acc (raw+gs.length) q (q-1)⟩
theorem sizeProgram (raw) (gs) (u v : Fin q → Nat) : (program raw gs u v).size=gs.length+q+(q-1) := by simp [program,Circuit.size,middle,suffix,Nat.add_assoc]
theorem oldGate (raw) (gs) (u v : Fin q → Nat) {j} (h : j<gs.length) :
  gateAt (program raw gs u v) j=gateAt ⟨gs,0⟩ j := by unfold gateAt program;simp only;rw [List.getD_append _ _ _ _ (by simp;omega),List.getD_append _ _ _ _ h]
theorem midGate (raw) (gs : List Gate) (u v : Fin q → Nat) (t : Fin q) :
    gateAt (program raw gs u v) (gs.length+t.val)=⟨.and,[u t,v t]⟩ := by
  change ((gs++middle u v)++suffix _ q).getD _ _=_
  rw [List.getD_append _ _ _ _ (by simp [middle]),List.getD_append_right _ _ _ _ (by omega)]
  simp [middle]
theorem endGate (raw) (gs : List Gate) (u v : Fin q → Nat) (t : Fin (q-1)) :
    gateAt (program raw gs u v) (gs.length+q+t.val)=⟨.or,[acc (raw+gs.length) q t.val,raw+gs.length+(t.val+1)]⟩ := by
  change ((gs++middle u v)++suffix _ q).getD _ _=_
  rw [List.getD_append_right _ _ _ _ (by simp [middle])]
  simp [middle,suffix]
theorem accBounds (base q i : Nat) (hq : 0<q) : base≤acc base q i ∧ acc base q i<base+q+i := by unfold acc;split <;> omega
theorem programLegal (raw) (gs : List Gate) (u v : Fin q → Nat) (hq : 0<q) (pre : Good raw gs)
    (bounds : ∀t,u t<raw+gs.length ∧ v t<raw+gs.length) :
    ReadsBack raw (program raw gs u v) ∧ gatesOK raw gs.length q (program raw gs u v) := by
  let C:=program raw gs u v
  let p:=gs.length
  have info j (h : j<C.size) : (∀i∈(gateAt C j).inputs,i<raw+j) ∧
      (gateAt C j).inputs.length=2 ∧ (if j<p then (gateAt C j).op=.or else if j<p+q then (gateAt C j).op=.and ∧
        ∀i∈(gateAt C j).inputs,i<raw+p else (gateAt C j).op=.or ∧ ∀i∈(gateAt C j).inputs,raw+p ≤ i) := by
    by_cases old:j<p
    · rw [if_pos old,oldGate raw gs u v old]
      have m : gateAt ⟨gs,0⟩ j∈gs := by change gs.getD j _∈gs;simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem old] using List.getElem_mem old
      exact ⟨pre.2 j old,(pre.1 _ m).2,(pre.1 _ m).1⟩
    rw [if_neg old];by_cases mid:j<p+q
    · let t : Fin q:=⟨j-p,by omega⟩
      have eq : gs.length+t.val=j := by change p+(j-p)=j;omega
      rw [if_pos mid,←eq,midGate]
      have ht:=bounds t;simp [p] at * <;> omega
    · let t : Fin (q-1):=⟨j-(p+q),by change j<(program raw gs u v).size at h;rw [sizeProgram] at h;dsimp [p] at *;omega⟩
      have eq : gs.length+q+t.val=j := by change p+q+(j-(p+q))=j;omega
      rw [if_neg mid,←eq,endGate];have h1:=accBounds (raw+p) q t.val hq;have h2:=t.isLt
      change _ ∧ _ ∧ _;simp only [List.mem_cons,List.not_mem_nil,or_false,List.length_cons,List.length_nil,Nat.zero_add,true_and,forall_eq_or_imp,forall_eq] <;> dsimp [p] at * <;> omega
  exact ⟨fun j h => (info j h).1,fun j h => (info j h).2⟩
end PEqualNP.Outside.L_lib_1673_aux
namespace PEqualNP.Outside.L_lib_1673_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
theorem probeOn (e : Cell m n) (A : Bits (m+n)) : sample (probe e) A=true ↔ On A e := by
  simp only [sample,probe,decide_eq_true_eq,On];grind
theorem prefixRead (gs : List Gate) (u v : Fin q → Nat) (e : Cell m n) {j} (hj : j < m+n+gs.length) :
    val (program (m+n) gs u v) e j=(testRun gs (probe e)).getD j false := by
  change (run opEval (List.ofFn (probe e)) ((gs++middle u v)++suffix _ q)).getD j false=_
  rw [List.append_assoc,appendRun,kept _ _ _ _ (by rw [runLength,List.length_ofFn];exact hj)]
  rfl
theorem programEval (gs : List Gate) (u v : Fin q → Nat) (hq : 0<q) (A B : Fin q → Bits (m+n))
    (back : ReadsBack (m+n) (program (m+n) gs u v))
    (bounds : ∀j,u j < m+n+gs.length ∧ v j < m+n+gs.length)
    (eu : ∀j x,(testRun gs x).getD (u j) false=sample x (A j))
    (ev : ∀j x,(testRun gs x).getD (v j) false=sample x (B j)) :
    let C:=program (m+n) gs u v
    ∀e : Cell m n,val C e C.output=true ↔ ∃j,Both (A j) (B j) e := by
  let N:=m+n
  let base:=N+gs.length
  let C:=program N gs u v
  intro C' e
  have prod (j : Fin q) : val C e (base+j.val)=true ↔ Both (A j) (B j) e := by
    have h : gs.length+j.val<C.size := by change _<(program N gs u v).size;rw [sizeProgram];omega
    have gate:=midGate N gs u v j
    have par : (gateAt C (gs.length+j.val)).inputs=[u j,v j] := congrArg Gate.inputs gate
    rw [show base+j.val=m+n+(gs.length+j.val) by dsimp [base,N];omega,valueGate C e back h par,gate]
    change (GateOp.and.eval [val (program (m+n) gs u v) e (u j),val (program (m+n) gs u v) e (v j)]=true) ↔ _
    rw [prefixRead _ _ _ _ (bounds j).1,prefixRead _ _ _ _ (bounds j).2,eu,ev]
    simp [GateOp.eval,probeOn,Both]
  have partialOut (i : Nat) (small : i<q) :
      val C e (acc base q i)=true ↔ ∃j : Fin q,j.val ≤ i ∧ Both (A j) (B j) e := by
    induction i with
    | zero =>
      let z : Fin q:=⟨0,small⟩
      have eq : acc base q 0=base+z.val := by simp [acc,z]
      rw [eq,prod];constructor
      · intro yes;exact ⟨z,by simp [z],yes⟩
      · rintro ⟨j,h,yes⟩;have eqj : j=z := Fin.ext (by dsimp [z];omega);simpa [eqj] using yes
    | succ i ih =>
      let t : Fin (q-1):=⟨i,by omega⟩
      let next : Fin q:=⟨i+1,small⟩
      have gate:=endGate N gs u v t
      have h : gs.length+q+i<C.size := by change _<(program N gs u v).size;rw [sizeProgram];omega
      have par : (gateAt C (gs.length+q+i)).inputs=[acc base q i,base+next.val] := congrArg Gate.inputs gate
      have op : (gateAt C (gs.length+q+i)).op=.or := congrArg Gate.op gate
      rw [show acc base q (i+1)=m+n+(gs.length+q+i) by simp [acc,base,N];omega,valueGate C e back h par,op]
      simp only [GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false,Bool.or_eq_true,ih (by omega),prod]
      constructor
      · rintro (⟨j,hj,hb⟩|hb)
        · exact ⟨j,by omega,hb⟩
        · exact ⟨next,le_rfl,hb⟩
      · rintro ⟨j,hj,hb⟩;by_cases early:j.val ≤ i
        · exact Or.inl ⟨j,early,hb⟩
        · have eqj : j=next := Fin.ext (by dsimp [next];omega);exact Or.inr (eqj ▸ hb)
  change val C e (acc base q (q-1))=true ↔ _
  rw [partialOut _ (by omega)]
  exact ⟨fun ⟨j,_,h⟩ => ⟨j,h⟩,fun ⟨j,h⟩ => ⟨j,by have lt:=j.isLt;omega,h⟩⟩
end PEqualNP.Outside.L_lib_1673_aux

namespace PEqualNP.Outside.L_lib_1673_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
theorem readLayer {P Z : Finset (Cell m n)} (fit : Layer P Z k) :
    ∃q,0<q ∧ q ≤ k ∧ ∃A B : Fin q → Bits (m+n),∃live : Finset (Fin q),
    (∀e∈P,∃t∈live,Both (A t) (B t) e) ∧ ∀t∈live,∀e∈Z,¬Both (A t) (B t) e := by
  classical
  obtain ⟨C,p,q,hq,qk,layers,outlo,outhi,back,ok,positive,negative⟩:=fit
  let N:=m+n
  let gate (t : Fin q) := p+t.val
  let root (t : Fin q) := N+gate t
  have mid (t : Fin q) : gate t<C.size := by dsimp [gate];have h:=t.isLt;omega
  have info (t) : (gateAt C (gate t)).op=.and ∧ ∀i∈(gateAt C (gate t)).inputs,i<N+p := by
    have f:= (ok _ (mid t)).2
    have lo : ¬gate t<p := by dsimp [gate];omega
    have hi : gate t<p+q := by dsimp [gate];have h:=t.isLt;omega
    simpa [lo,hi] using f
  choose a b parents using fun t => pairInputs ((ok _ (mid t)).1)
  let A (t : Fin q) := deps N C (a t)
  let B (t : Fin q) := deps N C (b t)
  have prod (t) (e : Cell m n) : val C e (root t)=true ↔ Both (A t) (B t) e := by
    have pa:=(info t).2 (a t) (by simp [parents]);have pb:=(info t).2 (b t) (by simp [parents])
    have first : p ≤ C.size := by omega
    have x:=prefixValue C back ok first e (a t) pa;have y:=prefixValue C back ok first e (b t) pb
    dsimp only [root,N];rw [valueGate C e back (mid t) (parents t),(info t).1]
    simpa [GateOp.eval,Both,A,B] using and_congr x y
  have dp t : deps N C (root t)=A t∪B t := gateDep N C back (mid t) (parents t)
  let reaches (i : Nat) (t : Fin q) := deps N C (root t)⊆deps N C i ∧
    ∀e : Cell m n,val C e (root t)=true → val C e i=true
  have trace (i) : N+p ≤ i → i<N+C.size → ∀e : Cell m n,val C e i=true → ∃t,reaches i t ∧ val C e (root t)=true := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro lo hi e on
      by_cases inside : i<N+p+q
      · let t : Fin q := ⟨i-(N+p),by omega⟩
        have eq : root t=i := by dsimp [root,gate,t];omega
        refine ⟨t,?_,eq ▸ on⟩;unfold reaches;rw [eq];simp
      · let j:=i-N
        have eq : N+j=i := by dsimp [j];omega
        have jj : j<C.size := by omega
        have pre : ¬j<p := by omega
        have aft : ¬j<p+q := by omega
        have typ : (gateAt C j).op=.or ∧ ∀u∈(gateAt C j).inputs,N+p ≤ u := by simpa [pre,aft] using (ok j jj).2
        obtain ⟨u,v,pair⟩:=pairInputs (ok j jj).1
        have dg : deps N C i=deps N C u∪deps N C v := eq ▸ gateDep N C back jj pair
        have vg (z : Cell m n) : val C z i=true ↔ val C z u=true ∨ val C z v=true := by
          rw [←eq,valueGate C z back jj pair,typ.1];simp [GateOp.eval]
        have walk (w : Nat) (mem : w∈(gateAt C j).inputs) (dz : deps N C w⊆deps N C i)
            (vz : ∀z : Cell m n,val C z w=true → val C z i=true) (hit : val C e w=true) :
            ∃t,reaches i t ∧ val C e (root t)=true := by
          have less : w < i := eq ▸ back j jj w mem
          obtain ⟨t,⟨ds,vs⟩,yes⟩:=ih w less (typ.2 _ mem) (by omega) e hit
          exact ⟨t,⟨ds.trans dz,fun z h => vz z (vs z h)⟩,yes⟩
        rcases (vg e).mp on with uOn|vOn
        · exact walk u (by simp [pair]) (by rw [dg];exact Finset.subset_union_left) (fun z h => (vg z).mpr (Or.inl h)) uOn
        · exact walk v (by simp [pair]) (by rw [dg];exact Finset.subset_union_right) (fun z h => (vg z).mpr (Or.inr h)) vOn
  let live:=Finset.univ.filter (reaches C.output)
  have evalEq (e : Cell m n) : val C e C.output=C.eval (PEqualNP.Represents.oneEach e.1 e.2) := by unfold val;rw [probeInput];rfl
  refine ⟨q,hq,qk,A,B,live,?_,?_⟩
  · intro e he;have on : val C e C.output=true := (evalEq _).trans (positive _ he)
    obtain ⟨t,reach,yes⟩:=trace _ outlo outhi _ on
    exact ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,reach⟩,(prod t _).mp yes⟩
  · intro t ht e he both
    have reach : reaches C.output t := (Finset.mem_filter.mp ht).2
    have on:=reach.2 e ((prod t _).mpr both)
    rw [evalEq,negative _ he] at on;contradiction
end PEqualNP.Outside.L_lib_1673_aux

namespace PEqualNP.Outside.L_lib_1673_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
theorem writeLayer {P Z : Finset (Cell m n)} (fam : Family P Z k) : Layer P Z k := by
  classical
  obtain ⟨q,hq,qk,A,B,ne,yes,no⟩:=fam
  let price j := ((A j).card-1)+((B j).card-1)
  have job (j : Fin q) : ∃r≤price j,∃I,Chain (seed (m+n)) r I ∧ A j∈I ∧ B j∈I := by
    obtain ⟨V,cv,a⟩:=rawGroup Finset.Subset.rfl (A j) (ne j).1
    obtain ⟨I,ci,b⟩:=rawGroup (grow cv) (B j) (ne j).2
    exact ⟨_,le_rfl,I,splice cv ci,grow ci a,b⟩
  obtain ⟨r,_,I,ch,all⟩:=batch (seed (m+n)) price (fun j V => A j∈V ∧ B j∈V) (fun _ {_ _} sub h => ⟨sub h.1,sub h.2⟩) job
  obtain ⟨gs,_,pre,seen⟩:=emit ch
  choose u hu eu using fun j => seen (A j) (all j).1 (ne j).1
  choose v hv ev using fun j => seen (B j) (all j).2 (ne j).2
  let C:=program (m+n) gs u v
  have bounds j:=And.intro (hu j) (hv j)
  obtain ⟨back,ok⟩:=programLegal (m+n) gs u v hq pre bounds
  have eval:=programEval gs u v hq A B back bounds eu ev
  have sz : C.size=gs.length+q+(q-1) := sizeProgram _ _ _ _
  have ob:=accBounds (m+n+gs.length) q (q-1) hq
  have bridge (e : Cell m n) : val C e C.output=C.eval (PEqualNP.Represents.oneEach e.1 e.2) := by unfold val;rw [probeInput];rfl
  refine ⟨C,gs.length,q,hq,qk,by omega,ob.1,?_,back,ok,?_,?_⟩
  · change acc _ _ _ < _;omega
  · intro e he;rw [←bridge e];exact (eval _).mpr (yes e he)
  · intro e he;rw [←bridge e];apply Bool.eq_false_iff.mpr
    intro on;obtain ⟨t,hit⟩:=(eval _).mp on;exact no e he t hit
theorem prune {P Z : Finset (Cell m n)} (pos : P.Nonempty) (A B : Fin k → Bits (m+n))
    (yes : ∀e∈P,∃j,Both (A j) (B j) e) (no : ∀e∈Z,∀j,¬Both (A j) (B j) e) : Family P Z k := by
  classical
  let used:=Finset.univ.filter (fun j => (A j).Nonempty ∧ (B j).Nonempty)
  have keep {j} {e : Cell m n} (h : Both (A j) (B j) e) : j∈used := by
    have part {V : Bits (m+n)} (on : On V e) : V.Nonempty := on.elim (fun h => ⟨_,h⟩) (fun h => ⟨_,h⟩)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,part h.1,part h.2⟩
  obtain ⟨e,ep⟩:=pos;obtain ⟨j,hj⟩:=yes _ ep
  let f : ↥used ≃ Fin used.card := Fintype.equivFinOfCardEq (by simp)
  refine ⟨used.card,Finset.card_pos.mpr ⟨j,keep hj⟩,by simpa using Finset.card_le_card (Finset.subset_univ used),
    fun t => A (f.symm t).val,fun t => B (f.symm t).val,fun t => (Finset.mem_filter.mp (f.symm t).property).2,?_,?_⟩
  · intro z hz;obtain ⟨i,on⟩:=yes _ hz;refine ⟨f ⟨i,keep on⟩,?_⟩;simpa using on
  · exact fun z hz t => no z hz _
end PEqualNP.Outside.L_lib_1673_aux

namespace PEqualNP.Outside.L_lib_1673_aux
open scoped Classical
def plus (D : Finset (Cell n n)) := D.filter (fun e => e.1≠e.2)
def minus (D : Finset (Cell n n)) := D.filter (fun e => e.1=e.2)
def Valid (D : Finset (Cell n n)) (c : Fin n → α) :=
  ∀i j,(i,i)∈D → (j,j)∈D → i≠j → (i,j)∈D ∨ (j,i)∈D → c i≠c j
theorem signature {D : Finset (Cell n n)} {k : Nat} (hn : 2 ≤ n) (hk : 0<k) :
    Layer (plus D) (minus D) k ↔ ∃c : Fin n → (Fin k → Bool),Valid D c := by
  classical
  constructor
  · intro fit;obtain ⟨q,hq,qk,A,B,live,yes,no⟩:=readLayer fit
    let bit (i : Fin n) (z : Fin k) := if h:z.val<q then decide (On (A ⟨z.val,h⟩) (i,i)) else false
    refine ⟨bit,?_⟩
    have directed {i j} (di : (i,i)∈D) (dj : (j,j)∈D) (diff : i≠j) (edge : (i,j)∈D) : bit i≠bit j := by
      obtain ⟨a,liveA,hit⟩:=yes (i,j) (Finset.mem_filter.mpr ⟨edge,diff⟩)
      let z : Fin k:=⟨a.val,by have lt:=a.isLt;omega⟩
      intro eq;have same:=congrFun eq z
      have be (l : Fin n) : bit l z=decide (On (A a) (l,l)) := by simp [bit,z,a.isLt]
      rw [be,be] at same
      have sa : On (A a) (i,i) ↔ On (A a) (j,j) := by simpa using congrArg (fun b : Bool => b=true) same |>.to_iff
      have oi:=no _ liveA (i,i) (Finset.mem_filter.mpr ⟨di,rfl⟩)
      have oj:=no _ liveA (j,j) (Finset.mem_filter.mpr ⟨dj,rfl⟩)
      simp only [On,Both] at hit sa oi oj;tauto
    intro i j di dj ij cross
    exact cross.elim (directed di dj ij) (fun y => (directed dj di ij.symm y).symm)
  · rintro ⟨c,ok⟩
    by_cases pos:(plus D).Nonempty
    · let pool (z : Fin k) (s : Bool) := Finset.univ.filter (fun i : Fin n => (i,i)∉D ∨ c i z=s)
      let A z:=pack (pool z true) (pool z true)
      let B z:=pack (pool z false) (pool z false)
      have rule z i j : Both (A z) (B z) (i,j) ↔
        (((i,i)∉D ∨ c i z=true) ∨ ((j,j)∉D ∨ c j z=true)) ∧ (((i,i)∉D ∨ c i z=false) ∨ ((j,j)∉D ∨ c j z=false)) := by
        simp [A,B,pool,On,Both,inLeft,inRight]
      apply writeLayer;apply prune pos A B
      · rintro ⟨i,j⟩ ep;obtain ⟨edge,ij⟩:=Finset.mem_filter.mp ep
        by_cases di:(i,i)∈D
        · by_cases dj:(j,j)∈D
          · have diff:=ok i j di dj ij (Or.inl edge)
            have hit : ∃z,c i z≠c j z := by by_contra! same;exact diff (funext same)
            obtain ⟨z,ne⟩:=hit;refine ⟨z,(rule ..).mpr ?_⟩
            cases x:c i z <;> cases y:c j z <;> simp_all
          · exact ⟨⟨0,hk⟩,(rule ..).mpr ⟨Or.inr (Or.inl dj),Or.inr (Or.inl dj)⟩⟩
        · exact ⟨⟨0,hk⟩,(rule ..).mpr ⟨Or.inl (Or.inl di),Or.inl (Or.inl di)⟩⟩
      · rintro ⟨i,j⟩ ez z hit;obtain ⟨edge,ij⟩:=Finset.mem_filter.mp ez
        change i=j at ij;subst j;have lit:=(rule ..).mp hit;simp [edge] at lit
    · let a : Fin n:=⟨0,by omega⟩;let b : Fin n:=⟨1,by omega⟩
      have ne : a≠b := fun h => by have v:=congrArg Fin.val h;contradiction
      let A : Bits (n+n):={left n a};let B : Bits (n+n):={left n b}
      apply writeLayer;refine ⟨1,by omega,hk,fun _ => A,fun _ => B,fun _ => ⟨Finset.singleton_nonempty _,Finset.singleton_nonempty _⟩,?_,?_⟩
      · intro e he;exact (pos ⟨e,he⟩).elim
      · rintro ⟨i,j⟩ _ _ on
        have s (v : Fin n) : On ({left n v} : Bits (n+n)) (i,j) ↔ i=v := by simp [On,(leftInj n n).eq_iff,(separate v j).symm]
        exact ne (((s a).mp on.1).symm.trans ((s b).mp on.2))
end PEqualNP.Outside.L_lib_1673_aux

namespace PEqualNP.Outside.L_lib_1673_aux
open scoped Classical
def Adj (D : Finset (Fin n × Fin n)) (i j : Fin n) := i≠j ∧ ((i,j)∈D ∨ (j,i)∈D)
theorem adjFlip {D : Finset (Fin n × Fin n)} {i j} (h : Adj D i j) : Adj D j i := ⟨h.1.symm,h.2.symm⟩
def Palette (α : Type) (D : Finset (Fin n × Fin n)) (S : Finset (Fin n)) :=
  ∃ c : Fin n → α,∀i∈S,∀j∈S,Adj D i j → c i≠c j
noncomputable def neighbors (D : Finset (Fin n × Fin n)) (S : Finset (Fin n)) (i : Fin n) := S.filter (Adj D i)
theorem critical [Fintype α] [Nonempty α] {D : Finset (Fin n × Fin n)} {V : Finset (Fin n)} (bad : ¬Palette α D V) :
    ∃ S⊆V,S.Nonempty ∧ ∀i∈S,Fintype.card α ≤ (neighbors D S i).card := by
  classical
  let bads:=V.powerset.filter (fun S => ¬Palette α D S)
  have has : V∈bads := Finset.mem_filter.mpr ⟨Finset.mem_powerset_self _,bad⟩
  obtain ⟨S,mem,minimal⟩:=Finset.exists_min_image bads Finset.card ⟨V,has⟩
  obtain ⟨sub,badS⟩:=Finset.mem_filter.mp mem
  have subV:=Finset.mem_powerset.mp sub
  refine ⟨S,subV,?_,?_⟩
  · by_contra no;rw [Finset.not_nonempty_iff_eq_empty.mp no] at badS
    exact badS ⟨fun _ => Classical.choice inferInstance,by simp⟩
  · intro i hi;by_contra! small
    have fit : Palette α D (S.erase i) := by
      by_contra badE
      have e : S.erase i∈bads := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ((Finset.erase_subset ..).trans subV),badE⟩
      exact (Nat.not_le_of_lt (Finset.card_erase_lt_of_mem hi)) (minimal _ e)
    obtain ⟨c,colors⟩:=fit
    let used:=(neighbors D S i).image c
    have thin : used.card < (Finset.univ : Finset α).card := by
      rw [Finset.card_univ];exact lt_of_le_of_lt Finset.card_image_le small
    obtain ⟨a,unused⟩:=Finset.sdiff_nonempty_of_card_lt_card thin
    have free:= (Finset.mem_sdiff.mp unused).2
    have skip j (hj : j∈S) (edge : Adj D i j) : a≠c j := by
      intro eq;apply free;exact eq ▸ Finset.mem_image_of_mem c (Finset.mem_filter.mpr ⟨hj,edge⟩)
    apply badS;refine ⟨Function.update c i a,?_⟩;intro x hx y hy edge
    by_cases eqx:x=i
    · subst x;simpa [Function.update,edge.1.symm] using skip y hy edge
    by_cases eqy:y=i
    · subst y;simpa [Function.update,eqx] using (skip x hx (adjFlip edge)).symm
    · simpa [Function.update,eqx,eqy] using colors x (Finset.mem_erase.mpr ⟨eqx,hx⟩) y (Finset.mem_erase.mpr ⟨eqy,hy⟩) edge
end PEqualNP.Outside.L_lib_1673_aux

namespace PEqualNP.Outside.L_lib_1673_aux
open scoped Classical
def vertices (D : Finset (Fin n × Fin n)) := Finset.univ.filter (fun i => (i,i)∈D)
def apart (D : Finset (Fin n × Fin n)) := D.filter (fun z => z.1≠z.2)
theorem diagSplit (D : Finset (Fin n × Fin n)) : (vertices D).card+(apart D).card=D.card := by
  have diag : (vertices D).diag=D.filter (fun z => z.1=z.2) := by ext ⟨i,j⟩;simp [vertices,Finset.mem_diag];grind
  have h:=Finset.card_filter_add_card_filter_not (s:=D) (p:=fun z => z.1=z.2)
  rw [←diag,Finset.diag_card] at h;exact h
theorem countEdges (D : Finset (Fin n × Fin n)) (S : Finset (Fin n)) (r : Nat) (degree : ∀i∈S,r ≤ (neighbors D S i).card) :
    S.card*r ≤ 2*(apart D).card := by
  classical
  let P:=apart D
  let R i:=P.filter (fun z => z.1=i)
  let C j:=P.filter (fun z => z.2=j)
  have each i (hi : i∈S) : r ≤ (R i).card+(C i).card := by
    have sub : neighbors D S i ⊆ (R i).image Prod.snd ∪ (C i).image Prod.fst := by
      intro j hj;obtain ⟨_,diff,x|x⟩:=Finset.mem_filter.mp hj
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨x,diff⟩,rfl⟩,rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(j,i),Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨x,diff.symm⟩,rfl⟩,rfl⟩)
    exact (degree _ hi).trans ((Finset.card_le_card sub).trans ((Finset.card_union_le ..).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)))
  have sumR : (∑i,(R i).card)=P.card := by simpa [R] using Finset.sum_card_fiberwise_eq_card_filter P (Finset.univ : Finset (Fin n)) Prod.fst
  have sumC : (∑i,(C i).card)=P.card := by simpa [C] using Finset.sum_card_fiberwise_eq_card_filter P (Finset.univ : Finset (Fin n)) Prod.snd
  have all : (∑i∈S,((R i).card+(C i).card)) ≤ ∑i : Fin n,((R i).card+(C i).card) := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have lo:=Finset.sum_le_sum each
  simp only [Finset.sum_const,nsmul_eq_mul] at lo
  have price : (∑i : Fin n,((R i).card+(C i).card))=P.card+P.card := by rw [Finset.sum_add_distrib,sumR,sumC]
  rw [price] at all;simpa [two_mul,P] using lo.trans all
theorem twiceChoose (r : Nat) : 2*((r+1).choose 2)=(r+1)*r := by
  induction r with
  | zero => decide
  | succ r ih => rw [Nat.choose_succ_succ (r+1) 1,Nat.choose_one_right];nlinarith
theorem lower [Fintype α] [Nonempty α] {D : Finset (Fin n × Fin n)} (bad : ¬Palette α D (vertices D)) :
    let r:=Fintype.card α
    r+1+(r+1).choose 2 ≤ D.card ∧
      (D.card=r+1+(r+1).choose 2 → ∃S⊆vertices D,S.card=r+1 ∧ ∀i∈S,∀j∈S,i≠j → Adj D i j) := by
  intro r
  obtain ⟨S,sub,ne,deg⟩:=critical bad
  have small i : neighbors D S i ⊆ S.erase i := by
    intro j h;obtain ⟨sj,edge⟩:=Finset.mem_filter.mp h;exact Finset.mem_erase.mpr ⟨edge.1.symm,sj⟩
  have positive:=Finset.card_pos.mpr ne
  obtain ⟨i0,hi0⟩:=ne
  have s0:=(deg i0 hi0).trans (Finset.card_le_card (small i0))
  rw [Finset.card_erase_of_mem hi0] at s0
  have big : r+1 ≤ S.card := by dsimp [r];omega
  have nV:=Finset.card_le_card sub
  have pairs:=countEdges D S r deg
  have mul:=Nat.mul_le_mul_right r big
  have choose:=twiceChoose r
  have total:=diagSplit D
  refine ⟨by omega,?_⟩;intro eq
  have card : S.card=r+1 := by omega
  refine ⟨S,sub,card,?_⟩
  intro i hi j hj diff
  have lo:=deg i hi
  have sz : (S.erase i).card=r := by rw [Finset.card_erase_of_mem hi,card];omega
  have eql : neighbors D S i=S.erase i := Finset.eq_of_subset_of_card_le (small i) (sz ▸ lo)
  have mem : j∈neighbors D S i := eql.symm ▸ (Finset.mem_erase.mpr ⟨diff.symm,hj⟩)
  exact (Finset.mem_filter.mp mem).2
end PEqualNP.Outside.L_lib_1673_aux

namespace PEqualNP.Outside.L_lib_1673_aux
open scoped Classical
def upper (S : Finset (Fin n)) := (S ×ˢ S).filter (fun z => z.1<z.2)
def steer (D : Finset (Fin n × Fin n)) (z : Fin n × Fin n) := if z∈D then z else z.swap
def skeleton (D : Finset (Fin n × Fin n)) (S : Finset (Fin n)) := S.diag ∪ (upper S).image (steer D)
def Shape (D : Finset (Fin n × Fin n)) (S : Finset (Fin n)) :=
  (∀i,(i,i)∈D ↔ i∈S) ∧ (∀e∈D,e.1∈S ∧ e.2∈S) ∧ ∀i∈S,∀j∈S,i≠j → ((i,j)∈D ↔ (j,i)∉D)
theorem upperSpec {S : Finset (Fin n)} {a b : Fin n} : (a,b)∈upper S ↔ a∈S ∧ b∈S ∧ a < b := by simp [upper,and_assoc]
theorem steerSpec (D : Finset (Fin n × Fin n)) {a b i j : Fin n} :
    steer D (a,b)=(i,j) ↔ ((a,b)∈D ∧ a=i ∧ b=j) ∨ ((a,b)∉D ∧ b=i ∧ a=j) := by by_cases h:(a,b)∈D <;> simp [steer,h,Prod.ext_iff]
theorem skeletonMem (D : Finset (Fin n × Fin n)) (S : Finset (Fin n)) (i j : Fin n) :
    (i,j)∈skeleton D S ↔ (i∈S ∧ i=j) ∨ (i∈S ∧ j∈S ∧ ((i < j ∧ (i,j)∈D) ∨ (j < i ∧ (j,i)∉D))) := by
  simp only [skeleton,Finset.mem_union,Finset.mem_diag,Finset.mem_image,Prod.exists,upperSpec,steerSpec]
  grind
theorem skeletonShape (D : Finset (Fin n × Fin n)) (S : Finset (Fin n)) : Shape (skeleton D S) S := by
  refine ⟨fun i => by simp [skeletonMem],?_,?_⟩
  · rintro ⟨i,j⟩ e;have h:=(skeletonMem ..).mp e;grind
  · intro i hi j hj ne;rw [skeletonMem,skeletonMem];rcases lt_or_gt_of_ne ne with lt|lt <;> simp [hi,hj,ne,ne.symm,lt,not_lt_of_gt lt]
theorem skeletonCard (D : Finset (Fin n × Fin n)) (S : Finset (Fin n)) : (skeleton D S).card=S.card+S.card.choose 2 := by
  have dis : Disjoint S.diag ((upper S).image (steer D)) := by
    apply Finset.disjoint_left.mpr;rintro ⟨i,j⟩ dm im
    obtain ⟨_,eq⟩:=Finset.mem_diag.mp dm
    obtain ⟨⟨a,b⟩,h,st⟩:=Finset.mem_image.mp im
    have ab:=(upperSpec.mp h).2.2;have h':=(steerSpec D).mp st;grind
  have inj : Set.InjOn (steer D) (upper S) := by
    rintro ⟨a,b⟩ h ⟨c,d⟩ h' eq
    have ab:=(upperSpec.mp h).2.2;have cd:=(upperSpec.mp h').2.2
    by_cases x:(a,b)∈D <;> by_cases y:(c,d)∈D <;> simp [steer,x,y,Prod.ext_iff] at eq ⊢ <;> grind
  rw [skeleton,Finset.card_union_of_disjoint dis,Finset.diag_card,Finset.card_image_of_injOn inj,upper,Finset.card_product_filter_lt]
theorem skeletonSub {D : Finset (Fin n × Fin n)} {S : Finset (Fin n)} (sub:S⊆vertices D)
    (clique : ∀i∈S,∀j∈S,i≠j → Adj D i j) : skeleton D S⊆D := by
  rintro ⟨i,j⟩ h;rcases (skeletonMem ..).mp h with ⟨hi,eq⟩|⟨hi,hj,⟨_,ins⟩|⟨lt,rev⟩⟩
  · subst j;exact (Finset.mem_filter.mp (sub hi)).2
  · exact ins
  · exact (clique i hi j hj (ne_of_gt lt)).2.resolve_right rev
theorem shapeEq {D : Finset (Fin n × Fin n)} {S : Finset (Fin n)} (sh : Shape D S) : D=skeleton D S := by
  ext ⟨i,j⟩;rw [skeletonMem];obtain ⟨dg,ends,one⟩:=sh
  by_cases eq:i=j
  · subst j;simp [dg]
  · by_cases hi:i∈S <;> by_cases hj:j∈S
    · have f:=one i hi j hj eq;have r:=one j hj i hi (Ne.symm eq)
      rcases lt_or_gt_of_ne eq with lt|lt <;> simp [hi,hj,eq,lt,not_lt_of_gt lt] <;> tauto
    all_goals have out : (i,j)∉D := by intro h;have p:=ends _ h;tauto
              simp_all
end PEqualNP.Outside.L_lib_1673_aux

namespace PEqualNP.Outside.L_lib_1673_aux
open scoped Classical
theorem paletteSpec (D : Finset (Cell n n)) (α : Type) :
    Palette α D (vertices D) ↔ ∃c : Fin n → α,Valid D c := by
  constructor
  · rintro ⟨c,h⟩;refine ⟨c,?_⟩;intro i j di dj ne edge
    exact h i (by simpa [vertices] using di) j (by simpa [vertices] using dj) ⟨ne,edge⟩
  · rintro ⟨c,h⟩;refine ⟨c,?_⟩;intro i di j dj edge
    exact h i j (by simpa [vertices] using di) (by simpa [vertices] using dj) edge.1 edge.2
theorem shapeBad [Fintype α] {D : Finset (Cell n n)} {S : Bits n} (sh : Shape D S) (big : Fintype.card α<S.card) :
    ¬Palette α D (vertices D) := by
  rintro ⟨c,ok⟩
  have inj : Function.Injective (fun i : ↥S => c i.val) := by
    intro i j eq;apply Subtype.ext;by_contra diff
    have f:=sh.2.2 i.val i.property j.val j.property diff
    have edge : Adj D i.val j.val := ⟨diff,by by_cases h:(j.val,i.val)∈D;exact Or.inr h;exact Or.inl (f.mpr h)⟩
    have mem (i : ↥S) : i.val∈vertices D := by simp [vertices,(sh.1 _).mpr i.property]
    exact ok _ (mem i) _ (mem j) edge eq
  have h:=Fintype.card_le_of_injective _ inj;simp at h;omega
theorem samples (α : Type) [Fintype α] [Nonempty α] (r : Nat) (rc : Fintype.card α=r) (hn : r+1 ≤ n) :
    (∃D : Finset (Cell n n),¬Palette α D (vertices D) ∧ D.card=r+1+(r+1).choose 2) ∧
    (∀D : Finset (Cell n n),¬Palette α D (vertices D) → r+1+(r+1).choose 2 ≤ D.card) ∧
    ∀D : Finset (Cell n n),(¬Palette α D (vertices D) ∧ D.card=r+1+(r+1).choose 2) ↔ ∃S : Bits n,S.card=r+1 ∧ Shape D S := by
  classical
  obtain ⟨S,_,sz⟩:=Finset.exists_subset_card_eq (s:=(Finset.univ : Bits n)) (n:=r+1) (by simpa using hn)
  have make {D : Finset (Cell n n)} {V : Bits n} (v : V.card=r+1) (shape : Shape D V) :
      ¬Palette α D (vertices D) ∧ D.card=r+1+(r+1).choose 2 := by
    refine ⟨shapeBad shape (by omega),?_⟩
    calc
      D.card=(skeleton D V).card := congrArg Finset.card (shapeEq shape)
      _ = _ := by rw [skeletonCard,v]
  refine ⟨⟨_,make sz (skeletonShape ∅ S)⟩,fun D bad => by simpa [rc] using (lower bad).1,?_⟩
  intro D;constructor
  · rintro ⟨bad,size⟩
    obtain ⟨V,sub,v,cl⟩:=(lower bad).2 (by simpa [rc] using size)
    rw [rc] at v
    have same : skeleton D V=D := Finset.eq_of_subset_of_card_le (skeletonSub sub cl) (by rw [skeletonCard,v,size])
    exact ⟨V,v,same ▸ skeletonShape D V⟩
  · rintro ⟨V,v,shape⟩;exact make v shape
end PEqualNP.Outside.L_lib_1673_aux

open PEqualNP.Outside.L_lib_1673_aux in
theorem PEqualNP.Outside.L_lib_1673 : (
  let layer := fun (m n k : Nat) (P Z : Finset (Fin m × Fin n)) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (p q : Nat),
      0 < q ∧ q ≤ k ∧ p+q ≤ C.size ∧
      m+n+p ≤ C.output ∧ C.output < m+n+C.size ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (m+n) C ∧
      (∀ j < C.size,
        let g := PEqualNP.MetaComplexity.NestedCover.gateAt C j
        g.inputs.length = 2 ∧
        (if j < p then g.op = PEqualNP.CircuitLowerBounds.GateOp.or
         else if j < p+q then g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
           ∀ w ∈ g.inputs, w < m+n+p
         else g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
           ∀ w ∈ g.inputs, m+n+p ≤ w)) ∧
      (∀ e ∈ P, C.eval (PEqualNP.Represents.oneEach e.1 e.2) = true) ∧
      ∀ e ∈ Z, C.eval (PEqualNP.Represents.oneEach e.1 e.2) = false
  ∀ (n k : Nat), 2 ≤ n → 0 < k →
    let fit := fun D : Finset (Fin n × Fin n) =>
      layer n n k (D.filter (fun e => e.1 ≠ e.2)) (D.filter (fun e => e.1 = e.2))
    let h := 2^k+1
    let b := h + Nat.choose h 2
    (∀ D, fit D ↔ ∃ bits : Fin n → (Fin k → Bool),
      ∀ i j, (i,i) ∈ D → (j,j) ∈ D → i ≠ j →
        (i,j) ∈ D ∨ (j,i) ∈ D → bits i ≠ bits j) ∧
    (h ≤ n →
      (∃ D, ¬ fit D ∧ D.card = b) ∧ (∀ D, ¬ fit D → b ≤ D.card) ∧
      ∀ D, (¬ fit D ∧ D.card = b) ↔
        ∃ S : Finset (Fin n), S.card = h ∧
          (∀ i, (i,i) ∈ D ↔ i ∈ S) ∧ (∀ e ∈ D, e.1 ∈ S ∧ e.2 ∈ S) ∧
          ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ((i,j) ∈ D ↔ (j,i) ∉ D))
) := by
  intro layer n k hn hk fit h b
  let α:=Fin k → Bool
  have rc : Fintype.card α=2^k := by simp [α]
  have bridge (D : Finset (Cell n n)) : fit D ↔ Palette α D (vertices D) := (signature hn hk).trans (paletteSpec D α).symm
  refine ⟨fun D => signature hn hk,?_⟩
  intro cap
  simpa only [←bridge,Shape,h,b] using samples α (2^k) rc cap
