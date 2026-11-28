import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1612_aux
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
end PEqualNP.Outside.L_lib_1612_aux
namespace PEqualNP.Outside.L_lib_1612_aux
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
end PEqualNP.Outside.L_lib_1612_aux
namespace PEqualNP.Outside.L_lib_1612_aux
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
end PEqualNP.Outside.L_lib_1612_aux

namespace PEqualNP.Outside.L_lib_1612_aux
open scoped Classical
theorem orient {A B : Bits (n+n)} {G : SimpleGraph (Fin n)} {i : Fin n} (edge : ∃j,G.Adj i j)
    (off : ∀i j,G.Adj i j → ¬Both A B (i,j)) (on : Both A B (i,i)) :
    (left n i∈A ∧ right n i∈B) ∨ (left n i∈B ∧ right n i∈A) := by
  obtain ⟨j,h⟩:=edge
  have a:=off _ _ h;have b:=off _ _ h.symm
  simp only [Both,On] at on a b;tauto
theorem colorBound {G : SimpleGraph (Fin n)} (near : ∀i,∃j,G.Adj i j)
    (A B : Fin q → Bits (n+n)) (live : Finset (Fin q)) (cover : ∀i,∃t∈live,Both (A t) (B t) (i,i))
    (conflict : ∀t∈live,∀i j,G.Adj i j → ¬Both (A t) (B t) (i,j)) {W : Bits (n+n)}
    (dep : ∀t∈live,A t∪B t⊆W) (limit : W.card ≤ s+1) (budget : q≤k) :
    2*n ≤ s+1 ∧ ∃color : Fin n → Fin (2*k),∀i j,G.Adj i j → color i≠color j := by
  classical
  choose owner held yes using cover
  have orientation i:=orient (near i) (conflict _ (held i)) (yes i)
  let side (i : Fin n) := left n i∈A (owner i) ∧ right n i∈B (owner i)
  let color (i : Fin n) : Fin (2*k) := ⟨2*(owner i).val+(if side i then 0 else 1),by have h:=(owner i).isLt;split <;> omega⟩
  have all : W=Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x;rcases allNames x with ⟨i,rfl⟩|⟨i,rfl⟩
    · apply dep _ (held i);rw [Finset.mem_union];rcases orientation i with h|h
      · exact Or.inl h.1
      · exact Or.inr h.1
    · apply dep _ (held i);rw [Finset.mem_union];rcases orientation i with h|h
      · exact Or.inr h.2
      · exact Or.inl h.2
  rw [all,Finset.card_univ,Fintype.card_fin] at limit
  refine ⟨by omega,color,?_⟩
  intro i j adj eq
  have num:=congrArg Fin.val eq
  change 2*(owner i).val+(if side i then 0 else 1)=2*(owner j).val+(if side j then 0 else 1) at num
  have own : owner i=owner j := by apply Fin.ext;split at num <;> split at num <;> omega
  have bad:=conflict (owner i) (held i) i j adj;apply bad
  by_cases si : side i
  · have sj : side j := by by_contra nj;rw [if_pos si,if_neg nj,own] at num;omega
    exact ⟨Or.inl si.1,Or.inr (own ▸ sj.2)⟩
  · have sj : ¬side j := by intro sj;rw [if_neg si,if_pos sj,own] at num;omega
    have xi:=(orientation i).resolve_left si;have xj:=(orientation j).resolve_left sj
    exact ⟨Or.inr (own ▸ xj.2),Or.inl xi.1⟩
end PEqualNP.Outside.L_lib_1612_aux

namespace PEqualNP.Outside.L_lib_1612_aux
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
end PEqualNP.Outside.L_lib_1612_aux

namespace PEqualNP.Outside.L_lib_1612_aux
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
theorem depCost (t : Nat) (C : Circuit) (i : Nat) : (deps t C i).card≤C.size+1 := by
  let available (I : Bank t) (ws : List (Bits t)) := ∅∈I ∧ ∀a∈ws,a∈I
  have get {I : Bank t} {ws} (h : available I ws) (j : Nat) : ws.getD j ∅∈I := by
    by_cases hj:j<ws.length
    · simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj] using h.2 _ (List.getElem_mem hj)
    · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : ws.length≤j),h.1]
  have go (gs : List Gate) (ws : List (Bits t)) (I : Bank t) (h : available I ws) :
      ∃B,Chain I gs.length B ∧ available B (run unionOp ws gs) := by
    induction gs generalizing ws I with
    | nil => exact ⟨I,.start,h⟩
    | cons g gs ih =>
      let new:=unionOp ws g
      let J:=insert new I
      have cc : Chain I 1 J := .step .start (get h _) (get h _)
      have acc : available J (extend unionOp ws g) := by
        refine ⟨Finset.mem_insert_of_mem h.1,?_⟩
        intro a ha;rcases List.mem_append.mp ha with old|last
        · exact Finset.mem_insert_of_mem (h.2 _ old)
        · have e : a=new := List.mem_singleton.mp last;exact e ▸ Finset.mem_insert_self ..
      obtain ⟨B,ch,ok⟩:=ih _ _ acc;refine ⟨B,?_,ok⟩;simpa [Nat.add_comm] using splice cc ch
  have init : available (seed t) (rawList t) := by
    refine ⟨by simp [seed],?_⟩;intro a h;obtain ⟨j,rfl⟩:=List.mem_ofFn.mp h;exact rawMem j
  obtain ⟨B,ch,h⟩:=go C.gates _ _ init
  have inB : deps t C i∈B := get h i
  by_cases ne:(deps t C i).Nonempty
  · obtain ⟨P,_,cap,all⟩:=forest ch;obtain ⟨Z,z,sub⟩:=all _ inB ne
    have v : Z.card-1≤credit P := Finset.single_le_sum (f:=fun A : Bits t => A.card-1) (fun _ _ => Nat.zero_le _) z
    have c:=Finset.card_le_card sub;change _≤C.gates.length+1;omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp ne]
def probe (e : Cell m n) (i : Fin (m+n)) := decide (i=left n e.1 ∨ i=right m e.2)
theorem probeInput (e : Cell m n) : List.ofFn (probe e)=PEqualNP.Represents.oneEach e.1 e.2 := by
  unfold PEqualNP.Represents.oneEach;rw [List.ofFn_add]
  congr 1
  · apply congrArg List.ofFn;funext i;change decide (left n i=left n e.1 ∨ left n i=right m e.2)=_
    simp [(leftInj m n).eq_iff,separate]
  · apply congrArg List.ofFn;funext j;change decide (right m j=left n e.1 ∨ right m j=right m e.2)=_
    simp [(rightInj m n).eq_iff,(separate e.1 j).symm]
end PEqualNP.Outside.L_lib_1612_aux

namespace PEqualNP.Outside.L_lib_1612_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
def gatesOK (raw p q : Nat) (C : Circuit) := ∀j<C.size,
  let g:=gateAt C j
  g.inputs.length=2 ∧ (if j<p then g.op=.or else if j<p+q then g.op=.and ∧ ∀i∈g.inputs,i<raw+p
  else g.op=.or ∧ ∀i∈g.inputs,raw+p ≤ i)
def Fits (G : SimpleGraph (Fin n)) (k s : Nat) := ∃(C : Circuit) (p q : Nat),0<q ∧ q ≤ k ∧ p+q ≤ C.size ∧ C.size  ≤  s ∧
  n+n+p ≤ C.output ∧ C.output<n+n+C.size ∧ ReadsBack (n+n) C ∧ gatesOK (n+n) p q C ∧
  (∀i : Fin n,C.eval (PEqualNP.Represents.oneEach i i)=true) ∧ ∀i j,G.Adj i j → C.eval (PEqualNP.Represents.oneEach i j)=false
def val (C : Circuit) (e : Cell n n) (j : Nat) := worth C (List.ofFn (probe e)) j
theorem valueGate (C : Circuit) (e : Cell n n) (back : ReadsBack (n+n) C) {j} (hj : j<C.size) {a b} (pp : (gateAt C j).inputs=[a,b]) :
    val C e (n+n+j)=(gateAt C j).op.eval [val C e a,val C e b] := by
  have hh : ReadsBack (List.ofFn (probe e)).length C := by simpa using back
  simpa only [List.length_ofFn,val] using worthGate C (List.ofFn (probe e)) hh hj pp
theorem prefixValue (C : Circuit) (back : ReadsBack (n+n) C) (ok : gatesOK (n+n) p q C) (first : p ≤ C.size) (e : Cell n n) :
    ∀i,i<n+n+p → (val C e i=true ↔ On (deps (n+n) C i) e) := by
  intro i;induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro small
    by_cases raw:i<n+n
    · let u : Fin (n+n) := ⟨i,raw⟩
      have a:=rawDep (n+n) C u
      have b:=worthInput C (List.ofFn (probe e)) (i:=i) (by simp [raw])
      change deps (n+n) C i={u} at a
      unfold val;rw [a,b];have get : (List.ofFn (probe e)).getD i false=probe e u := by simp [List.getD_eq_getElem?_getD,raw,u]
      rw [get];simp only [probe,decide_eq_true_eq,On,Finset.mem_singleton];grind
    · let j:=i-(n+n)
      have eq : n+n+j=i := by dsimp [j];omega
      have early : j<p := by omega
      have hj : j<C.size := by omega
      obtain ⟨sz,typ⟩:=ok j hj
      have op : (gateAt C j).op=.or := by simpa [early] using typ
      obtain ⟨a,b,parents⟩:=pairInputs sz
      have ha:=back j hj a (by simp [parents]);have hb:=back j hj b (by simp [parents])
      have av:=ih a (by omega) (by omega);have bv:=ih b (by omega) (by omega)
      rw [←eq,gateDep _ _ back hj parents,valueGate C e back hj parents,op]
      simp only [GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false,Bool.or_eq_true,av,bv,On,Finset.mem_union];tauto
end PEqualNP.Outside.L_lib_1612_aux

namespace PEqualNP.Outside.L_lib_1612_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
theorem necessary {G : SimpleGraph (Fin n)} (near : ∀i,∃j,G.Adj i j) (fits : Fits G k s) :
    2*n  ≤  s+1 ∧ ∃color : Fin n → Fin (2*k),∀i j,G.Adj i j → color i≠color j := by
  classical
  obtain ⟨C,p,q,_,qk,layers,cost,outlo,outhi,back,ok,diagonal,forbidden⟩:=fits
  let N:=n+n
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
  have prod (t) (e : Cell n n) : val C e (root t)=true ↔ Both (A t) (B t) e := by
    have pa:=(info t).2 (a t) (by simp [parents]);have pb:=(info t).2 (b t) (by simp [parents])
    have first : p ≤ C.size := by omega
    have x:=prefixValue C back ok first e (a t) pa;have y:=prefixValue C back ok first e (b t) pb
    dsimp only [root,N];rw [valueGate C e back (mid t) (parents t),(info t).1]
    simpa [GateOp.eval,Both,A,B] using and_congr x y
  have dp t : deps N C (root t)=A t∪B t := gateDep N C back (mid t) (parents t)
  let reaches (i : Nat) (t : Fin q) := deps N C (root t)⊆deps N C i ∧
    ∀e : Cell n n,val C e (root t)=true → val C e i=true
  have trace (i) : N+p ≤ i → i<N+C.size → ∀e : Cell n n,val C e i=true → ∃t,reaches i t ∧ val C e (root t)=true := by
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
        have vg (z : Cell n n) : val C z i=true ↔ val C z u=true ∨ val C z v=true := by
          rw [←eq,valueGate C z back jj pair,typ.1];simp [GateOp.eval]
        have walk (w : Nat) (mem : w∈(gateAt C j).inputs) (dz : deps N C w⊆deps N C i)
            (vz : ∀z : Cell n n,val C z w=true → val C z i=true) (hit : val C e w=true) :
            ∃t,reaches i t ∧ val C e (root t)=true := by
          have less : w < i := eq ▸ back j jj w mem
          obtain ⟨t,⟨ds,vs⟩,yes⟩:=ih w less (typ.2 _ mem) (by omega) e hit
          exact ⟨t,⟨ds.trans dz,fun z h => vz z (vs z h)⟩,yes⟩
        rcases (vg e).mp on with uOn|vOn
        · exact walk u (by simp [pair]) (by rw [dg];exact Finset.subset_union_left) (fun z h => (vg z).mpr (Or.inl h)) uOn
        · exact walk v (by simp [pair]) (by rw [dg];exact Finset.subset_union_right) (fun z h => (vg z).mpr (Or.inr h)) vOn
  let live:=Finset.univ.filter (reaches C.output)
  have evalEq (e : Cell n n) : val C e C.output=C.eval (PEqualNP.Represents.oneEach e.1 e.2) := by unfold val;rw [probeInput];rfl
  apply colorBound near A B live (W:=deps N C C.output) (budget:=qk)
  · intro i;have on : val C (i,i) C.output=true := (evalEq _).trans (diagonal i)
    obtain ⟨t,reach,yes⟩:=trace _ outlo outhi _ on
    exact ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,reach⟩,(prod t _).mp yes⟩
  · intro t lt i j adj both
    have reach : reaches C.output t := (Finset.mem_filter.mp lt).2
    have on:=reach.2 (i,j) ((prod t _).mpr both)
    rw [evalEq,forbidden i j adj] at on;contradiction
  · intro t lt;rw [←dp];exact (Finset.mem_filter.mp lt).2.1
  · exact (depCost N C C.output).trans (by omega)
end PEqualNP.Outside.L_lib_1612_aux

namespace PEqualNP.Outside.L_lib_1612_aux
open scoped Classical
theorem splitColors {G : SimpleGraph (Fin n)} (hn : 0<n) (c : Fin n → Fin (2*k)) (good : ∀i j,G.Adj i j → c i≠c j) :
    ∃q,0<q ∧ q≤k ∧ ∃A B : Fin q → Bits (n+n),
      (∀j,(A j).Nonempty ∧ (B j).Nonempty) ∧ (∑j,((A j).card+(B j).card))=2*n ∧
      (∀i,∃j,Both (A j) (B j) (i,i)) ∧ ∀i j,G.Adj i j → ∀t,¬Both (A t) (B t) (i,j) := by
  classical
  let group (i : Fin n) : Fin k := ⟨(c i).val/2,by have h:=(c i).isLt;omega⟩
  let turn (i : Fin n) := decide ((c i).val % 2=0)
  let used:=Finset.univ.image group
  let tag (i : Fin n) : ↥used := ⟨group i,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  let e : ↥used ≃ Fin used.card := Fintype.equivFinOfCardEq (by simp)
  let idx (i : Fin n) := e (tag i)
  have onto (j : Fin used.card) : ∃i,idx i=j := by
    obtain ⟨v,rfl⟩:=e.surjective j;obtain ⟨i,_,hi⟩:=Finset.mem_image.mp v.property
    exact ⟨i,congrArg e (Subtype.ext hi)⟩
  let fiber (j : Fin used.card) := Finset.univ.filter (fun i => idx i=j)
  let L (j : Fin used.card) := (fiber j).filter (fun i => turn i=true)
  let R (j : Fin used.card) := (fiber j).filter (fun i => ¬turn i=true)
  let A j := pack (L j) (R j)
  let B j := pack (R j) (L j)
  have card j : (A j).card+(B j).card=2*(fiber j).card := by
    have h:=Finset.card_filter_add_card_filter_not (s:=fiber j) (p:=fun i => turn i=true)
    change (L j).card+(R j).card=(fiber j).card at h;dsimp only [A,B];rw [packCard,packCard];omega
  have cl i j : i∈L j ↔ idx i=j ∧ turn i=true := by simp [L,fiber]
  have cr i j : i∈R j ↔ idx i=j ∧ turn i=false := by simp [R,fiber]
  have yes i : Both (A (idx i)) (B (idx i)) (i,i) := by
    cases v:turn i <;> simp [Both,On,A,B,inLeft,inRight,cl,cr,v]
  have someName {V : Bits (n+n)} {i : Fin n} (on : On V (i,i)) : V.Nonempty := on.elim (fun h => ⟨_,h⟩) (fun h => ⟨_,h⟩)
  have ua : used.Nonempty := ⟨_,(tag ⟨0,hn⟩).property⟩
  refine ⟨used.card,Finset.card_pos.mpr ua,by simpa using Finset.card_le_card (Finset.subset_univ used),A,B,?_,?_,fun i => ⟨_,yes i⟩,?_⟩
  · intro j;obtain ⟨i,rfl⟩:=onto j;exact ⟨someName (yes i).1,someName (yes i).2⟩
  · have z : (∑j,(fiber j).card)=n := by
      simpa [fiber] using Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin n)) (Finset.univ : Finset (Fin used.card)) idx
    simp only [card,←Finset.mul_sum,z]
  · intro i j adj t on
    simp only [Both,On,A,B,inLeft,inRight,cl,cr] at on
    have eq : idx i=idx j ∧ turn i=turn j := by cases a:turn i <;> cases b:turn j <;> simp_all
    have g : group i=group j := congrArg Subtype.val (e.injective eq.1)
    have div : (c i).val/2=(c j).val/2 := congrArg Fin.val g
    have par : ((c i).val % 2=0) ↔ ((c j).val % 2=0) := by simpa [turn] using congrArg (fun z : Bool => z=true) eq.2 |>.to_iff
    exact good i j adj (Fin.ext (by omega))
end PEqualNP.Outside.L_lib_1612_aux

namespace PEqualNP.Outside.L_lib_1612_aux
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
end PEqualNP.Outside.L_lib_1612_aux

namespace PEqualNP.Outside.L_lib_1612_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
theorem bankPrefix (A B : Fin q → Bits (n+n)) (ne : ∀j,(A j).Nonempty ∧ (B j).Nonempty)
    (count : (∑j,((A j).card+(B j).card))=2*n) :
    ∃gs : List Gate,Good (n+n) gs ∧ gs.length+2*q ≤ 2*n ∧ ∀j,Seen gs (A j) ∧ Seen gs (B j) := by
  let price j := ((A j).card-1)+((B j).card-1)
  have job (j : Fin q) : ∃r≤price j,∃I,Chain (seed (n+n)) r I ∧ A j∈I ∧ B j∈I := by
    obtain ⟨V,cv,a⟩:=rawGroup Finset.Subset.rfl (A j) (ne j).1
    obtain ⟨I,ci,b⟩:=rawGroup (grow cv) (B j) (ne j).2
    exact ⟨_,le_rfl,I,splice cv ci,grow ci a,b⟩
  obtain ⟨r,bill,I,ch,all⟩:=batch (seed (n+n)) price (fun j V => A j∈V ∧ B j∈V) (fun _ {_ _} sub h => ⟨sub h.1,sub h.2⟩) job
  obtain ⟨gs,cap,good,seen⟩:=emit ch
  have localEq j : price j+2=(A j).card+(B j).card := by
    have ha:=Finset.card_pos.mpr (ne j).1;have hb:=Finset.card_pos.mpr (ne j).2;dsimp [price];omega
  have total:=Finset.sum_congr (rfl : (Finset.univ : Finset (Fin q))=Finset.univ) (fun j _ => localEq j)
  rw [Finset.sum_add_distrib,count] at total;simp at total
  exact ⟨gs,good,by omega,fun j => ⟨seen _ (all j).1 (ne j).1,seen _ (all j).2 (ne j).2⟩⟩
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
end PEqualNP.Outside.L_lib_1612_aux

namespace PEqualNP.Outside.L_lib_1612_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
theorem probeOn (e : Cell m n) (A : Bits (m+n)) : sample (probe e) A=true ↔ On A e := by
  simp only [sample,probe,decide_eq_true_eq,On];grind
theorem prefixRead (gs : List Gate) (u v : Fin q → Nat) (e : Cell n n) {j} (hj : j<n+n+gs.length) :
    val (program (n+n) gs u v) e j=(testRun gs (probe e)).getD j false := by
  change (run opEval (List.ofFn (probe e)) ((gs++middle u v)++suffix _ q)).getD j false=_
  rw [List.append_assoc,appendRun,kept _ _ _ _ (by rw [runLength,List.length_ofFn];exact hj)]
  rfl
theorem programEval (gs : List Gate) (u v : Fin q → Nat) (hq : 0<q) (A B : Fin q → Bits (n+n))
    (back : ReadsBack (n+n) (program (n+n) gs u v))
    (bounds : ∀j,u j<n+n+gs.length ∧ v j<n+n+gs.length)
    (eu : ∀j x,(testRun gs x).getD (u j) false=sample x (A j))
    (ev : ∀j x,(testRun gs x).getD (v j) false=sample x (B j)) :
    let C:=program (n+n) gs u v
    ∀e : Cell n n,val C e C.output=true ↔ ∃j,Both (A j) (B j) e := by
  let N:=n+n
  let base:=N+gs.length
  let C:=program N gs u v
  intro C' e
  have prod (j : Fin q) : val C e (base+j.val)=true ↔ Both (A j) (B j) e := by
    have h : gs.length+j.val<C.size := by change _<(program N gs u v).size;rw [sizeProgram];omega
    have gate:=midGate N gs u v j
    have par : (gateAt C (gs.length+j.val)).inputs=[u j,v j] := congrArg Gate.inputs gate
    rw [show base+j.val=n+n+(gs.length+j.val) by dsimp [base,N];omega,valueGate C e back h par,gate]
    change (GateOp.and.eval [val (program (n+n) gs u v) e (u j),val (program (n+n) gs u v) e (v j)]=true) ↔ _
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
      rw [show acc base q (i+1)=n+n+(gs.length+q+i) by simp [acc,base,N];omega,valueGate C e back h par,op]
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
theorem sufficient {G : SimpleGraph (Fin n)} (hn : 0<n) (size : 2*n ≤ s+1)
    (c : Fin n → Fin (2*k)) (good : ∀i j,G.Adj i j → c i≠c j) : Fits G k s := by
  classical
  obtain ⟨q,hq,qk,A,B,ne,count,diag,forbid⟩:=splitColors hn c good
  obtain ⟨gs,pre,budget,seen⟩:=bankPrefix A B ne count
  choose u hu eu using fun j => (seen j).1
  choose v hv ev using fun j => (seen j).2
  let C:=program (n+n) gs u v
  have bounds j:=And.intro (hu j) (hv j)
  obtain ⟨back,ok⟩:=programLegal (n+n) gs u v hq pre bounds
  have eval:=programEval gs u v hq A B back bounds eu ev
  have sz : C.size=gs.length+q+(q-1) := sizeProgram _ _ _ _
  have ob:=accBounds (n+n+gs.length) q (q-1) hq
  have bridge (e : Cell n n) : val C e C.output=C.eval (PEqualNP.Represents.oneEach e.1 e.2) := by unfold val;rw [probeInput];rfl
  refine ⟨C,gs.length,q,hq,qk,by omega,by omega,ob.1,?_,back,ok,?_,?_⟩
  · change acc _ _ _ < _;omega
  · intro i;rw [←bridge (i,i)];exact (eval _).mpr (diag i)
  · intro i j adj;rw [←bridge (i,j)];apply Bool.eq_false_iff.mpr
    intro on;obtain ⟨t,hit⟩:=(eval _).mp on;exact forbid i j adj t hit
end PEqualNP.Outside.L_lib_1612_aux

open PEqualNP.Outside.L_lib_1612_aux in
theorem PEqualNP.Outside.L_lib_1612 : (
  let fits := fun {n : Nat} (G : SimpleGraph (Fin n)) (k s : Nat) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (p q : Nat),
      0 < q ∧ q ≤ k ∧ p+q ≤ C.size ∧ C.size ≤ s ∧
      n+n+p ≤ C.output ∧ C.output < n+n+C.size ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+n) C ∧
      (∀ j < C.size,
        let g := PEqualNP.MetaComplexity.NestedCover.gateAt C j
        g.inputs.length = 2 ∧
        (if j < p then g.op = PEqualNP.CircuitLowerBounds.GateOp.or
         else if j < p+q then g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
           ∀ w ∈ g.inputs, w < n+n+p
         else g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
           ∀ w ∈ g.inputs, n+n+p ≤ w)) ∧
      (∀ i : Fin n, C.eval (PEqualNP.Represents.oneEach i i) = true) ∧
      ∀ i j : Fin n, G.Adj i j → C.eval (PEqualNP.Represents.oneEach i j) = false
  ∀ (n : Nat) (G : SimpleGraph (Fin n)), 0 < n → (∀ i, ∃ j, G.Adj i j) →
    ∀ k s : Nat, fits G k s ↔
      2*n ≤ s+1 ∧ ∃ color : Fin n → Fin (2*k), ∀ i j, G.Adj i j → color i ≠ color j
) := by
  intro fits n G hn near k s
  change Fits G k s ↔ _
  exact ⟨necessary near,fun ⟨size,c,h⟩ => sufficient hn size c h⟩
