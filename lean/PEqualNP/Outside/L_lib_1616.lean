import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1616_aux
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
end PEqualNP.Outside.L_lib_1616_aux
namespace PEqualNP.Outside.L_lib_1616_aux
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
end PEqualNP.Outside.L_lib_1616_aux
namespace PEqualNP.Outside.L_lib_1616_aux
open scoped Classical
end PEqualNP.Outside.L_lib_1616_aux
namespace PEqualNP.Outside.L_lib_1616_aux
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
end PEqualNP.Outside.L_lib_1616_aux
namespace PEqualNP.Outside.L_lib_1616_aux
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
end PEqualNP.Outside.L_lib_1616_aux

namespace PEqualNP.Outside.L_lib_1616_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped Classical
def feeds (x y : Fin t → Bool) (W : Bits t) := ∀a∈W,x a=true → y a=true
def faithful (x y : Fin t → Bool) (S : List (Bits t)) (X Y : List Bool) :=
  ∀j,feeds x y (S.getD j ∅) → X.getD j false=true → Y.getD j false=true
theorem oldGet (xs : List α) (a d : α) {j} (diff : j≠xs.length) : (xs++[a]).getD j d=xs.getD j d := by
  by_cases lt:j<xs.length
  · exact List.getD_append _ _ _ _ lt
  · have big : xs.length+1 ≤ j := by omega
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (l:=xs) (by omega : xs.length ≤ j),List.getElem?_eq_none (l:=xs++[a]) (by simpa using big)]
theorem gateMono {g : Gate} (mono : g.op∈({GateOp.and,GateOp.or} : Set GateOp)) (X Y : List Bool)
    (resp : ∀i∈g.inputs,X.getD i false=true → Y.getD i false=true) : opEval X g=true → opEval Y g=true := by
  rcases mono with andOp|orOp
  · unfold opEval;rw [andOp];simp only [GateOp.eval,List.all_eq_true,List.mem_map,id_eq]
    intro all z hz;obtain ⟨i,hi,rfl⟩:=hz
    exact resp i hi (all _ ⟨i,hi,rfl⟩)
  · have orOp' : g.op=.or := orOp
    unfold opEval;rw [orOp'];simp only [GateOp.eval,List.any_eq_true,List.mem_map,id_eq]
    rintro ⟨z,⟨i,hi,rfl⟩,on⟩;exact ⟨_,⟨i,hi,rfl⟩,resp i hi on⟩
theorem twoInputs (l : List Nat) (len : l.length ≤ 2) (i : Nat) (h : i∈l) : i=l.getD 0 0 ∨ i=l.getD 1 0 := by
  cases l with
  | nil => simp at h
  | cons a l => cases l with
    | nil => exact Or.inl (List.mem_singleton.mp h)
    | cons b l => cases l with
      | nil => simpa using h
      | cons z l => simp at len
theorem supported (C : Circuit) (mono : Monotone2 C) (x y : Fin t → Bool) :
    ∀j,feeds x y (deps t C j) → worth C (List.ofFn x) j=true → worth C (List.ofFn y) j=true := by
  have start : faithful x y (rawList t) (List.ofFn x) (List.ofFn y) := by
    intro j;by_cases h:j<t
    · let i : Fin t:=⟨j,h⟩
      have u:=rawDep t (⟨[],0⟩ : Circuit) i
      change (rawList t).getD j ∅={i} at u
      simp only [u];intro link;simpa [List.getD_eq_getElem?_getD,h,i] using link i (Finset.mem_singleton_self i)
    · simp [List.getD_eq_getElem?_getD,h]
  have go (gs : List Gate) (S : List (Bits t)) (X Y : List Bool)
      (sz : S.length=X.length) (sy : S.length=Y.length) (inv : faithful x y S X Y)
      (leg : ∀g∈gs,g.op∈({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      faithful x y (run unionOp S gs) (run opEval X gs) (run opEval Y gs) := by
    induction gs generalizing S X Y with
    | nil => exact inv
    | cons g gs ih =>
      have ok:=leg g List.mem_cons_self
      apply ih (extend unionOp S g) (extend opEval X g) (extend opEval Y g) (by simp [extend,sz]) (by simp [extend,sy]) _ (fun z h => leg z (List.mem_cons_of_mem _ h))
      intro j;by_cases eq:j=S.length
      · subst j
        have last {α : Type} (xs : List α) (a d : α) : (xs++[a]).getD xs.length d=a := by rw [List.getD_append_right _ _ _ _ le_rfl,Nat.sub_self];rfl
        unfold extend;rw [last,sz,last,←sz,sy,last];intro feed
        apply gateMono ok.1;intro i h
        have parent:=twoInputs g.inputs ok.2 i h
        apply inv i;intro a ha
        apply feed a;unfold unionOp;rw [Finset.mem_union];rcases parent with hp|hp
        · exact Or.inl (hp ▸ ha)
        · exact Or.inr (hp ▸ ha)
      · unfold extend;rw [oldGet _ _ _ eq,oldGet _ _ _ (by omega : j≠X.length),oldGet _ _ _ (by omega : j≠Y.length)];exact inv j
  exact go C.gates (rawList t) (List.ofFn x) (List.ofFn y) (by simp [rawList]) (by simp [rawList]) start mono
end PEqualNP.Outside.L_lib_1616_aux

namespace PEqualNP.Outside.L_lib_1616_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open scoped Classical
def Legal (w : Nat) (C : Circuit) := Monotone2 C ∧ ReadsBack w C ∧ C.output<w+C.size
def addr (n base pin j : Nat) := if j<n then j else if j=n then pin else base+(j-(n+1))
def mapped (f : Nat → Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map f⟩
def combined (n : Nat) (pre : List Gate) (pin : Nat) (D : Circuit) : Circuit :=
  ⟨pre++D.gates.map (mapped (addr n (n+pre.length) pin)),addr n (n+pre.length) pin D.output⟩
theorem combSize n pre pin D : (combined n pre pin D).size=pre.length+D.size := by simp [combined,Circuit.size]
theorem addrBound {n base pin i j} (baseOK : n ≤ base) (pinOK : pin<base) (less : i<n+1+j) : addr n base pin i<base+j := by
  unfold addr;split_ifs <;> omega
theorem combineLegal {n pre pin D} (ok : Monotone2 ⟨pre,0⟩ ∧ ReadsBack n ⟨pre,0⟩) (hp : pin<n+pre.length) (hd : Legal (n+1) D) :
    Legal n (combined n pre pin D) := by
  let f:=addr n (n+pre.length) pin
  refine ⟨?_,?_,?_⟩
  · intro g mem;rcases List.mem_append.mp mem with h|h
    · exact ok.1 _ h
    · obtain ⟨src,hsrc,rfl⟩:=List.mem_map.mp h;simpa [mapped] using hd.1 src hsrc
  · intro j hj i hi
    have sz : j<pre.length+D.size := by change j<(combined n pre pin D).size at hj;simpa only [combSize] using hj
    by_cases early:j<pre.length
    · change i∈((pre++_).getD j _).inputs at hi
      rw [List.getD_append _ _ _ _ early] at hi;exact ok.2 j early i hi
    · let a:=j-pre.length
      have small : a<D.gates.length := by change a<D.size;dsimp [a];omega
      have gate : gateAt (combined n pre pin D) j=mapped f (gateAt D a) := by
        unfold gateAt;change (pre++D.gates.map (mapped f)).getD j _=_
        rw [List.getD_append_right _ _ _ _ (by omega)];change (D.gates.map _).getD a _=_
        simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem small,small]
      rw [gate] at hi;obtain ⟨u,hu,rfl⟩:=List.mem_map.mp hi
      have less:=addrBound (show n ≤ n+pre.length by omega) hp (hd.2.1 a small u hu)
      change addr n (n+pre.length) pin u<n+j;dsimp [a] at less;omega
  · rw [combSize];exact (addrBound (show n ≤ n+pre.length by omega) hp hd.2.2).trans_le (by omega)
theorem simulate (n base pin : Nat) (nb : n ≤ base) (hp : pin<base) (gs : List Gate)
    (X Y : List Bool) (l : Nat) (sx : X.length=base+l) (sy : Y.length=n+1+l)
    (agree : ∀i,X.getD (addr n base pin i) false=Y.getD i false) :
    ∀i,(run opEval X (gs.map (mapped (addr n base pin)))).getD (addr n base pin i) false=(run opEval Y gs).getD i false := by
  induction gs generalizing l X Y with
  | nil => exact agree
  | cons g gs ih =>
    let f:=addr n base pin
    let new:=mapped f g
    have same : opEval X new=opEval Y g := by simp only [opEval,new,mapped,List.map_map,Function.comp_def,f,agree]
    apply ih (extend opEval X new) (extend opEval Y g) (l+1) (by simp [extend,sx];omega) (by simp [extend,sy];omega)
    intro i;by_cases e:i=Y.length
    · subst i;have shifted : f Y.length=X.length := by dsimp [f,addr];simp [sy,sx];split_ifs <;> omega
      change (X++[_]).getD (f Y.length) false=(Y++[_]).getD Y.length false
      rw [shifted,List.getD_append_right _ _ _ _ le_rfl,List.getD_append_right _ _ _ _ le_rfl];simpa using same
    · have notNew : f i≠X.length := by dsimp [f,addr];split_ifs <;> omega
      unfold extend;rw [oldGet _ _ _ notNew,oldGet _ _ _ e];exact agree i
theorem evaluateCombined (x : List Bool) (hx : x.length=n) (pre : List Gate) (pin : Nat) (hp : pin<n+pre.length) (D : Circuit) :
    (combined n pre pin D).eval x=D.eval (x++[(run opEval x pre).getD pin false]) := by
  let X:=run opEval x pre
  have sz : X.length=n+pre.length := by rw [runLength,hx]
  let f:=addr n (n+pre.length) pin
  have init (i) : X.getD (f i) false=(x++[X.getD pin false]).getD i false := by
    by_cases before:i<n
    · simp only [f,addr,if_pos before];rw [List.getD_append _ _ _ _ (by omega)];exact kept opEval x pre false (by omega)
    by_cases eq:i=n
    · subst i;simp [f,addr,←hx]
    · have lo : x.length+1 ≤ i := by omega
      have high : X.length ≤ f i := by dsimp [f,addr];rw [if_neg before,if_neg eq,sz];omega
      simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_none high];rw [List.getElem?_eq_none (by simp;omega)]
  change (run opEval x (pre++D.gates.map (mapped f))).getD _ false=_
  rw [appendRun];exact simulate n (n+pre.length) pin (by omega) hp D.gates X _ 0 (by simpa using sz) (by simp [hx]) init _
end PEqualNP.Outside.L_lib_1616_aux

namespace PEqualNP.Outside.L_lib_1616_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped Classical
abbrev Input (n : Nat) := Fin n → Bool
def raw (x : Input n) := List.ofFn x++[false,true]
def portInputs (x : Input n) (z : Bool) := raw x++[z]
def input2 (x : Input n) : Input (n+2) := Fin.addCases x ![false,true]
def input3 (x : Input n) (z : Bool) : Input (n+3) := Fin.addCases x ![false,true,z]
theorem inputList (x : Input n) (v : Input d) : List.ofFn (Fin.addCases x v)=List.ofFn x++List.ofFn v := by
  rw [List.ofFn_add];congr 1
  · apply congrArg List.ofFn;funext i;change Fin.addCases (motive:=fun _ => Bool) x v (i.castAdd d)=x i;simp
  · apply congrArg List.ofFn;funext i;simp
theorem list2 (x : Input n) : List.ofFn (input2 x)=raw x := by unfold input2;rw [inputList];rfl
theorem list3 (x : Input n) (z : Bool) : List.ofFn (input3 x z)=portInputs x z := by unfold input3;rw [inputList];simp only [portInputs,raw,List.append_assoc];rfl
def below (x y : Input n) := ∀i,x i=true → y i=true
theorem portMono (P : Circuit) (leg : Monotone2 P) (x y : Input n) (xy : below x y) :
    P.eval (raw x)=true → P.eval (raw y)=true := by
  rw [←list2,←list2];apply supported P leg;intro i _;refine Fin.addCases ?_ ?_ i
  · intro j;simpa [input2] using xy j
  · intro j;simp [input2]
theorem branchMono (D : Circuit) (leg : Monotone2 D) (x y : Input n) (a b : Bool) (xy : below x y) (ab : a=true → b=true) :
    D.eval (portInputs x a)=true → D.eval (portInputs y b)=true := by
  rw [←list3,←list3];apply supported D leg;intro i _;refine Fin.addCases ?_ ?_ i
  · intro j;simpa [input3] using xy j
  · intro j;fin_cases j <;> simpa [input3] using (by first | exact ab | trivial)
noncomputable def alone (i : Fin n) : Input n := fun j => decide (j≠i)
noncomputable def indicator (e : Bits n) : Input n := fun i => decide (i∈e)
noncomputable def productBit (x : Input n) (e : Bits n) := decide (∀ i∈e,x i=true)
noncomputable def desired (E : Bank n) (x : Input n) := decide (∃e∈E,productBit x e=true)
def allOn (x : Input n) := (List.ofFn x).all id
theorem allOnTrue (x : Input n) : allOn x=true ↔ ∀i,x i=true := by simp [allOn,List.all_eq_true]
def one (n : Nat) : Input n:=fun _ => true
theorem badFlip (i : Fin n) : allOn (alone i)=false := by apply Bool.eq_false_iff.mpr;intro h;have zero:=(allOnTrue _).mp h i;simp [alone] at zero
def portIndex (n : Nat) : Fin (n+3) := Fin.natAdd n (2 : Fin 3)
def missing (n : Nat) (A : Circuit) := Finset.univ.filter (fun i : Fin n => i.castAdd 3∉deps (n+3) A A.output)
theorem missed (A : Circuit) (leg : Monotone2 A) (h : Input n → Bool)
    (conj : ∀x,A.eval (portInputs x (h x))=allOn x) {i} (lost : i∈missing n A) :
    portIndex n∈deps (n+3) A A.output ∧ h (alone i)=false := by
  classical
  let W:=deps (n+3) A A.output
  have up : A.eval (portInputs (one n) (h (one n)))=true := by rw [conj,allOnTrue];simp [one]
  have down:=conj (alone i);rw [badFlip] at down
  have absent : i.castAdd 3∉W := (Finset.mem_filter.mp lost).2
  have step (safe : portIndex n∈W → h (one n)=true → h (alone i)=true) : False := by
    have feed : feeds (input3 (one n) (h (one n))) (input3 (alone i) (h (alone i))) W := by
      intro a;refine Fin.addCases ?_ ?_ a
      · intro j mem _;have diff : j≠i := fun e => absent (e ▸ mem);simp [input3,alone,diff]
      · intro j;fin_cases j
        · simp [input3]
        · simp [input3]
        · intro mem;simpa [input3] using safe mem
    have t:=supported A leg _ _ A.output feed
    rw [list3,list3] at t
    exact Bool.noConfusion ((t up).symm.trans down)
  constructor
  · by_contra no;exact step (fun mem => (no mem).elim)
  · apply Bool.eq_false_iff.mpr;intro yes;exact step (fun _ _ => yes)
theorem missSize (n : Nat) (A : Circuit) :
    n ≤ (missing n A).card+A.size+1 ∧ ((missing n A).Nonempty → n ≤ (missing n A).card+A.size ∨ portIndex n∉deps (n+3) A A.output) := by
  let M:=missing n A;let W:=deps (n+3) A A.output
  let used:=(Mᶜ).image (Fin.castAdd 3)
  have inj : Function.Injective (Fin.castAdd (n:=n) 3) := fun _ _ e => Fin.ext (congrArg (fun a : Fin (n+3) => a.val) e)
  have sub : used⊆W := by intro z hz;obtain ⟨j,jh,rfl⟩:=Finset.mem_image.mp hz;simpa [M,missing,W] using jh
  have size : used.card=n-M.card := by simp [used,Finset.card_image_of_injective _ inj,Finset.card_compl]
  have bound:=depCost (n+3) A A.output;change W.card ≤ A.size+1 at bound
  have lo:=Finset.card_le_card sub
  change n ≤ M.card+A.size+1 ∧ _;refine ⟨by omega,?_⟩;intro _
  by_cases p:portIndex n∈W
  · left;have notin : portIndex n∉used := by
      intro h;obtain ⟨j,_,eq⟩:=Finset.mem_image.mp h;have v:=congrArg Fin.val eq;change j.val=n+2 at v;omega
    have b:=Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨p,sub⟩)
    rw [Finset.card_insert_of_notMem notin] at b;change n ≤ M.card+A.size;omega
  · exact Or.inr p
end PEqualNP.Outside.L_lib_1616_aux

namespace PEqualNP.Outside.L_lib_1616_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped Classical
noncomputable def optimum (E : Bank n) := sInf {s : Nat | ∃C : Circuit,Legal (n+2) C ∧ C.size=s ∧ ∀x,C.eval (raw x)=desired E x}
theorem plainBound (C : Circuit) (leg : Monotone2 C) (full : ∀x:Input n,C.eval (raw x)=allOn x) : n-1 ≤ C.size := by
  let W:=deps (n+2) C C.output
  have every (i : Fin n) : i.castAdd 2∈W := by
    by_contra absent
    have feed : feeds (input2 (one n)) (input2 (alone i)) W := by
      intro a;refine Fin.addCases ?_ ?_ a
      · intro j mem _;have diff : j≠i := fun e => absent (e ▸ mem);simp [input2,alone,diff]
      · intro j;simp [input2]
    have imp:=supported C leg _ _ C.output feed
    rw [list2,list2] at imp
    have on : C.eval (raw (one n))=true := by rw [full,allOnTrue];simp [one]
    have off:=full (alone i);rw [badFlip] at off;exact Bool.noConfusion ((imp on).symm.trans off)
  have sub : Finset.univ.image (Fin.castAdd 2)⊆W := by intro a h;obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp h;exact every i
  have inj : Function.Injective (Fin.castAdd (n:=n) 2) := fun _ _ e => Fin.ext (congrArg (fun a : Fin (n+2) => a.val) e)
  have lo:=Finset.card_le_card sub;rw [Finset.card_image_of_injective _ inj,Finset.card_univ,Fintype.card_fin] at lo
  have hi:=depCost (n+2) C C.output;change W.card ≤ C.size+1 at hi;omega
theorem appendBranch (P D : Circuit) (lp : Legal (n+2) P) (ld : Legal (n+3) D) :
    ∃C : Circuit, Legal (n+2) C ∧ C.size=P.size+D.size ∧ ∀x : Input n,C.eval (raw x)=D.eval (portInputs x (P.eval (raw x))) := by
  let C:=combined (n+2) P.gates P.output D
  refine ⟨C,combineLegal ⟨lp.1,lp.2.1⟩ lp.2.2 ld,combSize ..,?_⟩
  intro x;exact evaluateCombined (raw x) (by simp [raw]) P.gates P.output lp.2.2 D
theorem groundBranch (D : Circuit) (ld : Legal (n+3) D) :
    ∃C : Circuit,Legal (n+2) C ∧ C.size=D.size ∧ ∀x : Input n,C.eval (raw x)=D.eval (portInputs x false) := by
  let C:=combined (n+2) [] n D
  have pin : n<n+2+([] : List Gate).length := by simp
  have initial : Monotone2 (⟨[],0⟩ : Circuit) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) ⟨[],0⟩ := by simp [Monotone2,PEqualNP.MetaComplexity.NestedCover.ReadsBack]
  refine ⟨C,combineLegal initial pin ld,by simp [C,combSize],?_⟩
  intro x;have eq:=evaluateCombined (raw x) (by simp [raw]) [] n pin D
  have bit : (run opEval (raw x) []).getD n false=false := by
    change (List.ofFn x++[false,true]).getD n false=false
    rw [List.getD_append_right _ _ _ _ (by simp)];simp
  rw [bit] at eq;exact eq
theorem isolation (E : Bank n) (P A B : Circuit) (lp : Legal (n+2) P) (la : Legal (n+3) A) (lb : Legal (n+3) B)
    (work : ∀x,A.eval (portInputs x (P.eval (raw x)))=allOn x ∧ B.eval (portInputs x (P.eval (raw x)))=desired E x) :
    n-1 ≤ P.size+A.size ∧ optimum E ≤ P.size+B.size ∧
    ((∀e∈E,P.eval (raw (indicator e))=false) → optimum E ≤ B.size) := by
  obtain ⟨C,lc,ca,ev⟩:=appendBranch P A lp la
  have bound:=plainBound C lc.1 (fun x => (ev x).trans (work x).1)
  obtain ⟨D,ld,db,evalD⟩:=appendBranch P B lp lb
  refine ⟨ca ▸ bound,Nat.sInf_le ⟨D,ld,db,fun x => (evalD x).trans (work x).2⟩,?_⟩
  intro silent;obtain ⟨T,lt,sz,runT⟩:=groundBranch B lb
  apply Nat.sInf_le;refine ⟨T,lt,sz,?_⟩
  intro x;rw [runT];apply Bool.eq_iff_iff.mpr;constructor
  · intro yes;have imp:=branchMono B lb.1 x x false (P.eval (raw x)) (fun _ h => h) (by simp) yes
    exact (work x).2 ▸ imp
  · intro hit;obtain ⟨e,he,all⟩:=(of_decide_eq_true hit : ∃e∈E,productBit x e=true)
    have incl : below (indicator e) x := by
      intro i h;exact (of_decide_eq_true all : ∀j∈e,x j=true) i (by simpa [indicator] using h)
    have ok : desired E (indicator e)=true := by
      apply decide_eq_true;refine ⟨e,he,?_⟩;simp [productBit,indicator]
    have on:=(work (indicator e)).2.trans ok;rw [silent e he] at on
    exact branchMono B lb.1 _ x false false incl (fun h => h) on
end PEqualNP.Outside.L_lib_1616_aux

namespace PEqualNP.Outside.L_lib_1616_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped Classical
theorem saving (E : Bank n) (non : E.Nonempty) (each : ∀e∈E,e.Nonempty)
    (P A B : Circuit) (lp : Legal (n+2) P) (la : Legal (n+3) A) (lb : Legal (n+3) B)
    (work : ∀x,A.eval (portInputs x (P.eval (raw x)))=allOn x ∧ B.eval (portInputs x (P.eval (raw x)))=desired E x) :
    let r:=E.sup Finset.card
    let paid:=P.size+A.size+B.size
    (n-1)+optimum E ≤ paid+(r-1) ∧ (2 ≤ r → (n-1)+optimum E=paid+(r-1) →
       ∃e∈E,e.card=r ∧ ∀x,P.eval (raw x)=productBit x e) := by
  classical
  intro r paid
  let h (x : Input n):=P.eval (raw x)
  let M:=missing n A
  obtain ⟨t,ht⟩:=non;have cap:=Finset.le_sup (f:=Finset.card) ht
  have big:=Finset.card_pos.mpr (each t ht);have rt : 0<r := by change t.card ≤ r at cap;omega
  have nt : 0<n := by have b:=Finset.card_le_card (Finset.subset_univ t);simp at b;omega
  obtain ⟨joint,solo,ground⟩:=isolation E P A B lp la lb work
  have conj (x) : A.eval (portInputs x (h x))=allOn x := (work x).1
  by_cases live:∃e∈E,h (indicator e)=true
  · obtain ⟨e,he,on⟩:=live
    have small : M⊆e := by
      intro i lost;by_contra outside
      have trigger:=(missed A la.1 h conj lost).2
      have up : below (indicator e) (alone i) := by
        intro j hj;have member:j∈e := by simpa [indicator] using hj
        have diff:j≠i := fun eq => outside (eq ▸ member);simpa [alone] using diff
      have yes:=portMono P lp.1 _ _ up on;rw [show P.eval (raw (alone i))=false from trigger] at yes;contradiction
    have ms:=Finset.card_le_card small;have er : e.card ≤ r := Finset.le_sup he
    obtain ⟨weak,strong⟩:=missSize n A
    change n ≤ M.card+A.size+1 at weak
    by_cases used:M.Nonempty
    · have wire:=(missed A la.1 h conj used.choose_spec).1
      have lower : n ≤ M.card+A.size := (strong used).resolve_right (fun bad => bad wire)
      dsimp only [paid];refine ⟨by omega,?_⟩;intro hr eq
      have card : e.card=r := by omega
      have full : M=e := Finset.eq_of_subset_of_card_le small (by omega)
      refine ⟨e,he,card,?_⟩;intro x;apply Bool.eq_iff_iff.mpr
      constructor
      · intro yes;apply decide_eq_true;intro i ie
        by_contra notOn
        have up : below x (alone i) := by
          intro j lit;have ne : j≠i := fun eq => notOn (eq ▸ lit);simpa [alone] using ne
        have impossible:=portMono P lp.1 _ _ up yes
        have off:=(missed A la.1 h conj (show i∈M from full.symm ▸ ie)).2
        exact Bool.noConfusion (off.symm.trans impossible)
      · intro yes;have inc:=of_decide_eq_true yes
        apply portMono P lp.1 (indicator e) x _ on
        intro i hi;exact inc i (by simpa [indicator] using hi)
    · have zero : M.card=0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp used)
      dsimp only [paid];exact ⟨by omega,by intro _ eq;omega⟩
  · have silent : ∀e∈E,h (indicator e)=false := by intro e he;apply Bool.eq_false_iff.mpr;intro yes;exact live ⟨e,he,yes⟩
    have b:=ground silent;dsimp only [paid];exact ⟨by omega,by intro _ eq;omega⟩
end PEqualNP.Outside.L_lib_1616_aux

open PEqualNP.Outside.L_lib_1616_aux in
theorem PEqualNP.Outside.L_lib_1616 : (
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  ∀ (n : Nat) (E : Finset (Finset (Fin n))), E.Nonempty → (∀ e ∈ E, e.Nonempty) →
    (∀ a ∈ E, ∀ b ∈ E, a ⊆ b → a = b) →
    let r := E.sup Finset.card
    let productBit := fun (x : Fin n → Bool) (e : Finset (Fin n)) =>
      decide (∀ i ∈ e, x i = true)
    let g := fun x : Fin n → Bool => decide (∃ e ∈ E, productBit x e = true)
    let raw := fun x : Fin n → Bool => List.ofFn x ++ [false,true]
    let legal := fun (w : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack w C ∧
      C.output < w+C.size
    let opt := sInf {s : Nat | ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      legal (n+2) C ∧ C.size = s ∧ ∀ x, C.eval (raw x) = g x}
    ∀ P A B : PEqualNP.CircuitLowerBounds.Circuit,
      legal (n+2) P → legal (n+3) A → legal (n+3) B →
      (∀ x : Fin n → Bool,
        let ys := raw x ++ [P.eval (raw x)]
        A.eval ys = (List.ofFn x).all id ∧ B.eval ys = g x) →
      let paid := P.size+A.size+B.size
      (n-1)+opt ≤ paid+(r-1) ∧
      (2 ≤ r → (n-1)+opt = paid+(r-1) →
        ∃ e ∈ E, e.card = r ∧ ∀ x, P.eval (raw x) = productBit x e)
) := by
  intro n E ne active _ r prod' g' raw' legal' opt' P A B lp la lb work paid
  have pEq (x : Input n) (e : Bits n) : prod' x e=productBit x e := by
    apply Bool.eq_iff_iff.mpr;simp only [prod',productBit,decide_eq_true_eq]
  have gEq (x : Input n) : g' x=desired E x := by
    apply Bool.eq_iff_iff.mpr;simp only [g',desired,decide_eq_true_eq,pEq]
  have optEq : opt'=optimum E := by
    apply congrArg sInf;ext s
    simp only [gEq];rfl
  have tasks (x : Input n) : A.eval (portInputs x (P.eval (raw x)))=allOn x ∧ B.eval (portInputs x (P.eval (raw x)))=desired E x := by
    rw [←gEq];exact work x
  rw [optEq];simp_rw [pEq]
  exact saving E ne active P A B lp la lb tasks
