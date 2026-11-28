import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1590_aux
open scoped Classical
abbrev Row (α : Type) := Finset α
abbrev Family (α : Type) := Finset (Row α)
def Proper (E : Family α) := ∀A∈E,A.Nonempty
def Separated (E : Family α) := ∀A∈E,∀B∈E,A≠B → Disjoint A B
def Hits (S : Row α) (E : Family α) := ∀A∈E,∃a∈A,a∈S
def Holds (read : α → Prop) (E : Family α) := ∃A∈E,∀a∈A,read a
theorem hitBound (E : Family α) (ok : Proper E) : ∃ S : Row α, S.card≤E.card ∧ Hits S E := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨∅,by simp,by simp [Hits]⟩
  | @insert A E fresh ih =>
    obtain ⟨a,ha⟩:=ok A (Finset.mem_insert_self _ _)
    obtain ⟨S,sz,hit⟩:=ih (fun B h => ok B (Finset.mem_insert_of_mem h))
    refine ⟨insert a S,?_,?_⟩
    · rw [Finset.card_insert_of_notMem fresh];exact (Finset.card_insert_le _ _).trans (by omega)
    · intro B h;rcases Finset.mem_insert.mp h with rfl|h
      · exact ⟨a,ha,Finset.mem_insert_self _ _⟩
      · obtain ⟨j,hj,hh⟩:=hit B h;exact ⟨j,hj,Finset.mem_insert_of_mem hh⟩
theorem cheapOverlap (E : Family α) (ok : Proper E) (overlap : ¬Separated E) :
    ∃S : Row α,S.card<E.card ∧ Hits S E := by
  classical
  simp only [Separated,not_forall,not_imp] at overlap
  obtain ⟨A,ha,B,hb,ne,nd⟩:=overlap
  rw [Finset.disjoint_left] at nd;push_neg at nd;obtain ⟨a,hA,hB⟩:=nd
  let tail := (E.erase A).erase B
  have ht : tail⊆E := (Finset.erase_subset ..).trans (Finset.erase_subset ..)
  obtain ⟨S,sz,hit⟩:=hitBound tail (fun T h => ok T (ht h))
  refine ⟨insert a S,?_,?_⟩
  · have hba := Finset.mem_erase.mpr ⟨ne.symm,hb⟩
    have c1:=Finset.card_erase_add_one ha
    have c2:=Finset.card_erase_add_one hba
    have c3:=Finset.card_insert_le a S
    dsimp [tail] at sz;omega
  · intro T h
    by_cases x:T=A
    · exact ⟨a,x ▸ hA,Finset.mem_insert_self _ _⟩
    by_cases y:T=B
    · exact ⟨a,y ▸ hB,Finset.mem_insert_self _ _⟩
    obtain ⟨i,hi,mem⟩:=hit T (Finset.mem_erase.mpr ⟨y,Finset.mem_erase.mpr ⟨x,h⟩⟩)
    exact ⟨i,hi,Finset.mem_insert_of_mem mem⟩
theorem separatedLower {E : Family α} (sep : Separated E) {S : Row α} (hit : Hits S E) : E.card≤S.card := by
  classical
  choose f hf hs using hit
  let pick (A : ↥E) : ↥S := ⟨f A.1 A.2,hs A.1 A.2⟩
  have inj : Function.Injective pick := by
    intro A B eq
    apply Subtype.ext
    by_contra ne
    have same : f A.val A.property=f B.val B.property := congrArg Subtype.val eq
    exact Finset.disjoint_left.mp (sep _ A.property _ B.property ne) (hf _ _) (same ▸ hf _ B.property)
  simpa using Fintype.card_le_of_injective pick inj
end PEqualNP.Outside.L_lib_1590_aux

namespace PEqualNP.Outside.L_lib_1590_aux
open scoped Classical
def Raised (v : α → Prop) (p : Prop) : Option α → Prop := Option.elim' p v
noncomputable def Project (E : Family (Option α)) : Family α := E.image Finset.eraseNone
noncomputable def Tail (E : Family (Option α)) := E.filter (fun T => none∉T)
noncomputable def Expand (E : Family (Option α)) (A B : Row α) := insert A (insert B (Project (Tail E)))
theorem projNonempty {T : Row (Option α)} (nt : T.Nonempty) (ne : T ≠ {none}) : (Finset.eraseNone T).Nonempty := by
  by_contra empty
  apply ne
  have no (a : α) : some a∉T := fun ha => empty ⟨a,Finset.mem_eraseNone.mpr ha⟩
  obtain ⟨x,hx⟩:=nt
  cases x with
  | none => ext y;cases y <;> simp [hx,no]
  | some a => exact (no a hx).elim
theorem projectProper {E : Family (Option α)} (ok : Proper E) (absent : {none}∉E) : Proper (Project E) := by
  intro A h;obtain ⟨T,mem,rfl⟩:=Finset.mem_image.mp h
  exact projNonempty (ok _ mem) (fun eq => absent (eq ▸ mem))
theorem projectUpper {E : Family (Option α)} {v : α → Prop} {p : Prop} :
    Holds (Raised v p) E → Holds v (Project E) := by
  rintro ⟨T,mem,hv⟩
  exact ⟨_,Finset.mem_image_of_mem _ mem,fun a h => hv _ (Finset.mem_eraseNone.mp h)⟩
theorem tailProper {E : Family (Option α)} (ok : Proper E) : Proper (Project (Tail E)) := by
  apply projectProper
  · exact fun T h => ok _ (Finset.mem_filter.mp h).1
  · simp [Tail]
theorem expandProper {E : Family (Option α)} (ok : Proper E) {A B : Row α} (ha : A.Nonempty) (hb : B.Nonempty) : Proper (Expand E A B) := by
  intro T h;rcases Finset.mem_insert.mp h with rfl|h
  · exact ha
  rcases Finset.mem_insert.mp h with rfl|h
  · exact hb
  exact tailProper ok _ h
theorem expandCard (E : Family (Option α)) (present : {none}∈E) (A B : Row α) : (Expand E A B).card≤E.card+1 := by
  have sub : Tail E⊆E.erase {none} := by
    intro T h;obtain ⟨t,notIn⟩:=Finset.mem_filter.mp h
    exact Finset.mem_erase.mpr ⟨fun eq => notIn (eq ▸ Finset.mem_singleton_self _),t⟩
  have c0:=Finset.card_erase_add_one present
  have c1:=Finset.card_le_card sub
  have c2 : (Project (Tail E)).card≤(Tail E).card := Finset.card_image_le
  have c3:=Finset.card_insert_le B (Project (Tail E))
  have c4:=Finset.card_insert_le A (insert B (Project (Tail E)))
  unfold Expand;omega
def AllOn (v : α → Prop) (T : Row α) := ∀a∈T,v a
theorem expansion {E : Family (Option α)} (present : {none}∈E) (A B : Row α) (v : α → Prop) :
    Holds (Raised v (AllOn v A ∨ AllOn v B)) E ↔ Holds v (Expand E A B) := by
  constructor
  · rintro ⟨T,mem,hv⟩
    by_cases h : none∈T
    · rcases hv none h with h|h
      · exact ⟨A,Finset.mem_insert_self _ _,h⟩
      · exact ⟨B,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨mem,h⟩))),fun i hi => hv _ (Finset.mem_eraseNone.mp hi)⟩
  · rintro ⟨T,mem,hv⟩
    have root (h : AllOn v A ∨ AllOn v B) : Holds (Raised v (AllOn v A ∨ AllOn v B)) E :=
      ⟨_,present,fun i hi => (Finset.mem_singleton.mp hi) ▸ h⟩
    rcases Finset.mem_insert.mp mem with rfl|mem
    · exact root (Or.inl hv)
    rcases Finset.mem_insert.mp mem with rfl|mem
    · exact root (Or.inr hv)
    obtain ⟨U,hu,rfl⟩:=Finset.mem_image.mp mem
    obtain ⟨mem,hn⟩:=Finset.mem_filter.mp hu
    refine ⟨U,mem,?_⟩
    intro i hi;cases i with
    | none => exact (hn hi).elim
    | some a => exact hv a (Finset.mem_eraseNone.mpr hi)
end PEqualNP.Outside.L_lib_1590_aux

namespace PEqualNP.Outside.L_lib_1590_aux
open scoped Classical
abbrev Input (n : Nat) := Fin n → Bool
def Kills (S : Row (Fin n)) (g : Input n → Prop) := ∀x,(∀i∈S,x i=false) → ¬g x
def Cert (b : Nat) (g : Input n → Prop) := ∃S : Row (Fin n),S.card≤b ∧ Kills S g
def Tight (b : Nat) (g : Input n → Prop) := ∀ S : Row (Fin n),Kills S g → b≤S.card
def Form (g : Input n → Prop) := ∃ E : Family (Fin n),Proper E ∧ Separated E ∧ ∀x,g x ↔ Holds (fun i => x i=true) E
def Rank (v : Input n → α → Prop) (r : Nat) := ∀ E : Family α, Proper E →
  Cert (r+E.card) (fun x => Holds (v x) E) ∧ (Tight (r+E.card) (fun x => Holds (v x) E) → Form (fun x => Holds (v x) E))
theorem hitsKill {E : Family (Fin n)} {S} (h : Hits S E) : Kills S (fun x => Holds (fun i => x i=true) E) := by
  intro x hx; rintro ⟨T,t,ht⟩;obtain ⟨i,hi,hs⟩:=h T t
  have a : x i=true :=ht i hi;rw [hx _ hs] at a;contradiction
theorem rawRank (n) : Rank (fun (x : Input n) i => x i=true) 0 := by
  intro E ok
  obtain ⟨S,sz,hit⟩:=hitBound E ok
  refine ⟨⟨S,by omega,hitsKill hit⟩,?_⟩
  intro tight;refine ⟨E,ok,?_,fun _ => Iff.rfl⟩
  by_contra overlap
  obtain ⟨U,cu,h⟩:=cheapOverlap E ok overlap
  have z:=tight _ (hitsKill h);omega
theorem nextRank {v : Input n → α → Prop} {r : Nat} (prev : Rank v r)
    {A B : Row α} (ha : A.Nonempty) (hb : B.Nonempty) :
    Rank (fun x => Raised (v x) (AllOn (v x) A ∨ AllOn (v x) B)) (r+1) := by
  intro E ok
  by_cases present : {none}∈E
  · have hc:=expandCard E present A B
    obtain ⟨⟨S,sz,kill⟩,classify⟩:=prev _ (expandProper ok ha hb)
    have eq x:=expansion present A B (v x)
    have tr := fun (S : Row (Fin n)) (h : Kills S (fun x => Holds (v x) (Expand E A B))) =>
      show Kills S (fun x => Holds (Raised (v x) (AllOn (v x) A ∨ AllOn (v x) B)) E) from
        fun x hx hh => h x hx ((eq x).mp hh)
    refine ⟨⟨S,by omega,tr S kill⟩,?_⟩
    intro tight
    obtain ⟨D,p,s,e⟩:=classify (fun U h => by have z:=tight U (tr U h);omega)
    exact ⟨D,p,s,fun x => (eq x).trans (e x)⟩
  · obtain ⟨⟨S,sz,kill⟩,_⟩:=prev _ (projectProper ok present)
    have bound : (Project E).card≤E.card := Finset.card_image_le
    have kills : Kills S (fun x => Holds (Raised (v x) (AllOn (v x) A ∨ AllOn (v x) B)) E) :=
      fun x hx hh => kill x hx (projectUpper hh)
    refine ⟨⟨S,by omega,kills⟩,?_⟩
    intro tight;have h:=tight _ kills;omega
end PEqualNP.Outside.L_lib_1590_aux

namespace PEqualNP.Outside.L_lib_1590_aux
open scoped Classical
abbrev Wire (α : Type) := Option (Row α)
noncomputable def value (v : α → Prop) : Wire α → Bool
  | none => false
  | some A => decide (AllOn v A)
noncomputable def prod : Wire α → Wire α → Wire α
  | some A,some B => some (A∪B)
  | _,_ => none
theorem prodVal (v : α → Prop) (a b : Wire α) : value v (prod a b)=(value v a && value v b) := by
  cases a <;> cases b <;> simp only [prod,value,Bool.false_and,Bool.and_false]
  rename_i A B
  have h : AllOn v (A∪B) ↔ AllOn v A ∧ AllOn v B := Finset.forall_mem_union
  by_cases a : AllOn v A <;> by_cases b : AllOn v B <;> simp [h,a,b]
noncomputable def liftW : Wire α → Wire (Option α) := Option.map (fun A => A.image some)
theorem liftVal (v : α → Prop) (p : Prop) (a : Wire α) : value (Raised v p) (liftW a)=value v a := by
  cases a <;> simp [liftW,value,AllOn,Raised] <;> congr 1
def Rep (budget : Nat) (w : Input n → List Bool) :=
  ∃ (α : Type) (v : Input n → α → Prop) (r : Nat) (t : List (Wire α)),
    r≤budget ∧ Rank v r ∧ ∀x,w x=t.map (value (v x))
theorem inputRep (n : Nat) : Rep 0 (fun x : Input n => List.ofFn x ++ [false,true]) := by
  classical
  let ts := List.ofFn (fun i : Fin n => (some {i} : Wire (Fin n)))
  refine ⟨Fin n,fun x i => x i=true,0,ts++[none,some ∅],by omega,rawRank n,?_⟩
  intro x;simp [ts,List.map_ofFn,value,AllOn,Function.comp_def]
theorem bump {w : Input n → List Bool} (h : Rep a w) (le : a≤b) : Rep b w := by
  obtain ⟨α,v,r,t,sz,rank,eq⟩:=h;exact ⟨α,v,r,t,sz.trans le,rank,eq⟩
theorem wireVal (v : α → Prop) (t : List (Wire α)) (i : Nat) :
    (t.map (value v)).getD i false=value v (t.getD i none) := List.getD_map t none (value v)
theorem orRep {v : Input n → α → Prop} {r} (rank : Rank v r) (ts : List (Wire α)) (a b : Wire α) :
    Rep (r+1) (fun x => ts.map (value (v x)) ++ [value (v x) a || value (v x) b]) := by
  classical
  have old (c : Wire α) (eq : ∀x,(value (v x) a || value (v x) b)=value (v x) c) :
      Rep (r+1) (fun x => ts.map (value (v x)) ++ [value (v x) a || value (v x) b]) :=
    ⟨α,v,r,ts++[c],by omega,rank,fun x => by simp [eq x]⟩
  cases a with
  | none => exact old b (by simp [value])
  | some A => cases b with
    | none => exact old (some A) (by simp [value])
    | some B =>
      by_cases ha : A.Nonempty
      · by_cases hb : B.Nonempty
        · let v' x := Raised (v x) (AllOn (v x) A ∨ AllOn (v x) B)
          refine ⟨Option α,v',r+1,ts.map liftW ++ [some {none}],le_rfl,nextRank rank ha hb,?_⟩
          intro x
          have he : (value (v' x)) ∘ liftW=value (v x) := funext (liftVal _ _)
          simp only [List.map_append,List.map_map,he,List.map_cons,List.map_nil]
          congr 2
          simp [value,AllOn,v',Raised] <;> congr 1 <;> congr 1
        · have e := Finset.not_nonempty_iff_eq_empty.mp hb
          exact old (some B) (by simp [e,value,AllOn])
      · have e := Finset.not_nonempty_iff_eq_empty.mp ha
        exact old (some A) (by simp [e,value,AllOn])
end PEqualNP.Outside.L_lib_1590_aux

namespace PEqualNP.Outside.L_lib_1590_aux
open PEqualNP.CircuitLowerBounds
open scoped Classical
noncomputable def binCost (g : Gate) : Nat := if g.op=.or ∧ g.inputs.length=2 then 1 else 0
def tick (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def legal (g : Gate) := (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2
theorem symbolicStep {w : Input n → List Bool} (rep : Rep b w) (g : Gate) (ok : legal g) :
    Rep (b+binCost g) (fun x => tick (w x) g) := by
  classical
  obtain ⟨α,v,r,ts,sz,rank,eq⟩:=rep
  have plain (g : Gate) (c : Wire α) (ok : ∀x,g.op.eval (g.inputs.map fun i => (w x).getD i false)=value (v x) c) :
      Rep (b+binCost g) (fun x => tick (w x) g) := by
    exact ⟨α,v,r,ts++[c],by omega,rank,fun x => by simp only [tick]; rw [ok x,eq x]; simp⟩
  have get (i) x : (w x).getD i false=value (v x) (ts.getD i none) := by rw [eq,wireVal]
  rcases g with ⟨op,is⟩
  rcases ok with ⟨andOr,arity⟩
  change op=.and ∨ op=.or at andOr
  change is.length≤2 at arity
  cases is with
  | nil =>
    rcases andOr with rfl|rfl
    · exact plain _ (some ∅) (by simp [GateOp.eval,value,AllOn])
    · exact plain _ none (by simp [GateOp.eval,value])
  | cons i tail => cases tail with
    | nil =>
      rcases andOr with rfl|rfl <;> exact plain _ (ts.getD i none) (by intro x;simp [GateOp.eval] <;> exact get i x)
    | cons j tail => cases tail with
      | cons k tail => simp at arity
      | nil =>
        rcases andOr with rfl|rfl
        · exact plain _ (prod (ts.getD i none) (ts.getD j none)) (by intro x;simp [GateOp.eval,prodVal];exact congrArg₂ Bool.and (get i x) (get j x))
        · have h:=orRep rank ts (ts.getD i none) (ts.getD j none)
          have bd : r+1 ≤ b+binCost ⟨.or,[i,j]⟩ := by simp [binCost];omega
          apply bump _ bd
          convert h using 1
          funext x;unfold tick;simp only [List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,Bool.or_false,id_eq,eq x,wireVal]
noncomputable def countG (gs : List Gate) : Nat := (gs.map binCost).sum
theorem foldRep {w : Input n → List Bool} (rep : Rep b w) (gs : List Gate) (ok : ∀g∈gs,legal g) :
    Rep (b+countG gs) (fun x => gs.foldl tick (w x)) := by
  induction gs generalizing w b with
  | nil => simpa [countG] using rep
  | cons g gs ih =>
    have z:=ih (symbolicStep rep g (ok _ (by simp))) (fun j h => ok j (by simp [h]))
    simpa only [List.foldl_cons,countG,List.map_cons,List.sum_cons,Nat.add_assoc] using z
theorem circuitRep (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C) (n : Nat) :
    Rep (countG C.gates) (fun x : Input n => C.wires (List.ofFn x ++ [false,true])) := by
  change Rep _ (fun x => C.gates.foldl tick (List.ofFn x ++ [false,true]))
  simpa only [Nat.zero_add] using foldRep (inputRep n) C.gates (fun g h => hm g h)
end PEqualNP.Outside.L_lib_1590_aux

namespace PEqualNP.Outside.L_lib_1590_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
noncomputable def charged (C : Circuit) := ((Finset.range C.size).filter (fun j => let g := gateAt C j;g.op=.or ∧ g.inputs.length=2)).card
theorem countEq (C : Circuit) : charged C=countG C.gates := by
  classical
  have eq (gs : List Gate) : ∀d : Gate,((Finset.range gs.length).filter (fun j => (gs.getD j d).op=.or ∧ (gs.getD j d).inputs.length=2)).card=countG gs := by
    induction gs using List.reverseRecOn with
    | nil => simp [countG]
    | append_singleton gs g ih =>
      intro d
      rw [List.length_append];change ((Finset.range (gs.length+1)).filter _).card=_
      rw [Finset.range_add_one,Finset.filter_insert]
      have sam : ((Finset.range gs.length).filter (fun j => ((gs++[g]).getD j d).op=.or ∧ ((gs++[g]).getD j d).inputs.length=2))=
        ((Finset.range gs.length).filter (fun j => (gs.getD j d).op=.or ∧ (gs.getD j d).inputs.length=2)) := by
        apply Finset.filter_congr;intro j hj
        have e : (gs++[g]).getD j d=gs.getD j d := by simp [List.getD_eq_getElem?_getD,List.getElem?_append_left (Finset.mem_range.mp hj)]
        rw [e]
      have last : (gs++[g]).getD gs.length d=g := by simp
      rw [sam,last];have old:=ih d
      by_cases prop : g.op=.or ∧ g.inputs.length=2 <;> simp [prop,countG,binCost,Finset.card_insert_of_notMem] at old ⊢ <;> omega
  exact eq _ _
def zeroInput (n) : Input n := fun _ => false
def ZeroCert (g : Input n → Bool) (S : Row (Fin n)) := ∀x,(∀i∈S,x i=false) → g x=g (zeroInput n)
noncomputable def minCert (g : Input n → Bool) := sInf {b : Nat | ∃S : Row (Fin n),S.card=b ∧ ZeroCert g S}
theorem certLe {g : Input n → Bool} {S} (cert : ZeroCert g S) : minCert g≤S.card := Nat.sInf_le ⟨S,rfl,cert⟩
theorem pairDiff {g : Input n → Bool} (nonc : ∃x y,g x≠g y) (b : Bool) (eq : ∀x,g x=b) : False := by
  obtain ⟨x,y,h⟩:=nonc;exact h ((eq x).trans (eq y).symm)
theorem necessaryWire {g : Input n → Bool} {v : Input n → α → Prop} {r} (rank : Rank v r) (a : Wire α)
    (ev : ∀x,value (v x) a=g x) (nonc : ∃x y,g x≠g y) :
    minCert g≤r+1 ∧ (r ≤ minCert g-1 → Form (fun x => g x=true)) := by
  cases a with
  | none => exact (pairDiff nonc false (fun x => (ev x).symm)).elim
  | some A =>
    by_cases ha : A.Nonempty
    · have ok : Proper {A} := by simpa [Proper] using ha
      have eq (x) : Holds (v x) {A} ↔ g x=true := by rw [←ev];simp only [Holds,value,Finset.mem_singleton,exists_eq_left]; exact (@decide_eq_true_iff (AllOn (v x) A) (Classical.propDecidable _)).symm
      obtain ⟨⟨S,sz,kill⟩,classify⟩:=rank _ ok
      have gz : g (zeroInput n)=false := by
        apply Bool.eq_false_iff.mpr
        exact fun h => kill _ (by simp [zeroInput]) ((eq _).mpr h)
      have zd (T : Row (Fin n)) (z : Kills T (fun x => Holds (v x) {A})) : ZeroCert g T := by
        intro x hx;rw [gz];exact Bool.eq_false_iff.mpr (fun h => z _ hx ((eq _).mpr h))
      have upper:=certLe (zd S kill);simp only [Finset.card_singleton] at sz
      constructor
      · omega
      · intro low
        have positive : 0 < minCert g := by
          by_contra! h
          have mem : minCert g ∈ {b : Nat | ∃T : Row (Fin n),T.card=b ∧ ZeroCert g T} := by
            apply Nat.sInf_mem;exact ⟨_,_,rfl,zd S kill⟩
          obtain ⟨T,ct,ht⟩:=mem
          have em : T=∅ := Finset.card_eq_zero.mp (by omega)
          exact pairDiff nonc _ (fun x => ht x (by simp [em]))
        obtain ⟨D,p,s,evalD⟩:=classify (fun T ht => by have bound:=certLe (zd T ht);simp;omega)
        exact ⟨D,p,s,fun x => (eq x).symm.trans (evalD x)⟩
    · have em:=Finset.not_nonempty_iff_eq_empty.mp ha
      exact (pairDiff nonc true (fun x => by simpa [em,value,AllOn] using (ev x).symm)).elim
end PEqualNP.Outside.L_lib_1590_aux

namespace PEqualNP.Outside.L_lib_1590_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
def width (n : Nat) (gs : List Gate) := n+2+gs.length
def legalList (n : Nat) (gs : List Gate) := (∀g∈gs,legal g) ∧ ReadsBack (n+2) ⟨gs,0⟩
def run (n : Nat) (gs : List Gate) (x : Input n) := gs.foldl tick (List.ofFn x ++ [false,true])
def Obs (gs : List Gate) (f : Input n → Prop) (i : Nat) := i<width n gs ∧ ∀x,(run n gs x).getD i false=true ↔ f x
theorem foldLen (gs : List Gate) (w : List Bool) : (gs.foldl tick w).length=w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih,tick];omega
theorem runLen (gs : List Gate) (x : Input n) : (run n gs x).length=width n gs := by simp [run,foldLen,width]
theorem runSnoc (gs : List Gate) (g : Gate) (x : Input n) : run n (gs++[g]) x=tick (run n gs x) g := by simp [run]
theorem stable {f : Input n → Prop} {i gs} (ok : Obs gs f i) (tail : List Gate) : Obs (gs++tail) f i := by
  induction tail using List.reverseRecOn with
  | nil => simpa using ok
  | append_singleton tail g ih =>
    rw [←List.append_assoc]
    refine ⟨by have h:=ih.1;simp [width] at h ⊢;omega,?_⟩
    intro x;rw [runSnoc];unfold tick
    rw [List.getD_append _ _ _ _ (by rw [runLen];exact ih.1)];exact ih.2 x
theorem baseInput (i : Fin n) : Obs [] (fun x : Input n => x i=true) i.val := by
  refine ⟨by simp [width];omega,?_⟩
  intro x;change (List.ofFn x++[false,true]).getD i.val false=true ↔ _
  rw [List.getD_append _ _ _ _ (by simp)];simp
theorem baseTrue (n : Nat) : Obs [] (fun _ : Input n => True) (n+1) := by
  refine ⟨by simp [width],?_⟩
  intro x;change (List.ofFn x++[false,true]).getD (n+1) false=true ↔ _
  rw [List.getD_append_right _ _ _ _ (by simp)];simp
theorem baseFalse (n : Nat) : Obs [] (fun _ : Input n => False) n := by
  refine ⟨by simp [width],?_⟩
  intro x;change (List.ofFn x++[false,true]).getD n false=true ↔ _
  rw [List.getD_append_right _ _ _ _ (by simp)];simp
theorem pushLegal {gs} (ok : legalList n gs) {g : Gate} (hg : legal g) (prev : ∀i∈g.inputs,i<width n gs) :
    legalList n (gs++[g]) := by
  refine ⟨?_,?_⟩
  · intro a h;rcases List.mem_append.mp h with h|h
    · exact ok.1 a h
    · have eq : a=g := by simpa using h
      exact eq ▸ hg
  intro j hj i hi
  change i∈((gs++[g]).getD j _).inputs at hi
  by_cases old : j<gs.length
  · rw [List.getD_append _ _ _ _ old] at hi;exact ok.2 j old i hi
  · have eq : j=gs.length := by simp at hj;omega
    subst j;have mem : i∈g.inputs := by simpa using hi
    exact prev i mem
theorem pushObs {gs} {a b} {f q : Input n → Prop} (ha : Obs gs f a) (hb : Obs gs q b)
    (useOr : Bool) : let op := if useOr then GateOp.or else GateOp.and
    Obs (gs++[⟨op,[a,b]⟩]) (fun x => if useOr then f x ∨ q x else f x ∧ q x) (width n gs) := by
  intro op
  refine ⟨by simp [width],?_⟩
  intro x
  rw [runSnoc]
  change ((run n gs x)++[op.eval [_,_]]).getD (width n gs) false=true ↔ _
  rw [←runLen gs x];simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right le_rfl,Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
  cases useOr <;> simp [op,GateOp.eval,←ha.2 x,←hb.2 x]
end PEqualNP.Outside.L_lib_1590_aux

namespace PEqualNP.Outside.L_lib_1590_aux
open PEqualNP.CircuitLowerBounds
open scoped Classical
theorem productBuild (gs : List Gate) (ok : legalList n gs) (A : Row (Fin n)) :
    ∃ ts i,legalList n (gs++ts) ∧ countG (gs++ts)=countG gs ∧
    Obs (gs++ts) (fun x : Input n => AllOn (fun j => x j=true) A) i := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    refine ⟨[],n+1,by simpa using ok,by simp,?_⟩
    simpa [AllOn] using stable (baseTrue n) gs
  | @insert a A fresh ih =>
    obtain ⟨ts,i,leg,cost,hi⟩:=ih
    let G := gs++ts
    let g : Gate := ⟨.and,[a.val,i]⟩
    have ha : Obs G (fun x : Input n => x a=true) a := by simpa [G] using stable (baseInput a) G
    refine ⟨ts++[g],width n G,?_,?_,?_⟩
    · rw [←List.append_assoc];apply pushLegal leg (by simp [g,legal])
      intro j h;rcases List.mem_cons.mp h with rfl|h
      · exact ha.1
      · have e : j=i := by simpa [g] using h
        exact e ▸ hi.1
    · simpa [←List.append_assoc,countG,g,binCost] using cost
    · have h:=pushObs ha hi false
      simpa [G,g,AllOn,Finset.forall_mem_insert,←List.append_assoc] using h
theorem dnfBuild (E : Family (Fin n)) :
    ∃gs i,legalList n gs ∧ countG gs≤E.card-1 ∧ Obs gs (fun x : Input n => Holds (fun j => x j=true) E) i := by
  classical
  induction E using Finset.induction_on with
  | empty =>
    exact ⟨[],n,by simp [legalList,PEqualNP.MetaComplexity.NestedCover.ReadsBack],by simp [countG],by simpa [Holds] using baseFalse n⟩
  | @insert A E fresh ih =>
    obtain ⟨gs,j,ok,sz,hj⟩:=ih
    obtain ⟨ts,i,ht,cost,hi⟩:=productBuild gs ok A
    let G := gs++ts
    by_cases e : E=∅
    · subst E
      exact ⟨G,i,ht,by simp_all [G],by simpa [Holds,AllOn] using hi⟩
    · have old:=stable hj ts
      let g : Gate := ⟨.or,[i,j]⟩
      refine ⟨G++[g],width n G,?_,?_,?_⟩
      · apply pushLegal ht (by simp [g,legal])
        intro a h;rcases List.mem_cons.mp h with rfl|h
        · exact hi.1
        · have eq : a=j := by simpa [g] using h
          exact eq ▸ old.1
      · have p : 0<E.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr e)
        rw [Finset.card_insert_of_notMem fresh];change countG (G++[g])≤_
        have cg : countG (G++[g])=countG G+1 := by simp [countG,g,binCost]
        rw [cg];change countG G=countG gs at cost;omega
      · have h:=pushObs hi old true
        simpa [G,g,Holds,AllOn] using h
end PEqualNP.Outside.L_lib_1590_aux

namespace PEqualNP.Outside.L_lib_1590_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open scoped Classical
def Realizes (g : Input n → Bool) (C : Circuit) := Monotone2 C ∧ ReadsBack (n+2) C ∧
    ∃t : Fin (n+2+C.size),∀x : Input n,(C.wires (List.ofFn x++[false,true])).getD t.val false=g x
theorem extractLower {g : Input n → Bool} {C} (real : Realizes g C) (nonc : ∃x y,g x≠g y) :
    minCert g≤charged C+1 ∧ (charged C ≤ minCert g-1 → Form (fun x => g x=true)) := by
  obtain ⟨hm,_,t,ht⟩:=real
  obtain ⟨α,v,r,ts,sz,rank,eq⟩:=circuitRep C hm n
  have ev x : value (v x) (ts.getD t.val none)=g x := by rw [←wireVal,←eq];exact ht x
  obtain ⟨low,form⟩:=necessaryWire rank _ ev nonc
  rw [countEq];exact ⟨by omega,fun h => form (by omega)⟩
theorem minAttained (g : Input n → Bool) : ∃S : Row (Fin n), S.card=minCert g ∧ ZeroCert g S := by
  apply Nat.sInf_mem (s:={b : Nat | ∃S : Row (Fin n),S.card=b ∧ ZeroCert g S})
  refine ⟨_,Finset.univ,rfl,?_⟩
  intro x hx;have eq : x=zeroInput n := funext (fun i => hx i (Finset.mem_univ _))
  rw [eq]
theorem sizeLower {g : Input n → Bool} {E : Family (Fin n)} (proper : Proper E) (sep : Separated E)
    (eq : ∀x,g x=true ↔ Holds (fun i => x i=true) E) : E.card ≤ minCert g := by
  classical
  obtain ⟨S,sz,sc⟩:=minAttained g
  have gz : g (zeroInput n)=false := by
    apply Bool.eq_false_iff.mpr;intro h
    obtain ⟨A,ha,yes⟩:=(eq _).mp h
    obtain ⟨a,mem⟩:=proper A ha
    exact Bool.false_ne_true (yes a mem)
  rw [←sz];apply separatedLower sep;intro A ha
  by_contra! miss
  let x : Input n := fun i => decide (i∈A)
  have zero : ∀i∈S,x i=false := by
    intro i hi;have na : i∉A := fun h => miss i h hi
    simp [x,na]
  have on : Holds (fun i => x i=true) E := ⟨A,ha,fun i h => by simp [x,h]⟩
  have t:=(eq x).mpr on;rw [sc x zero,gz] at t;contradiction
theorem makeReal {g : Input n → Bool} {E : Family (Fin n)} (proper : Proper E) (sep : Separated E)
    (eq : ∀x,g x=true ↔ Holds (fun i => x i=true) E) :
    ∃ C, Realizes g C ∧ charged C ≤ minCert g-1 := by
  obtain ⟨gs,i,ok,sz,obs⟩:=dnfBuild E
  let C : Circuit := ⟨gs,0⟩
  refine ⟨C,⟨ok.1,ok.2,⟨i,obs.1⟩,?_⟩,?_⟩
  · intro x;apply Bool.eq_iff_iff.mpr
    exact (obs.2 x).trans (eq x).symm
  · rw [countEq];have lo:=sizeLower proper sep eq;change countG gs≤_;omega
end PEqualNP.Outside.L_lib_1590_aux

open PEqualNP.Outside.L_lib_1590_aux in
theorem PEqualNP.Outside.L_lib_1590 : letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
∀ (n : Nat) (g : (Fin n → Bool) → Bool), (∃ x y, g x ≠ g y) →
  let zero := fun _ : Fin n => false
  let c := sInf {v : Nat | ∃ S : Finset (Fin n), S.card = v ∧
    ∀ x : Fin n → Bool, (∀ i ∈ S, x i = false) → g x = g zero}
  let realizes := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
    PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    ∃ t : Fin (n+2+C.size), ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x ++ [false,true])).getD t.val false = g x
  let ors := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
    ((Finset.range C.size).filter (fun j =>
      let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C j
      gate.op = .or ∧ gate.inputs.length = 2)).card
  (∀ C, realizes C → c ≤ ors C + 1) ∧
  ((∃ C, realizes C ∧ ors C ≤ c-1) ↔
    ∃ E : Finset (Finset (Fin n)), E.Nonempty ∧ (∀ A ∈ E, A.Nonempty) ∧
      (∀ A ∈ E, ∀ B ∈ E, A ≠ B → Disjoint A B) ∧
      ∀ x : Fin n → Bool, g x = decide (∃ A ∈ E, ∀ j ∈ A, x j = true)) := by
  classical
  intro n g nonc zero c realizes ors
  have ce : c=minCert g := rfl
  have re (C) : realizes C ↔ Realizes g C := Iff.rfl
  have oe (C) : ors C=charged C := by
    apply congrArg Finset.card
    ext j;simp only [ors,charged,Finset.mem_filter]
  constructor
  · intro C ok;rw [ce,oe];exact (extractLower ((re C).mp ok) nonc).1
  · constructor
    · rintro ⟨C,rc,sz⟩
      rw [ce,oe] at sz
      obtain ⟨E,proper,sep,eq⟩:=(extractLower ((re C).mp rc) nonc).2 sz
      have ne : E.Nonempty := by
        by_contra empty
        have em := Finset.not_nonempty_iff_eq_empty.mp empty
        apply pairDiff nonc false
        intro x;apply Bool.eq_false_iff.mpr;intro h
        simpa [em,Holds] using (eq x).mp h
      refine ⟨E,ne,proper,sep,?_⟩
      intro x;apply Bool.eq_iff_iff.mpr
      exact (eq x).trans (@decide_eq_true_iff _ _).symm
    · rintro ⟨E,_,proper,sep,ev⟩
      have e (x) : g x=true ↔ Holds (fun i => x i=true) E := by
        rw [ev x];exact @decide_eq_true_iff (∃ A∈E,∀ j∈A,x j=true) (Classical.propDecidable _)
      obtain ⟨C,rc,sz⟩:=makeReal proper sep e
      exact ⟨C,(re C).mpr rc,by rwa [ce,oe]⟩
