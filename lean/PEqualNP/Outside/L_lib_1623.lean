import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1623_aux
open scoped Classical
def bit (x : Bool) : Nat := if x then 1 else 0
def mass {α : Type} [Fintype α] (c : α → Bool) := ∑i,bit (c i)
theorem countSet {α : Type} [Fintype α] (c : α → Bool) : mass c=(Finset.univ.filter (fun i => c i=true)).card := by simp [mass,bit]
theorem countSum {α β : Type} [Fintype α] [Fintype β] (c : α ⊕ β → Bool) : mass c=mass (fun i => c (.inl i))+mass (fun i => c (.inr i)) := Fintype.sum_sum_type ..
theorem posMass {α : Type} [Fintype α] {c : α → Bool} {i} (h : c i=true) : 1 ≤ mass c := by
  have v:=Finset.single_le_sum (f:=fun j => bit (c j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i);simpa [h,bit,mass] using v
theorem massAll {α : Type} [Fintype α] (c : α → Bool) (h : ∀i,c i=true) : mass c=Fintype.card α := by simp [mass,bit,h]
theorem massExcept {α : Type} [Fintype α] (a : α) : mass (fun i => decide (i≠a))+1=Fintype.card α := by
  classical
  rw [countSet];have e : (Finset.univ.filter (fun i : α => decide (i≠a)=true))=Finset.univ.erase a := by ext;simp
  rw [e];simpa using Finset.card_erase_add_one (Finset.mem_univ a)
theorem nonemptyClique {α : Type} [Fintype α] (c : α → Bool) (cl : ∀a b,a≠b → c a=true ∨ c b=true) :
    mass c+1≥Fintype.card α := by
  classical
  by_cases full : ∀i,c i=true
  · rw [massAll c full];omega
  · obtain ⟨a,na⟩:=Classical.not_forall.mp full
    have e : c=(fun i => decide (i≠a)) := by
      funext i;by_cases ia:i=a
      · subst i;simpa using Bool.eq_false_iff.mpr na
      · simpa [ia] using (cl i a ia).resolve_right na
    rw [e];exact (massExcept a).ge
theorem cliqueDrop {α : Type} [Fintype α] (del col : α → Bool)
    (bip : ∀a b,a≠b → del a=false → del b=false → col a≠col b) : Fintype.card α ≤ mass del+2 := by
  classical
  let remain:=Finset.univ.filter (fun a => del a=false)
  have incl : Set.InjOn col (remain : Set α) := by
    intro a ha b hb eq;by_contra ne
    exact bip a b ne (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 eq
  have size : remain.card≤2 := by
    have bd:=Finset.card_le_card (Finset.subset_univ (remain.image col))
    rw [Finset.card_image_of_injOn incl] at bd;simpa using bd
  have sp:=Finset.card_filter_add_card_filter_not (s:=Finset.univ) (p:=fun a => del a=true)
  rw [countSet];simp only [Fintype.card_ofFinset,Finset.card_univ] at sp
  have eq : (Finset.univ.filter (fun a => ¬del a=true))=remain := by ext;simp [remain]
  rw [eq] at sp;omega
theorem portsMass (c : Fin d × Bool → Bool) :
    mass c=∑j,(bit (c (j,false))+bit (c (j,true))) := by simp [mass,Fintype.sum_prod_type,Nat.add_comm]
theorem portsLower (c : Fin d × Bool → Bool) (ok : ∀j,c (j,false)=true ∨ c (j,true)=true) : d ≤ mass c := by
  have p j : 1≤bit (c (j,false))+bit (c (j,true)) := by rcases ok j with h|h <;> simp [h,bit]
  have sum:=Finset.sum_le_sum (s:=Finset.univ) (fun j _ => p j);simpa [portsMass] using sum
theorem portsUnique (c : Fin d × Bool → Bool) (ok : ∀j,c (j,false)=true ∨ c (j,true)=true)
    (low : mass c≤d) (j : Fin d) : ¬(c (j,false)=true ∧ c (j,true)=true) := by
  rintro ⟨a,b⟩
  have base j : 1≤bit (c (j,false))+bit (c (j,true)) := by rcases ok j with h|h <;> simp [h,bit]
  have strict:=Finset.sum_lt_sum (s:=Finset.univ) (fun j _ => base j) ⟨j,Finset.mem_univ j,by simp [a,b,bit]⟩
  rw [portsMass] at low;simp at strict;omega
end PEqualNP.Outside.L_lib_1623_aux

namespace PEqualNP.Outside.L_lib_1623_aux
open scoped Classical
abbrev X (h : Nat) := Fin h → Bool
abbrev F (h : Nat) := X h → Bool
def width (h : Nat) := h+4
def mult (h : Nat) := 2^(h+3)
def budget (h : Nat) := (2*width h+2)*mult h-1
def total (h : Nat) := (4*width h+2)*mult h
def coreBill (h : Nat) := width h+2^h+2
def coreSize (h : Nat) := 2*width h+2^h+5
def pad (h : Nat) := budget h-coreBill h+1
def extra (h : Nat) := total h-(coreSize h+pad h)
theorem space (h) : coreBill h≤budget h ∧ coreSize h+pad h≤total h := by
  have pow : mult h=8*2^h := by simp [mult,pow_add,Nat.mul_comm]
  have w : 4≤width h := by simp [width]
  have val : 1≤2^h := Nat.one_le_two_pow
  have z : width h ≤ width h*(2^h) := Nat.le_mul_of_pos_right _ (by positivity)
  have a : coreBill h+1 ≤ (2*width h+2)*mult h := by rw [pow];unfold coreBill;nlinarith
  have b : coreSize h+((2*width h+2)*mult h)+1 ≤ total h+coreBill h := by unfold coreSize total coreBill;rw [pow];nlinarith
  unfold budget pad budget;omega
abbrev Ports (h : Nat) := Fin (width h) × Bool
abbrev Code (h : Nat) := Option (X h)
abbrev Hub (h : Nat) := Code h ⊕ Bool
abbrev V (h : Nat) := Ports h ⊕ (Hub h ⊕ (Bool ⊕ (Fin (pad h) ⊕ Fin (extra h))))
abbrev port (z : Ports h) : V h := .inl z
abbrev hub (a : Hub h) : V h := .inr (.inl a)
abbrev leaf (b : Bool) : V h := .inr (.inr (.inl b))
abbrev fill (i : Fin (pad h)) : V h := .inr (.inr (.inr (.inl i)))
abbrev spare (i : Fin (extra h)) : V h := .inr (.inr (.inr (.inr i)))
theorem hubCount (h) : Fintype.card (Hub h)=2^h+3 := by simp [Hub,Code,X]
theorem countV (h) : Fintype.card (V h)=total h := by
  have z:=(space h).2
  simp only [V,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,hubCount,Ports,Fintype.card_option,Fintype.card_fun,Code,X]
  unfold extra coreSize at *;omega
def mark (h : Nat) : Fin (width h) := ⟨h,by simp [width]⟩
def probe (x : X h) (j : Fin (width h)) := if t:j.val<h then x ⟨j.val,t⟩ else decide (j.val=h+1)
theorem markBit (x : X h) : probe x (mark h)=false := by simp [probe,mark]
theorem probeInj {x y : X h} (eq : ∀j,probe x j=probe y j) : x=y := by
  funext i;let j : Fin (width h):=⟨i.val,by have a:=i.isLt;unfold width;omega⟩
  simpa [probe,j,i.isLt] using eq j
def basePin (z : Ports h) := z=(mark h,false)
def need (f : F h) : Code h → Ports h → Prop
  | none,z => basePin z
  | some x,z => if f x then z.2=!(probe x z.1) else basePin z
inductive Edge (f : F h) : V h → V h → Prop
  | ports (j : Fin (width h)) : Edge f (port (j,false)) (port (j,true))
  | clique (a b : Hub h) : a≠b → Edge f (hub a) (hub b)
  | pendant (b : Bool) : Edge f (hub (.inr b)) (leaf b)
  | incident (a : Code h) (z : Ports h) : need f a z → Edge f (hub (.inl a)) (port z)
  | padding (i j : Fin (pad h)) : i≠j → Edge f (fill i) (fill j)
theorem noLoop {f : F h} {u v : V h} (e : Edge f u v) : u≠v := by cases e <;> simp_all
def Covers (f : F h) (c : V h → Bool) := ∀u v,Edge f u v → c u=true ∨ c v=true
theorem parts (c : V h → Bool) :
    mass c=mass (c ∘ port)+mass (c ∘ hub)+mass (c ∘ leaf)+mass (c ∘ fill)+mass (c ∘ spare) := by
  simp only [mass,V,Fintype.sum_sum_type,Function.comp_apply];ac_rfl
end PEqualNP.Outside.L_lib_1623_aux

namespace PEqualNP.Outside.L_lib_1623_aux
open scoped Classical
theorem lowerParts {f : F h} {c} (cv : Covers f c) :
    width h ≤ mass (c ∘ port) ∧ Fintype.card (Hub h) ≤ mass (c ∘ hub)+1 ∧ pad h ≤ mass (c ∘ fill)+1 := by
  refine ⟨portsLower _ (fun j => cv _ _ (.ports j)),nonemptyClique _ (fun a b ne => cv _ _ (.clique a b ne)),?_⟩
  simpa using nonemptyClique (c ∘ fill) (fun a b ne => cv _ _ (.padding a b ne))
theorem budgetEq (h : Nat) : budget h=width h+2^h+2+(pad h-1) := by
  have bound:=(space h).1;unfold coreBill at bound;unfold pad coreBill;omega
theorem coverBound {f : F h} {c} (cv : Covers f c) : budget h ≤ mass c := by
  obtain ⟨p,q,z⟩:=lowerParts cv;rw [hubCount] at q;rw [parts,budgetEq];omega
theorem forced {f : F h} {c} (cv : Covers f c) (cheap : mass c ≤ budget h) :
    (∀j,¬(c (port (j,false))=true ∧ c (port (j,true))=true)) ∧
    ∃a : Code h,c (hub (.inl a))=false := by
  obtain ⟨p,q,z⟩:=lowerParts cv;rw [hubCount] at q
  rw [parts,budgetEq] at cheap
  have sz : mass (c ∘ port)≤width h := by omega
  have noLeaf : mass (c ∘ leaf)=0 := by omega
  have low : mass (c ∘ hub)<Fintype.card (Hub h) := by rw [hubCount];omega
  refine ⟨portsUnique _ (fun j => cv _ _ (.ports j)) sz,?_⟩
  by_contra! none
  have full (a : Hub h) : c (hub a)=true := by
    cases a with
    | inl a => simpa using none a
    | inr b =>
      rcases cv _ _ (.pendant b) with yes|no
      · exact yes
      · have v:=posMass (c:=c ∘ leaf) (i:=b) no;omega
  have eq:=massAll (c ∘ hub) full;omega
theorem readCover {f : F h} {x : X h} {c} (cv : Covers f c) (cheap : mass c ≤ budget h)
    (pins : ∀j,c (port (j,!(probe x j)))=true) : f x=true := by
  obtain ⟨unique,a,miss⟩:=forced cv cheap
  have needOn (z) (hz : need f a z) : c (port z)=true := (cv _ _ (.incident a z hz)).resolve_left (by simp [miss])
  have clash : c (port (mark h,false))≠true := by
    intro eq;exact unique _ ⟨eq,by simpa [markBit] using pins (mark h)⟩
  cases a with
  | none => exact (clash (needOn _ rfl)).elim
  | some y =>
    cases ey:f y with
    | false => exact (clash (needOn _ (by simp [need,ey,basePin]))).elim
    | true =>
      have same j : probe x j=probe y j := by
        have a:=pins j
        have b:=needOn (j,!(probe y j)) (by simp [need,ey])
        have u:=unique j
        cases ex:probe x j <;> cases ep:probe y j <;> simp_all
      rw [probeInj same];exact ey
def firstFill (h : Nat) : Fin (pad h) := ⟨0,by simp [pad]⟩
def canon (choice : Fin (width h) → Bool) (root : Option (Code h)) : V h → Bool :=
  Sum.elim (fun z => decide (z.2=choice z.1))
    (Sum.elim (fun a => decide (root.map Sum.inl ≠ some a))
    (Sum.elim (fun _ => false) (Sum.elim (fun i => decide (i≠firstFill h)) (fun _ => false))))
theorem canonOK {f : F h} (choice : Fin (width h) → Bool) (root : Option (Code h))
    (adm : ∀a,root=some a → ∀z,need f a z → z.2=choice z.1) : Covers f (canon choice root) := by
  intro _ _ e;cases e with
  | ports j => cases eq:choice j <;> simp [canon,eq]
  | clique a b ne => simp [canon];grind
  | padding a b ne => simp [canon];grind
  | pendant b => cases root <;> simp [canon]
  | incident a z hz =>
    cases root with
    | none => simp [canon]
    | some b =>
      by_cases e:b=a
      · subst b;exact Or.inr (by simp [canon,adm _ rfl _ hz])
      · exact Or.inl (by simp [canon,e])
theorem exceptCost {α : Type} [Fintype α] (c : α → Bool) (a : α) (law : ∀v,c v=true ↔ v≠a) : mass c+1=Fintype.card α := by
  classical
  rw [countSet]
  have eq : (Finset.univ.filter (fun v => c v=true))=Finset.univ.erase a := by ext v;simp [law]
  rw [eq];simpa using Finset.card_erase_add_one (Finset.mem_univ a)
theorem massCanon (choice : Fin (width h) → Bool) (root : Option (Code h)) :
    mass (canon choice root)=budget h+(if root.isNone then 1 else 0) := by
  rw [parts,budgetEq]
  have portCost : mass (canon choice root ∘ port)=width h := by
    rw [portsMass];have one j : bit ((canon choice root ∘ port) (j,false))+bit ((canon choice root ∘ port) (j,true))=1 := by
      cases e:choice j <;> simp [canon,bit,e]
    calc
      _ = ∑ _j : Fin (width h),1 := Finset.sum_congr rfl (fun j _ => one j)
      _ = _ := by simp
  have lc : mass (canon choice root ∘ leaf)=0 := by simp [mass,bit,canon]
  have sc : mass (canon choice root ∘ spare)=0 := by simp [mass,bit,canon]
  have fc:=exceptCost (canon choice root ∘ fill) (firstFill h) (fun i => by simp [canon])
  rw [Fintype.card_fin] at fc;rw [portCost,lc,sc]
  cases root with
  | none =>
    have hc:=massAll (canon choice (.none : Option (Code h)) ∘ hub) (fun _ => by simp [canon])
    rw [hubCount] at hc
    change _=width h+2^h+2+(pad h-1)+1
    omega
  | some a =>
    have hc:=exceptCost (canon choice (some a) ∘ hub) (Sum.inl a) (fun v => by simp [canon,ne_comm])
    rw [hubCount] at hc
    change _=width h+2^h+2+(pad h-1)+0
    omega
end PEqualNP.Outside.L_lib_1623_aux

namespace PEqualNP.Outside.L_lib_1623_aux
open scoped Classical
def Bip (f : F h) (del col : V h → Bool) :=
  ∀u v,Edge f u v → del u=false → del v=false → col u≠col v
def newDel (del : V h → Bool) : V h → Bool :=
  Sum.elim (del ∘ port) (Sum.elim (Sum.elim (fun _ => true) (fun _ => false))
    (Sum.elim (fun _ => false) (Sum.elim (del ∘ fill) (del ∘ spare))))
def newCol (col : V h → Bool) : V h → Bool :=
  Sum.elim (col ∘ port) (Sum.elim (Sum.elim (fun _ => false) id)
    (Sum.elim Bool.not (Sum.elim (col ∘ fill) (col ∘ spare))))
theorem replaceBip {f : F h} {del col : V h → Bool} (ok : Bip f del col) (g : F h) : Bip g (newDel del) (newCol col) := by
  intro u v e du dv;cases e with
  | ports j => exact ok _ _ (.ports j) du dv
  | padding i j h => exact ok _ _ (.padding i j h) du dv
  | incident a z _ => contradiction
  | pendant b => cases b <;> simp [newCol]
  | clique a b ne =>
    cases a with
    | inl _ => contradiction
    | inr a => cases b with
      | inl _ => contradiction
      | inr b => exact fun e => ne (congrArg Sum.inr e)
theorem cheaperBip {f : F h} {del col : V h → Bool} (ok : Bip f del col) : mass (newDel del) ≤ mass del := by
  have d:=cliqueDrop (del ∘ hub) (col ∘ hub) (fun a b ne ha hb => ok _ _ (.clique a b ne) ha hb)
  have cnt : mass (newDel del ∘ hub)=Fintype.card (Code h) := by
    unfold mass;simp [Fintype.sum_sum_type,newDel,bit]
  have lc : mass (newDel del ∘ leaf)=0 := by simp [mass,newDel,bit]
  rw [parts,parts del,cnt,lc]
  change mass (del ∘ port)+Fintype.card (Code h)+0+mass (del ∘ fill)+mass (del ∘ spare) ≤ _
  simp only [Hub,Fintype.card_sum,Fintype.card_bool] at d;omega
end PEqualNP.Outside.L_lib_1623_aux

namespace PEqualNP.Outside.L_lib_1623_aux
open scoped Classical
noncomputable def paint {α β : Type} [Fintype α] (e : α ≃ β) (c : α → Bool) := (Finset.univ.filter (fun a => c a=true)).map e.toEmbedding
noncomputable def read {α β : Type} (e : α ≃ β) (C : Finset β) (a : α) := decide (e a∈C)
theorem painted {α β : Type} [Fintype α] (e : α ≃ β) (c : α → Bool) (v : α) : e v∈paint e c ↔ c v=true := by simp [paint]
theorem paintSize {α β : Type} [Fintype α] (e : α ≃ β) (c : α → Bool) : (paint e c).card=mass c := by simp [paint,countSet]
theorem readYes {α β : Type} (e : α ≃ β) (C : Finset β) (a : α) : read e C a=true ↔ e a∈C := by simp [read]
theorem readNo {α β : Type} (e : α ≃ β) (C : Finset β) (a : α) : read e C a=false ↔ e a∉C := by simp [read]
theorem readSize {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (C : Finset β) : mass (read e C)=C.card := by
  classical
  have eq : paint e (read e C)=C := by ext i;obtain ⟨a,rfl⟩:=e.surjective i;rw [painted,readYes]
  rw [←paintSize e,eq]
noncomputable def numbering (h) := Fintype.equivFinOfCardEq (countV h)
noncomputable def edges (e : V h ≃ Fin N) (f : F h) := Finset.univ.filter (fun t : Fin N × Fin N => t.1<t.2 ∧
  (Edge f (e.symm t.1) (e.symm t.2) ∨ Edge f (e.symm t.2) (e.symm t.1)))
theorem ordered (e : V h ≃ Fin N) (f : F h) : ∀t∈edges e f,t.1<t.2 := fun _ h => (Finset.mem_filter.mp h).2.1
theorem rules (e : V h ≃ Fin N) (f : F h) (P : Fin N → Fin N → Prop) (sym : ∀i j,P i j → P j i) :
    (∀t∈edges e f,P t.1 t.2) ↔ ∀u v,Edge f u v → P (e u) (e v) := by
  constructor
  · intro all u v edge
    have ne : e u≠e v := fun eq => noLoop edge (e.injective eq)
    rcases lt_or_gt_of_ne ne with lt|gt
    · apply all (e u,e v);simp [edges,lt,edge]
    · apply sym;apply all (e v,e u);simp [edges,gt,edge]
  · intro all t ht;obtain ⟨_,x|x⟩:=(Finset.mem_filter.mp ht).2
    · simpa using all _ _ x
    · apply sym;simpa using all _ _ x
def inc {α β : Type} (e : α ≃ β) (t : Nat) := e.sumCongr (Equiv.refl (Fin t))
theorem incL {α β : Type} (e : α ≃ β) (u : α) : inc e t (Sum.inl u)=Sum.inl (e u) := rfl
theorem incR {α β : Type} (e : α ≃ β) (j : Fin t) : inc e t (Sum.inr j)=Sum.inr j := rfl
end PEqualNP.Outside.L_lib_1623_aux

namespace PEqualNP.Outside.L_lib_1623_aux
open scoped Classical
theorem opposite (a b : Bool) : (a=true ↔ b≠true) ↔ a≠b := by cases a <;> cases b <;> decide
def Oct (e : V h ≃ Fin N) (f : F h) (t) (J : Finset ((Ports h ⊕ Fin t) × (Ports h ⊕ Fin t))) (B : Nat) :=
  let attach := Sum.map (fun z => e (port z)) (id : Fin t → Fin t)
  ∃T S : Finset (Fin N ⊕ Fin t),T.card≤B ∧
    (∀a∈edges e f,Sum.inl a.1∉T → Sum.inl a.2∉T → (Sum.inl a.1∈S ↔ Sum.inl a.2∉S)) ∧
    ∀a∈J,attach a.1∉T → attach a.2∉T → (attach a.1∈S ↔ attach a.2∉S)
theorem normalized (e : V h ≃ Fin N) (f : F h) (T S : Finset (Fin N ⊕ Fin t)) :
    (∀a∈edges e f,Sum.inl a.1∉T → Sum.inl a.2∉T → (Sum.inl a.1∈S ↔ Sum.inl a.2∉S)) ↔
    Bip f (fun u => read (inc e t) T (Sum.inl u)) (fun u => read (inc e t) S (Sum.inl u)) := by
  let P (i j : Fin N) := Sum.inl i∉T → Sum.inl j∉T → (Sum.inl i∈S ↔ Sum.inl j∉S)
  have sym i j : P i j → P j i := by unfold P;tauto
  rw [rules e f P sym];unfold Bip P
  simp only [readNo,incL];constructor
  · intro rule u v ed hu hv
    exact (opposite _ _).mp (((readYes _ _ _).trans (rule u v ed hu hv)).trans (not_congr (readYes _ _ _)).symm)
  · intro rule u v ed hu hv
    have law:=(opposite _ _).mpr (rule u v ed hu hv)
    exact ((readYes _ _ _).symm.trans law).trans (not_congr (readYes _ _ _))
theorem octMove (e : V h ≃ Fin N) (f g : F h) {t J B} (ok : Oct e f t J B) : Oct e g t J B := by
  classical
  obtain ⟨T,S,sz,core,edge⟩:=ok
  let k:=inc e t
  let d u := read k T (.inl u)
  let col u := read k S (.inl u)
  let de (x : Fin t) := read k T (.inr x)
  let ce (x : Fin t) := read k S (.inr x)
  have bip : Bip f d col := (normalized e f T S).mp core
  let d' : V h ⊕ Fin t → Bool := Sum.elim (newDel d) de
  let s' : V h ⊕ Fin t → Bool := Sum.elim (newCol col) ce
  have pulled (w : V h ⊕ Fin t → Bool) (z) : read k (paint k w) z=w z := by
    apply Bool.eq_iff_iff.mpr;rw [readYes,painted]
  refine ⟨paint k d',paint k s',?_,?_,?_⟩
  · rw [paintSize,countSum];have cost:=readSize k T;rw [countSum] at cost
    change mass d+mass de=T.card at cost;change mass (newDel d)+mass de≤B
    have less:=cheaperBip bip;omega
  · apply (normalized e g _ _).mpr
    change Bip g (fun u => read k (paint k d') (.inl u)) (fun u => read k (paint k s') (.inl u))
    simp only [pulled];exact replaceBip bip g
  · let ins := Sum.map (fun z : Ports h => e (port z)) (id : Fin t → Fin t)
    have dt (z) : ins z∈paint k d' ↔ ins z∈T := by
      cases z with
      | inl z => change k (.inl (port z))∈paint k d' ↔ _;rw [painted];exact readYes k T _
      | inr j => change k (.inr j)∈paint k d' ↔ _;rw [painted];exact readYes k T _
    have st (z) : ins z∈paint k s' ↔ ins z∈S := by
      cases z with
      | inl z => change k (.inl (port z))∈paint k s' ↔ _;rw [painted];exact readYes k S _
      | inr j => change k (.inr j)∈paint k s' ↔ _;rw [painted];exact readYes k S _
    intro a ha;change ins a.1∉paint k d' → ins a.2∉paint k d' → (ins a.1∈paint k s' ↔ ins a.2∉paint k s')
    simp only [dt,st];exact edge _ ha
end PEqualNP.Outside.L_lib_1623_aux

namespace PEqualNP.Outside.L_lib_1623_aux
open scoped Classical
def Query (e : V h ≃ Fin N) (f : F h) (x : X h) (t : Nat) (p : Fin (width h) → Fin t) (B : Nat) :=
  ∃ C : Finset (Fin N ⊕ Fin t),C.card≤B ∧
    (∀a∈edges e f,Sum.inl a.1∈C ∨ Sum.inl a.2∈C) ∧
    ∀j,Sum.inl (e (port (j,!(probe x j))))∈C ∨ Sum.inr (p j)∈C
theorem lowCover (e : V h ≃ Fin N) (f : F h) (B : Nat) :
    (∃C : Finset (Fin N),C.card≤B ∧ ∀a∈edges e f,a.1∈C ∨ a.2∈C) ↔ budget h≤B := by
  have toCore (C : Finset (Fin N)) : (∀a∈edges e f,a.1∈C ∨ a.2∈C) ↔ Covers f (read e C) := by
    rw [rules e f (fun i j => i∈C ∨ j∈C) (fun _ _ v => v.symm)]
    simp only [Covers,readYes]
  constructor
  · rintro ⟨C,sz,ok⟩;have h:=coverBound ((toCore C).mp ok);rw [readSize] at h;omega
  · intro b
    let c:=canon (h:=h) (fun _ => false) (some none)
    have cv : Covers f c := by
      apply canonOK;intro a eq z hz
      have ez : a=none := Option.some.inj eq.symm
      subst a;change z=(mark h,false) at hz;rw [hz]
    have eq : mass c=budget h := by simpa [c] using massCanon (h:=h) (fun _ => false) (some none)
    have rd : read e (paint e c)=c := by funext u;apply Bool.eq_iff_iff.mpr;rw [readYes,painted]
    exact ⟨paint e c,by rw [paintSize,eq];exact b,(toCore _).mpr (by rw [rd];exact cv)⟩
theorem queryUpper (e : V h ≃ Fin N) {f : F h} {x : X h} (t) (p : Fin (width h) → Fin t) {B}
    (c : V h → Bool) (cv : Covers f c) (bill : mass c≤B) (pins : ∀j,c (port (j,!(probe x j)))=true) : Query e f x t p B := by
  let k:=inc e t
  let set : V h ⊕ Fin t → Bool := Sum.elim c (fun _ => false)
  let C:=paint k set
  refine ⟨C,?_,?_,?_⟩
  · rw [paintSize,countSum];change mass c+mass (fun _ : Fin t => false)≤B;simpa [mass,bit] using bill
  · apply (rules e f (fun i j => Sum.inl i∈C ∨ Sum.inl j∈C) (fun _ _ h => h.symm)).mpr
    intro u v edge;change k (.inl u)∈paint k set ∨ k (.inl v)∈paint k set
    rw [painted,painted];exact cv u v edge
  · intro j;apply Or.inl;change k (.inl _)∈paint k set;rw [painted];exact pins j
theorem readQuery (e : V h ≃ Fin N) (f : F h) (x : X h) (t) (p : Fin (width h) → Fin t) :
    (Query e f x t p (budget h) ↔ f x=true) ∧ Query e f x t p (budget h+1) := by
  let choice j:= !(probe x j)
  have construct (root : Option (Code h)) (ok : ∀a,root=some a → ∀z,need f a z → z.2=choice z.1) :
      Query e f x t p (budget h+if root.isNone then 1 else 0) := by
    apply queryUpper e t p (canon choice root) (canonOK choice root ok) (massCanon choice root).le
    intro j;simp [canon,choice]
  refine ⟨⟨?_,?_⟩,by simpa using construct none (by simp)⟩
  · rintro ⟨C,sz,ok,matchPin⟩
    let k:=inc e t
    let c (u : V h) := read k C (.inl u)
    let ext (v : Fin t) := read k C (.inr v)
    have raw:=(rules e f (fun i j => Sum.inl i∈C ∨ Sum.inl j∈C) (fun _ _ h => h.symm)).mp ok
    have cv : Covers f c := by
      intro u v edge;change read k C (.inl u)=true ∨ read k C (.inl v)=true
      rw [readYes,readYes];exact raw u v edge
    have cost:=readSize k C;rw [countSum] at cost;change mass c+mass ext=C.card at cost
    have b:=coverBound cv
    apply readCover cv (by omega)
    intro j;rcases matchPin j with l|r
    · exact (readYes k C _).mpr l
    · have on : ext (p j)=true := (readYes k C _).mpr r
      have v:=posMass on;omega
  · intro yes
    apply (show Query e f x t p (budget h+0) → Query e f x t p (budget h) from id)
    apply construct (some (some x))
    intro a eq z hz;have id : a=some x := Option.some.inj eq.symm;subst a
    simpa [need,yes,choice] using hz
end PEqualNP.Outside.L_lib_1623_aux

open PEqualNP.Outside.L_lib_1623_aux in
theorem PEqualNP.Outside.L_lib_1623 : (
  letI : ∀ q : Prop, Decidable q := Classical.propDecidable
  ∀ h : Nat,
  let X := Fin h → Bool
  let F := X → Bool
  let d := h+4
  let M := 2^(d-1)
  let n := (4*d+2)*M
  let K := (2*d+2)*M-1
  let D := Fin d × Bool
  let probe := fun (x : X) (j : Fin d) =>
    if t : j.val < h then x ⟨j.val,t⟩ else decide (j.val=h+1)
  ∃ (s : D → Fin n) (G : F → Finset (Fin n × Fin n)),
    let oct := fun (f : F) (t : Nat) (J : Finset ((D ⊕ Fin t) × (D ⊕ Fin t))) (B : Nat) =>
      let inc := Sum.map s (id : Fin t → Fin t)
      ∃ T S : Finset (Fin n ⊕ Fin t), T.card ≤ B ∧
        (∀ e ∈ G f, Sum.inl e.1 ∉ T → Sum.inl e.2 ∉ T →
          (Sum.inl e.1 ∈ S ↔ Sum.inl e.2 ∉ S)) ∧
        (∀ e ∈ J, inc e.1 ∉ T → inc e.2 ∉ T → (inc e.1 ∈ S ↔ inc e.2 ∉ S))
    let query := fun (f : F) (x : X) (t : Nat) (p : Fin d → Fin t) (B : Nat) =>
      ∃ C : Finset (Fin n ⊕ Fin t), C.card ≤ B ∧
        (∀ e ∈ G f, Sum.inl e.1 ∈ C ∨ Sum.inl e.2 ∈ C) ∧
        ∀ j, Sum.inl (s (j, !(probe x j))) ∈ C ∨ Sum.inr (p j) ∈ C
    Function.Injective s ∧
    (∀ f, (∀ e ∈ G f, e.1 < e.2) ∧ ∀ B : Nat,
      (∃ C : Finset (Fin n), C.card ≤ B ∧ ∀ e ∈ G f, e.1 ∈ C ∨ e.2 ∈ C) ↔ K ≤ B) ∧
    (∀ f g t (J : Finset ((D ⊕ Fin t) × (D ⊕ Fin t))), (∀ e ∈ J, e.1 ≠ e.2) →
      ∀ B, oct f t J B ↔ oct g t J B) ∧
    (∀ f x t (p : Fin d → Fin t), (query f x t p K ↔ f x=true) ∧ query f x t p (K+1)) ∧
    ∀ (b : Nat) (enc : F → (Fin b → Bool)) (ans : (Fin b → Bool) → X → Bool),
      (∀ f x, ans (enc f) x=true ↔ query f x d id K) → 2^h ≤ b
) := by
  classical
  intro h X' F' d M n K D prob
  have dEq : d=width h := rfl
  have mEq : M=mult h := by simp [M,d,mult]
  have nEq : n=total h := by simp only [n,dEq,mEq,total]
  have kEq : K=budget h := by simp only [K,dEq,mEq,budget]
  let e : V h ≃ Fin n := (numbering h).trans (Equiv.cast (congrArg Fin nEq.symm))
  let s (z : D) := e (port z)
  let G (f : F') := edges e f
  refine ⟨s,G,?_⟩
  intro oct query
  have pe (x : X') (j : Fin d) : prob x j=probe x j := by
    by_cases small:j.val<h <;> simp [prob,probe,small]
  have oe (f : F') (t) (J) (B) : oct f t J B ↔ Oct e f t J B := Iff.rfl
  have qe (f : F') (x : X') (t) (p) (B) : query f x t p B ↔ Query e f x t p B := by
    simp only [query,Query,pe,s,G];rfl
  refine ⟨fun z t eq => Sum.inl.inj (e.injective eq),?_,?_,?_,?_⟩
  · intro f;refine ⟨ordered e f,?_⟩;intro B;rw [kEq];exact lowCover e f B
  · intro f g t J _ B;rw [oe,oe];exact ⟨octMove e f g,octMove e g f⟩
  · intro f x t p;rw [qe,qe,kEq];exact readQuery e f x t p
  · intro b enc ans law
    have inject : Function.Injective enc := by
      intro f g eq;funext x;apply Bool.eq_iff_iff.mpr
      have ev (a : F') : query a x d id K ↔ a x=true := (qe a x d id K).trans (by rw [kEq];exact (readQuery e a x d id).1)
      calc
        f x=true ↔ ans (enc f) x=true := (ev f).symm.trans (law f x).symm
        _ ↔ ans (enc g) x=true := by rw [eq]
        _ ↔ g x=true := (law g x).trans (ev g)
    have card:=Fintype.card_le_of_injective enc inject
    change Fintype.card ((Fin h → Bool) → Bool) ≤ Fintype.card (Fin b → Bool) at card
    simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool] at card
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp card
