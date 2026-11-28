import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1557_aux
open scoped Classical
abbrev Bits (k : Nat) := Finset (Fin k)
def covers (G : Finset (Fin n × Fin n)) (C : Bits n) := ∀e∈G,e.1∈C ∨ e.2∈C
def view (p : Fin k → Fin n) (C : Bits n) := Finset.univ.filter (fun i => p i∈C)
def feasible (G : Finset (Fin n × Fin n)) (I O : Bits n) (C : Bits n) := covers G C ∧ I⊆C ∧ Disjoint C O
def mix (D A X Y : Bits n) := (X∩(D∪A))∪(Y\(D∪A))
def pattern (D C : Bits n) := C∩D
theorem mixLeft {D A X Y : Bits n} {i} (h : i∈D ∨ i∈A) : i∈mix D A X Y ↔ i∈X := by
  simp only [mix,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff];tauto
theorem mixRight {D A X Y : Bits n} {i} (eq : pattern D X=pattern D Y) (h : i∈D ∨ i∉A) : i∈mix D A X Y ↔ i∈Y := by
  have same : i∈D → (i∈X ↔ i∈Y) := by
    intro hi;have hh:=Finset.ext_iff.mp eq i;simpa [pattern,hi] using hh
  simp only [mix,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff];tauto
theorem mixFeasible {D A I O X Y : Bits n} {G : Finset (Fin n × Fin n)}
    (cuts : ∀e∈G,e.1∉D → e.2∉D → (e.1∈A ↔ e.2∈A))
    (hx : feasible G I O X) (hy : feasible G I O Y) (eq : pattern D X=pattern D Y) :
    feasible G I O (mix D A X Y) := by
  refine ⟨?_,?_,?_⟩
  · intro e he
    by_cases l : (e.1∈D ∨ e.1∈A) ∧ (e.2∈D ∨ e.2∈A)
    · exact (hx.1 e he).imp (mixLeft l.1).mpr (mixLeft l.2).mpr
    have r : (e.1∈D ∨ e.1∉A) ∧ (e.2∈D ∨ e.2∉A) := by
      have h:=cuts e he;tauto
    exact (hy.1 e he).imp (mixRight eq r.1).mpr (mixRight eq r.2).mpr
  · intro a ha;by_cases h : a∈A
    · exact (mixLeft (Or.inr h)).mpr (hx.2.1 ha)
    · exact (mixRight eq (Or.inr h)).mpr (hy.2.1 ha)
  · apply Finset.disjoint_left.mpr;intro a ha hO;by_cases h : a∈A
    · exact Finset.disjoint_left.mp hx.2.2 ((mixLeft (Or.inr h)).mp ha) hO
    · exact Finset.disjoint_left.mp hy.2.2 ((mixRight eq (Or.inr h)).mp ha) hO
theorem mixPrice (w : Fin n → Nat) (D A X Y : Bits n) :
    (mix D A X Y).sum w=(X∩(D∪A)).sum w+(Y\(D∪A)).sum w := by
  apply Finset.sum_union;apply Finset.disjoint_left.mpr;intro i h k;exact (Finset.mem_sdiff.mp k).2 (Finset.mem_inter.mp h).2
theorem dividePrice (w : Fin n → Nat) (D A X : Bits n) :
    (X∩(D∪A)).sum w+(X\(D∪A)).sum w=X.sum w := by rw [←mixPrice];congr 1;ext;simp [mix]
theorem mixViews {D A X Y : Bits n} {p : Fin k → Fin n} {q : Fin l → Fin n}
    (left : ∀i,p i∈D ∨ p i∈A) (right : ∀j,q j∈D ∨ q j∉A) (eq : pattern D X=pattern D Y) :
    view p (mix D A X Y)=view p X ∧ view q (mix D A X Y)=view q Y := by
  constructor
  · ext i;simp [view,mixLeft (left i)]
  · ext i;simp [view,mixRight eq (right i)]
noncomputable def best {α : Type} [Fintype α] (ok : α → Prop) (val : α → Nat) (fallback : Nat) :=
  if ex : ∃a,ok a then Nat.find (show ∃ k,∃a,ok a ∧ val a=k by obtain ⟨a,ha⟩:=ex;exact ⟨_,a,ha,rfl⟩) else fallback
theorem bestLe {α : Type} [Fintype α] (ok : α → Prop) (val : α → Nat) (limit) {a} (ha : ok a) :
    best ok val limit ≤ val a := by
  classical
  unfold best;rw [dif_pos (show ∃a,ok a from ⟨a,ha⟩)];exact Nat.find_min' _ ⟨a,ha,rfl⟩
theorem bestCases {α : Type} [Fintype α] (ok : α → Prop) (val : α → Nat) (limit) :
    best ok val limit=limit ∨ ∃a,ok a ∧ val a=best ok val limit := by
  classical
  unfold best;split
  · exact Or.inr (Nat.find_spec (p:=fun k => ∃a,ok a ∧ val a=k) _)
  · exact Or.inl rfl
end PEqualNP.Outside.L_lib_1557_aux
namespace PEqualNP.Outside.L_lib_1557_aux
open scoped Classical
def Realizes (n h : Nat) (u : Fin k → Nat) (v : Fin l → Nat) (F : Bits k → Bits l → Nat) :=
  ∃ (G : Finset (Fin n × Fin n)) (w : Fin n → Nat) (D A I O : Bits n) (p : Fin k → Fin n) (q : Fin l → Fin n) (c : Nat),
    D.card≤h ∧ Function.Injective p ∧ Function.Injective q ∧
    (∀i,p i∈A ∧ p i∉D ∧ w (p i)=u i) ∧ (∀j,q j∉A ∧ q j∉D ∧ w (q j)=v j) ∧
    (∀a∈G,a.1∉D → a.2∉D → (a.1∈A ↔ a.2∈A)) ∧
    ∀X Y b,c+F X Y≤b ↔ ∃C,feasible G I O C ∧ C.sum w≤b ∧ view p C=X ∧ view q C=Y
def Fac (h : Nat) (F : Bits k → Bits l → Nat) :=
  ∃ (a : Fin (2^h) → Bits k → Int) (t : Fin (2^h) → Bits l → Int),
    ∀ X Y,(∀i,(F X Y:Int)≤a i X+t i Y) ∧ ∃i,(F X Y:Int)=a i X+t i Y
def Admiss (u : Fin k → Nat) (v : Fin l → Nat) (F : Bits k → Bits l → Nat) :=
  (∀X Y i,F (insert i X) Y≤F X Y+u i) ∧ ∀X Y j,F X (insert j Y)≤F X Y+v j
end PEqualNP.Outside.L_lib_1557_aux
namespace PEqualNP.Outside.L_lib_1557_aux
open scoped Classical
theorem insertBound {α : Type} [DecidableEq α] (F : Finset α → Nat) (u : α → Nat)
    (one : ∀X i,F (insert i X)≤F X+u i) {U X : Finset α} (sub : U⊆X) :
    F X+U.sum u≤F U+X.sum u := by
  classical
  have step (T : Finset α) (dis : Disjoint U T) : F (U∪T)≤F U+T.sum u := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert i T out ih =>
      have off:=Finset.disjoint_insert_right.mp dis
      have prev:=ih off.2
      have next:=one (U∪T) i
      rw [Finset.union_insert,Finset.sum_insert out]
      calc
        _ ≤ F (U∪T)+u i := next
        _ ≤ (F U+T.sum u)+u i := Nat.add_le_add_right prev _
        _ = _ := by ac_rfl
  have diff:=step (X\U) (Finset.disjoint_sdiff)
  have joint : U∪(X\U)=X := by ext i;simp;grind
  have cost : U.sum u+(X\U).sum u=X.sum u := by rw [←Finset.sum_union Finset.disjoint_sdiff,joint]
  rw [joint] at diff;omega
theorem wholeBound {u : Fin k → Nat} {v : Fin l → Nat} {F : Bits k → Bits l → Nat}
    (ad : Admiss u v F) {U X : Bits k} {V Y : Bits l} (lx : U⊆X) (ly : V⊆Y) :
    F X Y+U.sum u+V.sum v≤F U V+X.sum u+Y.sum v := by
  have a:=insertBound (fun x => F x Y) u (fun x i => ad.1 x Y i) lx
  have b:=insertBound (fun y => F U y) v (fun y j => ad.2 U y j) ly
  omega
def maxCost {α : Type} [Fintype α] (f : α → Int) := Finset.univ.sup (fun x => (f x).natAbs)
theorem absLe {α : Type} [Fintype α] (f : α → Int) (a) : -((maxCost f : Nat):Int)≤f a ∧ f a≤(maxCost f : Int) := by
  have h:=Finset.le_sup (s:=Finset.univ) (f:=fun x => (f x).natAbs) (Finset.mem_univ a)
  change (f a).natAbs ≤ maxCost f at h;omega
theorem cutPenalty {h : Nat} (Z Zl Zr : Bits h) (a b : Int) (cap : Nat) (target : Nat)
    (left : Zl⊆Z) (right : Zr⊆Z) (bound : (target:Int)-a-b≤cap)
    (tight : Zl=Z → Zr=Z → (target:Int)≤a+b) :
    (target:Int)≤a+b+(cap:Int)*(2*Z.card-Zl.card-Zr.card) := by
  by_cases eq:Zl=Z ∧ Zr=Z
  · obtain ⟨rfl,rfl⟩:=eq;have le:=tight rfl rfl;linarith
  have l:=Finset.card_le_card left;have r:=Finset.card_le_card right
  have ne : Zl.card<Z.card ∨ Zr.card<Z.card := by
    by_contra! bad;exact eq ⟨Finset.eq_of_subset_of_card_le left bad.1,Finset.eq_of_subset_of_card_le right bad.2⟩
  have diff : (1:Int)≤2*(Z.card:Int)-Zl.card-Zr.card := by omega
  have penalty:=mul_le_mul_of_nonneg_left diff (Int.natCast_nonneg cap)
  linarith
end PEqualNP.Outside.L_lib_1557_aux
namespace PEqualNP.Outside.L_lib_1557_aux
open scoped Classical
abbrev Choice (h k : Nat) := Bits h × Bits k
abbrev Shore (h k : Nat) := Fin k ⊕ Choice h k
abbrev Vtx (h k l : Nat) := Fin h ⊕ (Shore h k ⊕ Shore h l)
def shoreEdge : Shore h k → Shore h k → Prop
  | .inl i,.inr a => i∈a.2
  | .inr a,.inr b => a≠b
  | _,_ => False
def tagEdge (i : Fin h) : Shore h k → Prop
  | .inr a => i∈a.1
  | _ => False
def graphRel : Vtx h k l → Vtx h k l → Prop
  | .inl i,.inr (.inl a) => tagEdge i a
  | .inl i,.inr (.inr a) => tagEdge i a
  | .inr (.inl a),.inr (.inl b) => shoreEdge a b
  | .inr (.inr a),.inr (.inr b) => shoreEdge a b
  | _,_ => False
def shoreMember (X : Bits k) (a : Choice h k) : Shore h k → Bool :=
  Sum.elim (fun i => decide (i∈X)) (fun b => decide (b≠a))
def member (Z : Bits h) (X : Bits k) (Y : Bits l) (a : Choice h k) (b : Choice h l) : Vtx h k l → Bool :=
  Sum.elim (fun i => decide (i∈Z)) (Sum.elim (shoreMember X a) (shoreMember Y b))
theorem shoreCovered {X : Bits k} {a : Choice h k} (sub : a.2⊆X) {x y : Shore h k} (r : shoreEdge x y) :
    shoreMember X a x=true ∨ shoreMember X a y=true := by
  cases x with
  | inl i => cases y with
    | inl j => exact False.elim r
    | inr b => by_cases e:b=a
               · subst b;exact Or.inl (decide_eq_true (sub r))
               · exact Or.inr (decide_eq_true e)
  | inr b => cases y with
    | inl i => exact False.elim r
    | inr c => by_cases e:b=a
               · subst b;exact Or.inr (decide_eq_true (Ne.symm r))
               · exact Or.inl (decide_eq_true e)
theorem tagCovered {Z : Bits h} {X : Bits k} {a : Choice h k} (sub : a.1⊆Z) {i} {x} (r : tagEdge i x) :
    i∈Z ∨ shoreMember X a x=true := by
  cases x with
  | inl v => exact False.elim r
  | inr b => by_cases e:b=a
             · subst b;exact Or.inl (sub r)
             · exact Or.inr (decide_eq_true e)
theorem memberCovers {Z : Bits h} {X : Bits k} {Y : Bits l} {a : Choice h k} {b : Choice h l}
    (aZ : a.1⊆Z) (aX : a.2⊆X) (bZ : b.1⊆Z) (bY : b.2⊆Y) (x y : Vtx h k l) (r : graphRel x y) :
    member Z X Y a b x=true ∨ member Z X Y a b y=true := by
  cases x with
  | inl i => cases y with
    | inl _ => exact False.elim r
    | inr y => cases y with
      | inl y => exact (tagCovered (X:=X) (x:=y) aZ r).imp decide_eq_true id
      | inr y => exact (tagCovered (X:=Y) (x:=y) bZ r).imp decide_eq_true id
  | inr x => cases y with
    | inl _ => cases x <;> exact False.elim r
    | inr y => cases x <;> cases y <;> first | exact False.elim r | exact shoreCovered aX r | exact shoreCovered bY r
theorem cardVtx (h k l : Nat) : Fintype.card (Vtx h k l)=k+l+h+2^h*(2^k+2^l) := by simp [Vtx,Shore,Choice,Bits];ring
end PEqualNP.Outside.L_lib_1557_aux
namespace PEqualNP.Outside.L_lib_1557_aux
open scoped Classical
def bankBits (b : Fin k → Bool) := Finset.univ.filter (fun i => b i=true)
theorem dominate {Z : Bits h} (c : Shore h k → Bool)
    (hc : ∀x y,shoreEdge x y → c x=true ∨ c y=true)
    (sel : ∀i x,tagEdge i x → i∈Z ∨ c x=true) :
    let X:=bankBits (fun i => c (.inl i))
    ∃a : Choice h k,a.1⊆Z ∧ a.2⊆X ∧ ∀x,shoreMember X a x=true → c x=true := by
  intro X
  by_cases skip:∃a : Choice h k,c (.inr a)=false
  · obtain ⟨a,off⟩:=skip
    refine ⟨a,?_,?_,?_⟩
    · intro i hi;exact (sel i (.inr a) hi).resolve_right (by simp [off])
    · intro i hi;apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      exact (hc (.inl i) (.inr a) hi).resolve_right (by simp [off])
    · intro x on;cases x with
      | inl i => exact (Finset.mem_filter.mp (of_decide_eq_true on : i∈X)).2
      | inr b => exact (hc (.inr b) (.inr a) (of_decide_eq_true on : b≠a)).resolve_right (by simp [off])
  · refine ⟨(∅,∅),Finset.empty_subset _,Finset.empty_subset _,?_⟩
    intro x on;cases x with
    | inl i => exact (Finset.mem_filter.mp (of_decide_eq_true on : i∈X)).2
    | inr b => cases h:c (.inr b);exact False.elim (skip ⟨b,h⟩);rfl
theorem normal {c : Vtx h k l → Bool} (hc : ∀x y,graphRel x y → c x=true ∨ c y=true) :
    let Z:=bankBits (fun i => c (.inl i))
    let X:=bankBits (fun i => c (.inr (.inl (.inl i))))
    let Y:=bankBits (fun j => c (.inr (.inr (.inl j))))
    ∃ (a : Choice h k) (b : Choice h l),a.1⊆Z ∧ a.2⊆X ∧ b.1⊆Z ∧ b.2⊆Y ∧
      ∀x,member Z X Y a b x=true → c x=true := by
  intro Z X Y
  have zm i : i∈Z ↔ c (.inl i)=true := by simp [Z,bankBits]
  obtain ⟨a,aZ,aX,al⟩:=dominate (Z:=Z) (fun x => c (.inr (.inl x)))
    (fun x y h => hc (.inr (.inl x)) (.inr (.inl y)) h)
    (fun i x h => (hc (.inl i) (.inr (.inl x)) h).imp (zm i).mpr id)
  obtain ⟨b,bZ,bY,br⟩:=dominate (Z:=Z) (fun x => c (.inr (.inr x)))
    (fun x y h => hc (.inr (.inr x)) (.inr (.inr y)) h)
    (fun i x h => (hc (.inl i) (.inr (.inr x)) h).imp (zm i).mpr id)
  refine ⟨a,b,aZ,aX,bZ,bY,?_⟩;intro x yes
  cases x with
  | inl i => exact (zm i).mp (of_decide_eq_true yes)
  | inr r => cases r with
    | inl x => exact al x yes
    | inr x => exact br x yes
end PEqualNP.Outside.L_lib_1557_aux
namespace PEqualNP.Outside.L_lib_1557_aux
open scoped Classical
def bill {α : Type} [Fintype α] (wt : α → Nat) (c : α → Bool) := ∑x,if c x then wt x else 0
def weights (T : Nat) (u : Fin k → Nat) (v : Fin l → Nat) (L : Choice h k → Nat) (R : Choice h l → Nat) : Vtx h k l → Nat :=
  Sum.elim (fun _ => 2*T) (Sum.elim (Sum.elim u L) (Sum.elim v R))
theorem sumSelected (V : Bits k) (u : Fin k → Nat) :
    (∑i : Fin k,if i∈V then u i else 0)=V.sum u := by
  rw [←Finset.sum_filter];simp
theorem shoreBill (u : Fin k → Nat) (L : Choice h k → Nat) (X : Bits k) (a : Choice h k) :
    bill (Sum.elim u L) (shoreMember X a)+L a=X.sum u+∑b,L b := by
  unfold bill;rw [Fintype.sum_sum_type];simp only [shoreMember,Sum.elim_inl,Sum.elim_inr,decide_eq_true_eq,sumSelected]
  rw [Nat.add_assoc];congr 1
  have eq : (∑b,if b≠a then L b else 0)+ (∑b,if b=a then L b else 0)=∑b,L b := by
    rw [←Finset.sum_add_distrib];apply Finset.sum_congr rfl;intro b _;by_cases h:b=a <;> simp [h]
  simpa using eq
theorem normalBill (T : Nat) (u : Fin k → Nat) (v : Fin l → Nat) (L : Choice h k → Nat) (R : Choice h l → Nat)
    (Z : Bits h) (X : Bits k) (Y : Bits l) (a : Choice h k) (b : Choice h l) :
    bill (weights T u v L R) (member Z X Y a b)+L a+R b=
      (∑a,L a)+(∑b,R b)+Z.card*(2*T)+X.sum u+Y.sum v := by
  have tags : (∑i : Fin h,if i∈Z then 2*T else 0)=Z.card*(2*T) := by rw [sumSelected];simp
  have split : bill (weights T u v L R) (member Z X Y a b)=
      Z.card*(2*T)+(bill (Sum.elim u L) (shoreMember X a)+bill (Sum.elim v R) (shoreMember Y b)) := by
    unfold bill;rw [Fintype.sum_sum_type];simp only [weights,member,Sum.elim_inl,Sum.elim_inr,decide_eq_true_eq,tags,Fintype.sum_sum_type];rfl
  rw [split]
  have aBill:=shoreBill u L X a;have bBill:=shoreBill v R Y b
  omega
theorem billMono {α : Type} [Fintype α] (w : α → Nat) {a b : α → Bool} (sub : ∀x,a x=true → b x=true) : bill w a≤bill w b := by
  apply Finset.sum_le_sum;intro x _;by_cases h:a x=true
  · simp [h,sub x h]
  · simp [h]
def prize (B T : Nat) (u : Fin k → Nat) (f : Choice h k → Int) (a : Choice h k) :=
  ((3*B : Nat)+(T:Int)*a.1.card+((a.2.sum u:Nat):Int)-f a).toNat
theorem prizeEq {B T : Nat} (u : Fin k → Nat) (f : Choice h k → Int) (mx : maxCost f≤B) (a) :
    (prize B T u f a:Int)=3*(B:Int)+T*a.1.card+a.2.sum u-f a := by
  have hi:=(absLe f a).2
  have nonneg : (0:Int)≤(T:Int)*a.1.card := by positivity
  unfold prize;rw [show ((3*B : Nat):Int)=3*(B:Int) by norm_cast];apply Int.toNat_of_nonneg;omega
theorem prizeLow {B T : Nat} (u : Fin k → Nat) (f : Choice h k → Int) (mx : maxCost f≤B) (a) :
    2*B≤prize B T u f a := by
  have e:=prizeEq (T:=T) u f mx a;have := (absLe f a).2
  have nonneg : (0:Int)≤(T:Int)*a.1.card := by positivity
  omega
theorem cardOptions (h k l : Nat) (pos : 0<h+k+l) : 3≤Fintype.card (Choice h k)+Fintype.card (Choice h l) := by
  simp only [Choice,Bits,Fintype.card_prod,Fintype.card_finset,Fintype.card_fin]
  have p (n : Nat) : 1≤2^n := Nat.one_le_pow _ _ (by decide)
  have q (n : Nat) (hn : 0<n) : 2≤2^n := by simpa using Nat.pow_le_pow_right (by decide : 0<2) hn
  have a:=p h;have b:=p k;have c:=p l
  rcases Nat.eq_zero_or_pos h with rfl|hp
  · simp;by_cases hk:k=0
    · subst k;have :=q l (by omega);simp;omega
    · have :=q k (by omega);omega
  · have h1:=Nat.mul_le_mul_left (2^h) b;have h2:=Nat.mul_le_mul_left (2^h) c;have big:=q h hp;simp only [Nat.mul_one] at h1 h2;omega
end PEqualNP.Outside.L_lib_1557_aux
namespace PEqualNP.Outside.L_lib_1557_aux
open scoped Classical
def Priced (u : Fin k → Nat) (v : Fin l → Nat) (F : Bits k → Bits l → Nat) (w : Vtx h k l → Nat) (c : Nat) :=
  (∀i,w (.inr (.inl (.inl i)))=u i) ∧ (∀i,w (.inr (.inr (.inl i)))=v i) ∧
  ∀ X Y budget,c+F X Y≤budget ↔ ∃C : Vtx h k l → Bool,
    (∀a b,graphRel a b → C a=true ∨ C b=true) ∧ bill w C≤budget ∧
    bankBits (fun i => C (.inr (.inl (.inl i))))=X ∧ bankBits (fun i => C (.inr (.inr (.inl i))))=Y
theorem priced {h k l : Nat} {u : Fin k → Nat} {v : Fin l → Nat} {F : Bits k → Bits l → Nat}
    (positive : 0<h+k+l) (fac : Fac h F) (ad : Admiss u v F) :
    ∃w : Vtx h k l → Nat,∃c,Priced u v F w c := by
  classical
  obtain ⟨left,right,data⟩:=fac
  let idx : Bits h ≃ Fin (2^h) := Fintype.equivFinOfCardEq (by simp [Bits])
  let f (a : Choice h k) := left (idx a.1) a.2
  let g (b : Choice h l) := right (idx b.1) b.2
  let B := maxCost f+maxCost g
  let T := B+Finset.univ.sup (fun x : Bits k × Bits l => F x.1 x.2)
  have mf : maxCost f≤B := Nat.le_add_right _ _
  have mg : maxCost g≤B := Nat.le_add_left _ _
  let L := prize B T u f
  let R := prize B T v g
  let total := (∑a,L a)+(∑b,R b)
  have funds : 6*B≤total := by
    have loL:=Finset.sum_le_sum (s:=Finset.univ) (fun a _ => prizeLow (T:=T) u f mf a)
    have loR:=Finset.sum_le_sum (s:=Finset.univ) (fun b _ => prizeLow (T:=T) v g mg b)
    simp only [Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul] at loL loR
    have three:=Nat.mul_le_mul_right (2*B) (cardOptions h k l positive)
    rw [Nat.add_mul] at three
    change _≤∑a,L a at loL;change _≤∑b,R b at loR
    unfold total;omega
  let c := total-6*B
  have offset : c+6*B=total := Nat.sub_add_cancel funds
  let wt := weights T u v L R
  have equation (Z : Bits h) (X : Bits k) (Y : Bits l) (a : Choice h k) (b : Choice h l) :
      (bill wt (member Z X Y a b):Int)=(c:Int)+X.sum u+Y.sum v-(a.2.sum u:Nat)-(b.2.sum v:Nat)+f a+g b+
          (T:Int)*(2*(Z.card:Int)-a.1.card-b.1.card) := by
    have N:=normalBill T u v L R Z X Y a b
    change bill wt (member Z X Y a b)+L a+R b=total+Z.card*(2*T)+X.sum u+Y.sum v at N
    have eq : (bill wt (member Z X Y a b):Int)+(L a:Int)+(R b:Int)=(total:Int)+Z.card*(2*(T:Int))+X.sum u+Y.sum v := by exact_mod_cast N
    have leftW:=prizeEq (T:=T) u f mf a;have rightW:=prizeEq (T:=T) v g mg b
    change (L a:Int)=_ at leftW;change (R b:Int)=_ at rightW
    have ofst : (c:Int)+6*(B:Int)=total := by exact_mod_cast offset
    rw [leftW,rightW] at eq;linear_combination eq-ofst
  refine ⟨wt,c,fun _ => rfl,fun _ => rfl,?_⟩
  intro X Y budget;constructor
  · intro cheap;obtain ⟨i,eq⟩:=(data X Y).2
    let Z:=idx.symm i
    let a : Choice h k := (Z,X)
    let b : Choice h l := (Z,Y)
    have tight : (F X Y:Int)=f a+g b := by simpa [f,g,a,b,Z] using eq
    have billEq:=equation Z X Y a b
    change (bill wt (member Z X Y a b):Int)=(c:Int)+X.sum u+Y.sum v-(X.sum u:Nat)-(Y.sum v:Nat)+f a+g b+(T:Int)*(2*(Z.card:Int)-Z.card-Z.card) at billEq
    rw [show 2*(Z.card:Int)-Z.card-Z.card=0 by ring,mul_zero] at billEq
    refine ⟨member Z X Y a b,memberCovers (Finset.Subset.refl _) (Finset.Subset.refl _) (Finset.Subset.refl _) (Finset.Subset.refl _),by omega,?_,?_⟩
    · ext i;simp [bankBits,member,shoreMember]
    · ext i;simp [bankBits,member,shoreMember]
  · rintro ⟨C,edges,cheap,lview,rview⟩
    let Z := bankBits (fun i => C (.inl i))
    obtain ⟨a,b,aZ,aX,bZ,bY,sub⟩:=normal edges
    rw [lview] at aX;rw [rview] at bY;rw [lview,rview] at sub
    have less:=billMono wt sub
    change bill wt (member Z X Y a b)≤bill wt C at less
    have top := Finset.le_sup (s:=Finset.univ) (f:=fun x : Bits k × Bits l => F x.1 x.2) (Finset.mem_univ (a.2,b.2))
    have cap : (F a.2 b.2:Int)-f a-g b≤T := by
      have lf:=(absLe f a).1;have rg:=(absLe g b).1
      dsimp only at top;unfold T B;omega
    have pen:=cutPenalty Z a.1 b.1 (f a) (g b) T (F a.2 b.2) aZ bZ cap (by
      intro la rb;simpa only [f,g,la,rb] using (data a.2 b.2).1 (idx Z))
    have incr:=wholeBound ad aX bY
    have ex:=equation Z X Y a b
    omega
end PEqualNP.Outside.L_lib_1557_aux
namespace PEqualNP.Outside.L_lib_1557_aux
open scoped Classical
def portL (i : Fin k) : Vtx h k l := .inr (.inl (.inl i))
def portR (i : Fin l) : Vtx h k l := .inr (.inr (.inl i))
def sel (i : Fin h) : Vtx h k l := .inl i
def deleted : Vtx h k l → Bool := Sum.elim (fun _ => true) (fun _ => false)
def leftSide : Vtx h k l → Bool := Sum.elim (fun _ => false) (Sum.elim (fun _ => true) (fun _ => false))
theorem sideSep {x y : Vtx h k l} (e : graphRel x y) (hx : deleted x=false) (hy : deleted y=false) : leftSide x=leftSide y := by
  cases x with
  | inl i => contradiction
  | inr x => cases y with
    | inl i => contradiction
    | inr y => cases x <;> cases y <;> first | rfl | exact False.elim e
def mark {α : Type} (e : α ≃ Fin n) (b : α → Bool) := Finset.univ.filter (fun i => b (e.symm i)=true)
theorem markMem {α : Type} (e : α ≃ Fin n) (b : α → Bool) (i : Fin n) : i∈mark e b ↔ b (e.symm i)=true := by simp [mark]
def readBack {α : Type} (e : α ≃ Fin n) (C : Bits n) (x : α) := decide (e x∈C)
theorem markBack {α : Type} (e : α ≃ Fin n) (b : α → Bool) : readBack e (mark e b)=b := by
  funext x;cases hx:b x <;> simp [readBack,markMem,hx]
theorem billBack {α : Type} [Fintype α] (e : α ≃ Fin n) (w : α → Nat) (C : Bits n) :
    C.sum (fun i => w (e.symm i))=bill w (readBack e C) := by
  unfold bill;rw [←Finset.sum_filter] <;> simp only [readBack,decide_eq_true_eq] <;> try rfl
  have eq : C=(Finset.univ.filter (fun i => i∈C)) := by ext;simp
  calc
    _ = (Finset.univ.filter (fun i => i∈C)).sum (fun i => w (e.symm i)) := by rw [←eq]
    _ = _ := by rw [Finset.sum_filter,←e.sum_comp,Finset.sum_filter];simp
noncomputable def edgeSet (e : Vtx h k l ≃ Fin n) := Finset.univ.filter (fun t : Fin n × Fin n => graphRel (e.symm t.1) (e.symm t.2))
theorem coveredBack (e : Vtx h k l ≃ Fin n) (C : Bits n) : covers (edgeSet e) C ↔
    ∀x y,graphRel x y → readBack e C x=true ∨ readBack e C y=true := by
  constructor
  · intro hc x y r;have mem : (e x,e y)∈edgeSet e := by simp [edgeSet,r]
    simpa [readBack] using hc _ mem
  · intro hc t ht;have r:=(Finset.mem_filter.mp ht).2;simpa [readBack] using hc _ _ r
theorem realizesOfPriced {w : Vtx h k l → Nat} {c} {u : Fin k → Nat} {v : Fin l → Nat} {F : Bits k → Bits l → Nat}
    (ok : Priced u v F w c) : Realizes (Fintype.card (Vtx h k l)) h u v F := by
  classical
  let e := Fintype.equivFin (Vtx h k l)
  let n := Fintype.card (Vtx h k l)
  let p (i : Fin k) := e (portL i)
  let q (j : Fin l) := e (portR j)
  have dm : mark e deleted=Finset.univ.image (fun i : Fin h => e (sel i)) := by
    ext x;obtain ⟨a,rfl⟩:=e.surjective x;rw [markMem,Equiv.symm_apply_apply];cases a <;> simp [sel,deleted]
  have dc : (mark e deleted).card=h := by
    rw [dm,Finset.card_image_of_injective]
    · simp
    · intro i j he;exact Sum.inl.inj (e.injective he)
  have views (C : Bits n) : view p C=bankBits (fun i => readBack e C (.inr (.inl (.inl i)))) ∧
      view q C=bankBits (fun i => readBack e C (.inr (.inr (.inl i)))) := by
    constructor <;> unfold view bankBits <;> apply Finset.filter_congr <;> intro i _ <;> exact (decide_eq_true_iff).symm
  refine ⟨edgeSet e,fun i => w (e.symm i),mark e deleted,mark e leftSide,∅,∅,p,q,c,dc.le,?_,?_,?_,?_,?_,?_⟩
  · intro i j he;exact Sum.inl.inj (Sum.inl.inj (Sum.inr.inj (e.injective he)))
  · intro i j he;exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (e.injective he)))
  · intro i;simp [p,markMem,portL,leftSide,deleted,ok.1 i]
  · intro j;simp [q,markMem,portR,leftSide,deleted,ok.2.1 j]
  · intro t ht hD hD';simp only [markMem,Bool.not_eq_true] at hD hD' ⊢
    rw [sideSep (Finset.mem_filter.mp ht).2 hD hD']
  · intro X Y budget;rw [ok.2.2];constructor
    · rintro ⟨b,hc,cost,v1,v2⟩
      let C:=mark e b
      have rb : readBack e C=b := markBack _ _
      refine ⟨C,⟨(coveredBack _ _).mpr (by rwa [rb]),Finset.empty_subset _,Finset.disjoint_empty_right _⟩,?_,?_,?_⟩
      · rwa [billBack,rb]
      · simpa only [(views C).1,rb] using v1
      · simpa only [(views C).2,rb] using v2
    · rintro ⟨C,hc,cost,v1,v2⟩
      refine ⟨readBack e C,(coveredBack _ _).mp hc.1,?_,(views C).1.symm.trans v1,(views C).2.symm.trans v2⟩
      rwa [←billBack]
end PEqualNP.Outside.L_lib_1557_aux
namespace PEqualNP.Outside.L_lib_1557_aux
open scoped Classical
theorem zeroHost (u v : Fin 0 → Nat) (F : Bits 0 → Bits 0 → Nat) : Realizes 1 0 u v F := by
  classical
  refine ⟨∅,fun _ => F ∅ ∅,∅,∅,Finset.univ,∅,Fin.elim0,Fin.elim0,0,by simp,fun i => Fin.elim0 i,fun i => Fin.elim0 i,fun i => Fin.elim0 i,fun i => Fin.elim0 i,by simp,?_⟩
  intro X Y b
  have x : X=∅ := Subsingleton.elim _ _
  have y : Y=∅ := Subsingleton.elim _ _
  subst X;subst Y
  constructor
  · intro hb
    refine ⟨Finset.univ,⟨by simp [covers],by rfl,by simp⟩,?_,Subsingleton.elim _ _,Subsingleton.elim _ _⟩
    simpa using hb
  · rintro ⟨C,hc,le,_,_⟩
    have eq : C=Finset.univ := Finset.Subset.antisymm (Finset.subset_univ _) hc.2.1
    simpa [eq] using le
theorem realizeSmall {h k l : Nat} {u : Fin k → Nat} {v : Fin l → Nat} {F : Bits k → Bits l → Nat}
    (fac : Fac h F) (ad : Admiss u v F) :
    ∃ n ≤ k+l+h+2^h*(2^k+2^l),Realizes n h u v F := by
  by_cases hh : 0<h+k+l
  · obtain ⟨w,c,ok⟩:=priced hh fac ad
    exact ⟨_,(cardVtx h k l).le,realizesOfPriced ok⟩
  · have hz : h=0 := by omega
    have kz : k=0 := by omega
    have lz : l=0 := by omega
    subst h;subst k;subst l
    exact ⟨1,by decide,zeroHost _ _ _⟩
theorem viewIff (p : Fin k → Fin n) (C : Bits n) (X : Bits k) :
    view p C=X ↔ ∀i,i∈X ↔ p i∈C := by
  constructor
  · rintro rfl i;simp only [view,Finset.mem_filter,Finset.mem_univ,true_and]
  · intro H;ext i;simpa only [view,Finset.mem_filter,Finset.mem_univ,true_and] using (H i).symm
end PEqualNP.Outside.L_lib_1557_aux

namespace PEqualNP.Outside.L_lib_1557_aux
open scoped Classical
def mass (m : Fin k → Nat) (X : Bits k) := X.sum m
def metric (m : Fin k → Nat) (X Y : Bits k) := mass m (X\Y)+mass m (Y\X)
def tariff (m : Fin k → Nat) (X Y : Bits k) := 2*mass m Finset.univ+2*mass m (X∪Y)
def entry (m : Fin k → Nat) (X : Bits k) (i : Fin k) := if i∈X then m i else 0
theorem expandMass (m : Fin k → Nat) (X : Bits k) : mass m X=∑i,entry m X i := by
  classical
  have e : X=Finset.univ.filter (fun i => i∈X) := by ext;simp
  unfold mass;conv_lhs => rw [e,Finset.sum_filter]
  rfl
theorem expandMetric (m : Fin k → Nat) (X Y : Bits k) : metric m X Y=∑i,(entry m (X\Y) i+entry m (Y\X) i) := by simp [metric,expandMass,Finset.sum_add_distrib]
theorem tri (m : Fin k → Nat) (X Y Z : Bits k) : metric m X Z ≤ metric m X Y+metric m Y Z := by
  simp only [expandMetric,←Finset.sum_add_distrib];apply Finset.sum_le_sum;intro i _
  by_cases x:i∈X <;> by_cases y:i∈Y <;> by_cases z:i∈Z <;> simp [entry,x,y,z]
theorem metricComm (m : Fin k → Nat) (X Y : Bits k) : metric m X Y=metric m Y X := Nat.add_comm ..
theorem encodePrice (m : Fin k → Nat) (X Y : Bits k) :
    tariff m X Y=2*mass m Finset.univ+mass m X+mass m Y+metric m X Y := by
  have coord : 2*mass m (X∪Y)=mass m X+mass m Y+metric m X Y := by
    rw [two_mul];simp only [expandMetric,expandMass,←Finset.sum_add_distrib];apply Finset.sum_congr rfl
    intro i _;by_cases x:i∈X <;> by_cases y:i∈Y <;> simp [entry,x,y]
  unfold tariff;omega
theorem metricSelf (m : Fin k → Nat) (X : Bits k) : metric m X X=0 := by simp [metric,mass]
theorem nearInsert (m : Fin k → Nat) (X : Bits k) (i : Fin k) : metric m (insert i X) X≤ m i := by
  by_cases h:i∈X
  · simp [Finset.insert_eq_of_mem h,metricSelf]
  · have e : insert i X \ X={i} := by ext j;by_cases hh:j=i <;> simp [hh,h]
    have ee : X \ insert i X=∅ := Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_insert _ _)
    simp [metric,mass,e,ee]
theorem massInsert (m : Fin k → Nat) (X : Bits k) (i : Fin k) : mass m (insert i X)≤ mass m X+m i := by
  by_cases h:i∈X
  · simp [Finset.insert_eq_of_mem h]
  · simp [mass,Finset.sum_insert h,Nat.add_comm]
end PEqualNP.Outside.L_lib_1557_aux

namespace PEqualNP.Outside.L_lib_1557_aux
open scoped Classical
noncomputable def leastVal {α : Type} [Nonempty α] (f : α → Nat) := Nat.find (show ∃v,∃a,f a=v from ⟨_,Classical.choice inferInstance,rfl⟩)
theorem leastWitness {α : Type} [Nonempty α] (f : α → Nat) : ∃a,f a=leastVal f := by unfold leastVal;exact Nat.find_spec (p:=fun v => ∃a,f a=v) _
theorem leastBound {α : Type} [Nonempty α] (f : α → Nat) (a) : leastVal f ≤ f a := Nat.find_min' _ ⟨a,rfl⟩
def Classes (k h s : Nat) (m : Fin k → Nat) := ∃S : Finset (Finset (Bits k)),S.card ≤ 2^h ∧
  (∀X,∃T∈S,X∈T) ∧ ∀T∈S,∀X∈T,∀Y∈T,metric m X Y ≤ s
theorem numbered {m : Fin k → Nat} (cover : Classes k h s m) :
    ∃T : Fin (2^h) → Finset (Bits k),(∀i,(T i).Nonempty) ∧ (∀X,∃i,X∈T i) ∧
      ∀i,∀X∈T i,∀Y∈T i,metric m X Y ≤ s := by
  classical
  obtain ⟨S,cap,full,diam⟩:=cover
  let Q:=S.filter Finset.Nonempty
  obtain ⟨U,u,mem⟩:=full ∅
  letI : Nonempty ↥Q := ⟨⟨U,Finset.mem_filter.mpr ⟨u,_,mem⟩⟩⟩
  have size : Fintype.card ↥Q ≤ 2^h := by
    rw [Fintype.card_coe];exact (Finset.card_le_card (Finset.filter_subset ..)).trans cap
  let emb : ↥Q ↪ Fin (2^h) := (Fintype.equivFin ↥Q).toEmbedding.trans (Fin.castLEEmb size)
  let name := Function.invFun emb
  have onto : Function.Surjective name := (Function.leftInverse_invFun emb.injective).surjective
  refine ⟨fun i => (name i).val,fun i => (Finset.mem_filter.mp (name i).property).2,?_,fun i => diam _ (Finset.mem_filter.mp (name i).property).1⟩
  intro X;obtain ⟨U,u,mem⟩:=full X
  obtain ⟨i,hi⟩:=onto ⟨U,Finset.mem_filter.mpr ⟨u,_,mem⟩⟩
  exact ⟨i,by simpa [hi] using mem⟩
theorem factorApprox {m : Fin k → Nat} (cover : Classes k h s m) :
    ∃F : Bits k → Bits k → Nat, Fac h F ∧ Admiss (fun i => 2*m i) (fun i => 2*m i) F ∧
      ∀X Y,tariff m X Y ≤ F X Y ∧ F X Y ≤ tariff m X Y+s := by
  classical
  obtain ⟨T,nonempty,full,diam⟩:=numbered cover
  letI (i : Fin (2^h)) : Nonempty ↥(T i) := by obtain ⟨x,hx⟩:=nonempty i;exact ⟨⟨x,hx⟩⟩
  let near (i : Fin (2^h)) (X : Bits k) := leastVal (fun z : ↥(T i) => metric m X z.1)
  let far (i : Fin (2^h)) (Y : Bits k) := (T i).sup (fun z => metric m z Y)
  let row i X := 2*mass m Finset.univ+mass m X+near i X
  let col i Y := mass m Y+far i Y
  let F X Y := leastVal (fun i => row i X+col i Y)
  have maxle i z (hz : z∈T i) Y : metric m z Y ≤ far i Y := Finset.le_sup (f:=fun z => metric m z Y) hz
  have nr i X : ∃z : ↥(T i),metric m X z.val=near i X := leastWitness _
  have atMin X Y : ∃i,row i X+col i Y=F X Y := leastWitness _
  have below X Y i : F X Y ≤ row i X+col i Y := leastBound _ _
  have nearStep i X j : near i (insert j X) ≤ near i X+m j := by
    obtain ⟨z,eq⟩:=nr i X
    have a:=leastBound (fun z : ↥(T i) => metric m (insert j X) z.1) z
    change near i (insert j X) ≤ _ at a
    have b:=tri m (insert j X) X z.val;have c:=nearInsert m X j;omega
  have farStep i Y j : far i (insert j Y) ≤ far i Y+m j := by
    apply Finset.sup_le;intro z hz
    have b:=tri m z Y (insert j Y);have c:=nearInsert m Y j;rw [metricComm m Y (insert j Y)] at b
    have a:=maxle i z hz Y;omega
  refine ⟨F,⟨fun i X => (row i X:Int),fun i Y => (col i Y:Int),?_⟩,⟨?_,?_⟩,?_⟩
  · intro X Y;constructor
    · intro i;dsimp only;exact_mod_cast below X Y i
    · obtain ⟨i,hi⟩:=atMin X Y;exact ⟨i,by dsimp only;exact_mod_cast hi.symm⟩
  · intro X Y j;obtain ⟨i,hi⟩:=atMin X Y
    have hb:=below (insert j X) Y i;have d:=nearStep i X j;have a:=massInsert m X j
    dsimp only [row] at hi hb;dsimp only;omega
  · intro X Y j;obtain ⟨i,hi⟩:=atMin X Y
    have hb:=below X (insert j Y) i;have d:=farStep i Y j;have a:=massInsert m Y j
    dsimp only [col] at hi hb;dsimp only;omega
  · intro X Y;rw [encodePrice];constructor
    · obtain ⟨i,hi⟩:=atMin X Y;obtain ⟨z,hz⟩:=nr i X
      have a:=maxle i z.val z.property Y;have d:=tri m X z.val Y
      dsimp only [row,col] at hi;omega
    · obtain ⟨i,mem⟩:=full X
      have nz:=leastBound (fun z : ↥(T i) => metric m X z.val) ⟨X,mem⟩
      change near i X ≤  metric m X X at nz;rw [metricSelf] at nz
      have cap : far i Y ≤  metric m X Y+s := by
        apply Finset.sup_le;intro z hz;have a:=tri m z X Y;have b:=diam i z hz X mem;omega
      have b:=below X Y i;dsimp only [row,col] at b;omega
end PEqualNP.Outside.L_lib_1557_aux

namespace PEqualNP.Outside.L_lib_1557_aux
open scoped Classical
def matchPorts (G : Finset (Fin n × Fin n)) (I O : Bits n) (p q : Fin k → Fin n) (X Y : Bits k) (C : Bits n) :=
  feasible G I O C ∧ view p C=X ∧ view q C=Y
def ApproxHost (h s : Nat) (m : Fin k → Nat) :=
  ∃ (n c : Nat) (G : Finset (Fin n × Fin n)) (w : Fin n → Nat) (D A I O : Bits n) (p q : Fin k → Fin n),
    D.card ≤ h ∧ Function.Injective p ∧ Function.Injective q ∧
    (∀i,p i∈A ∧ p i∉D ∧ w (p i)=2*m i) ∧ (∀i,q i∉A ∧ q i∉D ∧ w (q i)=2*m i) ∧
    (∀e∈G,e.1∉D → e.2∉D → (e.1∈A ↔ e.2∈A)) ∧
    ∀X Y,(∀C,matchPorts G I O p q X Y C → c+tariff m X Y ≤ C.sum w) ∧
      ∃C,matchPorts G I O p q X Y C ∧ C.sum w ≤ c+tariff m X Y+s
theorem upperHost {m : Fin k → Nat} (classes : Classes k h s m) : ApproxHost h s m := by
  obtain ⟨F,fac,ad,err⟩:=factorApprox classes
  obtain ⟨n,_,G,w,D,A,I,O,p,q,c,dc,injP,injQ,l,r,sep,rep⟩:=realizeSmall fac ad
  refine ⟨n,c,G,w,D,A,I,O,p,q,dc,injP,injQ,l,r,sep,?_⟩
  intro X Y;obtain ⟨lo,hi⟩:=err X Y
  constructor
  · rintro C ⟨ok,x,y⟩;have e:=(rep X Y (C.sum w)).mpr ⟨C,ok,le_rfl,x,y⟩;omega
  · obtain ⟨C,ok,cb,x,y⟩:=(rep X Y (c+F X Y)).mp le_rfl
    exact ⟨C,⟨ok,x,y⟩,by omega⟩
theorem classOfHost {m : Fin k → Nat} (host : ApproxHost h s m) : Classes k h s m := by
  classical
  obtain ⟨n,c,G,w,D,A,I,O,p,q,sz,_,_,lp,rq,sep,ans⟩:=host
  choose C fit cost using fun (X : Bits k) => (ans X X).2
  let color X := pattern D (C X)
  let fiber (Z : Bits n) := Finset.univ.filter (fun X : Bits k => color X=Z)
  have colorOK X : color X∈D.powerset := Finset.mem_powerset.mpr Finset.inter_subset_right
  refine ⟨D.powerset.image fiber,?_,?_,?_⟩
  · exact Finset.card_image_le.trans ((Finset.card_powerset D) ▸ Nat.pow_le_pow_right (by decide : 0<2) sz)
  · intro X;exact ⟨_,Finset.mem_image_of_mem _ (colorOK X),by simp [fiber]⟩
  · intro T ht;obtain ⟨Z,_,rfl⟩:=Finset.mem_image.mp ht
    intro X hx Y hy
    have ec : color X=color Y := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    have cross (U V : Bits k) (e : color U=color V) : c+tariff m U V ≤ (mix D A (C U) (C V)).sum w := by
      have vp:=mixViews (fun i => Or.inr (lp i).1) (fun i => Or.inr (rq i).1) e
      exact (ans U V).1 _ ⟨mixFeasible sep (fit U).1 (fit V).1 e,vp.1.trans (fit U).2.1,vp.2.trans (fit V).2.2⟩
    have xy:=cross X Y ec;have yx:=cross Y X ec.symm
    have x:=cost X;have y:=cost Y
    rw [mixPrice,encodePrice] at xy yx
    rw [encodePrice,metricSelf] at x y
    rw [metricComm m Y X] at yx
    have a:=dividePrice w D A (C X);have b:=dividePrice w D A (C Y)
    omega
end PEqualNP.Outside.L_lib_1557_aux

open PEqualNP.Outside.L_lib_1557_aux in
theorem PEqualNP.Outside.L_lib_1557 : letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (k h s : Nat) (m : Fin k → Nat),
let B := Finset (Fin k)
let mu := fun (X : B) => X.sum m
let dist := fun (X Y : B) => mu (X \ Y) + mu (Y \ X)
let target := fun (X Y : B) => 2 * mu Finset.univ + 2 * mu (X ∪ Y)
(∃ (n c : Nat) (G : Finset (Fin n × Fin n)) (w : Fin n → Nat)
    (D A I O : Finset (Fin n)) (p q : Fin k → Fin n),
    D.card ≤ h ∧ Function.Injective p ∧ Function.Injective q ∧
    (∀ i, p i ∈ A ∧ p i ∉ D ∧ w (p i) = 2 * m i) ∧
    (∀ i, q i ∉ A ∧ q i ∉ D ∧ w (q i) = 2 * m i) ∧
    (∀ e ∈ G, e.1 ∉ D → e.2 ∉ D → (e.1 ∈ A ↔ e.2 ∈ A)) ∧
    ∀ X Y : B,
      let fits := fun (C : Finset (Fin n)) =>
        I ⊆ C ∧ Disjoint C O ∧ (∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C) ∧
        (∀ i, i ∈ X ↔ p i ∈ C) ∧ (∀ i, i ∈ Y ↔ q i ∈ C)
      (∀ C, fits C → c + target X Y ≤ C.sum w) ∧
      ∃ C, fits C ∧ C.sum w ≤ c + target X Y + s) ↔
∃ S : Finset (Finset B), S.card ≤ 2 ^ h ∧
  (∀ X : B, ∃ T ∈ S, X ∈ T) ∧
  ∀ T ∈ S, ∀ X ∈ T, ∀ Y ∈ T, dist X Y ≤ s := by
  classical
  intro k h s m B mu dist target
  have distEq (X Y : B) : dist X Y=metric m X Y := by
    unfold dist mu metric mass
    congr 2 <;> ext i <;> simp only [Finset.mem_sdiff] <;> exact @Finset.mem_sdiff (Fin k) (fun i j => Classical.propDecidable (i=j)) _ _ _
  have tarEq (X Y : B) : target X Y=tariff m X Y := by
    unfold target mu tariff mass
    congr 3 <;> ext i <;> simp only [Finset.mem_union] <;> exact @Finset.mem_union (Fin k) (fun i j => Classical.propDecidable (i=j)) _ _ _
  have fitsEq {n} (G : Finset (Fin n × Fin n)) (I O : Bits n) (p q : Fin k → Fin n) (X Y : B) (C : Bits n) :
      (I⊆C ∧ Disjoint C O ∧ (∀e∈G,e.1∈C ∨ e.2∈C) ∧
       (∀i,i∈X ↔ p i∈C) ∧ (∀i,i∈Y ↔ q i∈C)) ↔ matchPorts G I O p q X Y C := by
    unfold matchPorts feasible covers;rw [viewIff,viewIff];tauto
  simp only [distEq,tarEq,fitsEq]
  constructor
  · intro H;apply classOfHost
    obtain ⟨n,c,G,w,D,A,I,O,p,q,sz,ip,iq,l,r,sep,ans⟩:=H
    exact ⟨n,c,G,w,D,A,I,O,p,q,sz,ip,iq,l,r,sep,ans⟩
  · intro H
    obtain ⟨n,c,G,w,D,A,I,O,p,q,sz,ip,iq,l,r,sep,ans⟩:=upperHost (m:=m) (h:=h) (s:=s) H
    exact ⟨n,c,G,w,D,A,I,O,p,q,sz,ip,iq,l,r,sep,ans⟩
