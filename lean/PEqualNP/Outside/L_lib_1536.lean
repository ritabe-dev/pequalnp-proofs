import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1536_aux
open scoped Classical
variable {α : Type} [Fintype α] [DecidableEq α]
abbrev Hue := Fin 3
def covers (E : α → α → Prop) (C : Finset α) := ∀ x y,E x y → x∈C ∨ y∈C
def halfC (E : α → α → Prop) (f : α → Hue) := ∀ x y,E x y → 2≤(f x).val+(f y).val
def halfCost (f : α → Hue) := ∑x,(f x).val
def halves (f : α → Hue) := (Finset.univ.filter (fun x => f x=1)).card
def integral (C : Finset α) (x : α) : Hue := if x∈C then 2 else 0
theorem intOK {E : α → α → Prop} {C : Finset α} (h : covers E C) : halfC E (integral C) := by
  intro x y ed;rcases h _ _ ed with hx|hy <;> simp_all [integral]
theorem intPrice (C : Finset α) : halfCost (integral C)=2*C.card := by
  unfold halfCost;calc
    _ = ∑ x : α,if x∈C then 2 else 0 := by apply Finset.sum_congr rfl;intro x _;by_cases h : x∈C <;> simp [integral,h]
    _ = _ := by rw [←Finset.sum_filter];simp [Nat.mul_comm]
def roundB (z : Hue) (b : Bool) : Bool := if z=0 then false else if z=2 then true else b
def soften (z : Hue) (b : Bool) : Hue := if (z=0 ∧ b=true) ∨ (z=2 ∧ b=false) then 1 else z
def valB (b : Bool) := b.toNat
theorem roundGood : ∀ s t : Hue,∀ a b : Bool,2 ≤ s.val+t.val → (a=true ∨ b=true) →
    roundB s a=true ∨ roundB t b=true := by decide +kernel
theorem softGood : ∀ s t : Hue,∀ a b : Bool,2 ≤ s.val+t.val → (a=true ∨ b=true) →
    2≤(soften s a).val+(soften t b).val := by decide +kernel
theorem localBill : ∀ s : Hue,∀ a : Bool,(soften s a).val+valB (roundB s a)=s.val+valB a := by decide +kernel
theorem extraHalf : ∀ (s : Hue) (a : Bool),s=1 → soften s a=1 := by decide +kernel
theorem countB (p : α → Bool) : (∑x,valB (p x))=(Finset.univ.filter (fun x => p x=true)).card := by
  calc
    _ = ∑x, if p x=true then 1 else 0 := by apply Finset.sum_congr rfl;intro x _;cases h : p x <;> simp [valB,h]
    _ = _ := by rw [←Finset.sum_filter];simp
theorem persistent (E : α → α → Prop) :
    ∃ f : α → Hue,halfC E f ∧ (∀ C,covers E C → halfCost f≤2*C.card) ∧
    ∀ C,covers E C → (∀ C',covers E C' → C.card≤C'.card) → ∀x∈C,0<(f x).val := by
  classical
  let F := Finset.univ.filter (halfC E)
  have mem f : f∈F ↔ halfC E f := by simp [F]
  have ne : F.Nonempty := ⟨fun _ => 2,(mem _).mpr (by intro _ _ _;exact (by decide : 2≤(2:Hue).val+(2:Hue).val))⟩
  obtain ⟨z,hz,best⟩ := Finset.exists_min_image F halfCost ne
  let L := F.filter (fun f => halfCost f=halfCost z)
  obtain ⟨f,hf,most⟩ := Finset.exists_max_image L halves ⟨z,Finset.mem_filter.mpr ⟨hz,rfl⟩⟩
  obtain ⟨okay,price⟩ := Finset.mem_filter.mp hf
  have valid := (mem f).mp okay
  refine ⟨f,valid,?_,?_⟩
  · intro C hc;rw [price,←intPrice];exact best _ ((mem _).mpr (intOK hc))
  · intro C cv cheapest x hx
    let b (a : α) := decide (a∈C)
    let D := Finset.univ.filter (fun a => roundB (f a) (b a)=true)
    let y := fun a => soften (f a) (b a)
    have bits (a b' : α) (ed : E a b') : b a=true ∨ b b'=true := by simpa [b] using cv _ _ ed
    have dy : covers E D := by
      intro a v ed;simpa [D] using roundGood _ _ _ _ (valid _ _ ed) (bits _ _ ed)
    have fy : halfC E y := fun a v ed => softGood _ _ _ _ (valid _ _ ed) (bits _ _ ed)
    have bill : halfCost y+D.card=halfCost f+C.card := by
      have cb : (∑ a,valB (b a))=C.card := by rw [countB];simp [b]
      rw [←cb,show D.card=(∑a,valB (roundB (f a) (b a))) from (countB _).symm]
      simp only [halfCost,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl;intro a _;exact localBill _ _
    have pmin := best y ((mem _).mpr fy)
    have dmin := cheapest D dy
    have ys : y∈L := Finset.mem_filter.mpr ⟨(mem _).mpr fy,by omega⟩
    have upto := most y ys
    let U := Finset.univ.filter (fun a => f a=1)
    let V := Finset.univ.filter (fun a => y a=1)
    have sub : U⊆V := by
      intro a ha;apply Finset.mem_filter.mpr;exact ⟨Finset.mem_univ _,extraHalf _ _ (Finset.mem_filter.mp ha).2⟩
    have equal := Finset.eq_of_subset_of_card_le sub (show V.card≤U.card from upto)
    by_contra! no
    have fx : f x=0 := Fin.ext (by omega)
    have vx : x∈V := by simp [V,y,b,hx,fx,soften]
    have ux : x∈U := equal ▸ vx
    have bad := (Finset.mem_filter.mp ux).2
    rw [fx] at bad;contradiction
end PEqualNP.Outside.L_lib_1536_aux

namespace PEqualNP.Outside.L_lib_1536_aux
open scoped Classical
variable {α : Type} [Fintype α] [DecidableEq α]
def allows (E : α → α → Prop) (B : Nat) (U : Finset α) := ∃ C,covers E C ∧ C.card≤B ∧ U⊆C
theorem smallCore (E : α → α → Prop) (opt r g : Nat) (U : Finset α)
    (slack : ∀y,halfC E y → 2*opt≤halfCost y+g) (bad : ¬allows E (opt+r) U) :
    ∃ T⊆U,T.card≤g+2*(r+1) ∧ ¬allows E (opt+r) T := by
  classical
  let B := opt+r
  let F := U.powerset.filter (fun t => ¬allows E B t)
  have mem (t) : t∈F ↔ t⊆U ∧ ¬allows E B t := by simp [F]
  have ne : F.Nonempty := ⟨U,(mem _).mpr ⟨Finset.Subset.rfl,bad⟩⟩
  obtain ⟨T,ht,smallest⟩:=Finset.exists_min_image F Finset.card ne
  obtain ⟨sub,fail⟩ := (mem T).mp ht
  refine ⟨T,sub,?_,fail⟩
  rcases T.eq_empty_or_nonempty with empty|nonempty
  · simp [empty]
  have afterErase (u : α) (hu : u∈T) : allows E B (T.erase u) := by
    by_contra no
    have bound:=smallest (T.erase u) ((mem _).mpr ⟨(Finset.erase_subset _ _).trans sub,no⟩)
    have strict:=Finset.card_erase_lt_of_mem hu;omega
  let H := fun x y => E x y ∧ x∉T ∧ y∉T
  have extCov (Y : Finset α) (yes : covers H Y) : covers E (T∪Y) := by
    intro x y ed;by_cases hx : x∈T
    · exact Or.inl (Finset.mem_union_left _ hx)
    by_cases hy : y∈T
    · exact Or.inr (Finset.mem_union_left _ hy)
    exact (yes x y ⟨ed,hx,hy⟩).imp (Finset.mem_union_right T) (Finset.mem_union_right T)
  have floorCost (Y) (yes : covers H Y) : B<T.card+Y.card := by
    by_contra! small
    exact fail ⟨T∪Y,extCov Y yes,(Finset.card_union_le T Y).trans small,Finset.subset_union_left⟩
  have witness (u) (hu : u∈T) : ∃ Z,covers H Z ∧ (∀Y,covers H Y → Z.card≤Y.card) ∧
      T.card+Z.card=B+1 ∧ (∀v,v∉T → (E u v ∨ E v u) → v∈Z) := by
    obtain ⟨C,cov,cheap,rest⟩:=afterErase u hu
    have absent : u∉C := by
      intro inside;apply fail ⟨C,cov,cheap,?_⟩
      intro x hx;by_cases eq : x=u
      · exact eq ▸ inside
      · exact rest (Finset.mem_erase.mpr ⟨eq,hx⟩)
    let Z := C\T
    have yes : covers H Z := by
      intro x y h;exact (cov x y h.1).imp (fun a=>Finset.mem_sdiff.mpr ⟨a,h.2.1⟩) (fun b=>Finset.mem_sdiff.mpr ⟨b,h.2.2⟩)
    have union : T∪Z=insert u C := by
      ext x;simp only [Z,Finset.mem_union,Finset.mem_sdiff,Finset.mem_insert];constructor
      · rintro (h|⟨h,_⟩)
        · by_cases eq : x=u;exact Or.inl eq;exact Or.inr (rest (Finset.mem_erase.mpr ⟨eq,h⟩))
        · exact Or.inr h
      · rintro (rfl|h);exact Or.inl hu;by_cases inside : x∈T;exact Or.inl inside;exact Or.inr ⟨h,inside⟩
    have card : T.card+Z.card=B+1 := by
      have h:=congrArg Finset.card union
      rw [Finset.card_union_of_disjoint (show Disjoint T Z from Finset.disjoint_sdiff),Finset.card_insert_of_notMem absent] at h
      have := floorCost Z yes;omega
    refine ⟨Z,yes,fun Y h => by have := floorCost Y h;omega,card,?_⟩
    intro v out rel;rcases rel with rel|rel
    · exact Finset.mem_sdiff.mpr ⟨(cov u v rel).resolve_left absent,out⟩
    · exact Finset.mem_sdiff.mpr ⟨(cov v u rel).resolve_right absent,out⟩
  obtain ⟨f,feas,low,fix⟩ := persistent H
  let y (x : α) : Hue := if x∈T then 1 else f x
  have touch (u) (hu : u∈T) (v) (no : v∉T) (ed : E u v ∨ E v u) : 0<(f v).val := by
    obtain ⟨Z,ok,best,_,use⟩:=witness u hu;exact fix Z ok best v (use v no ed)
  have hy : halfC E y := by
    intro x z ed;by_cases hx : x∈T <;> by_cases hz : z∈T
    · simp [y,hx,hz]
    · have h:=touch _ hx _ hz (Or.inl ed);simp [y,hx,hz];omega
    · have h:=touch _ hz _ hx (Or.inr ed);simp [y,hx,hz];omega
    · simpa only [y,hx,hz,ite_false] using feas x z ⟨ed,hx,hz⟩
  have bill : halfCost y≤T.card+halfCost f := by
    have cnt : (∑x : α,if x∈T then 1 else 0)=T.card := by rw [←Finset.sum_filter];simp
    rw [←cnt,halfCost,halfCost,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum;intro x _;by_cases hx : x∈T <;> simp [y,hx]
  obtain ⟨u,hu⟩:=nonempty
  obtain ⟨Z,ok,_,size,_⟩:=witness u hu
  have lower:=slack y hy;have price:=low Z ok;unfold B at size;omega
end PEqualNP.Outside.L_lib_1536_aux

namespace PEqualNP.Outside.L_lib_1536_aux
open scoped Classical
variable {α : Type} [Fintype α] [DecidableEq α]
abbrev Copy (w : α → Nat) := (v : α) × Fin (w v)
def liftSet (w : α → Nat) (C : Finset α) : Finset (Copy w) :=
  C.sigma (fun _ => Finset.univ)
theorem liftMem (w : α → Nat) (C : Finset α) (z : Copy w) : z∈liftSet w C ↔ z.1∈C := by simp [liftSet]
theorem liftCard (w : α → Nat) (C : Finset α) : (liftSet w C).card=C.sum w := by simp [liftSet,Finset.card_sigma]
def filled (w : α → Nat) (Y : Finset (Copy w)) := Finset.univ.filter (fun i => ∀j : Fin (w i),Sigma.mk i j∈Y)
theorem filledMem (w : α → Nat) (Y : Finset (Copy w)) (i) : i∈filled w Y ↔ ∀j : Fin (w i),Sigma.mk i j∈Y := by simp [filled]
theorem fillCost (w : α → Nat) (Y : Finset (Copy w)) : (filled w Y).sum w≤Y.card := by
  rw [←liftCard];apply Finset.card_le_card; rintro ⟨i,j⟩ h;exact (filledMem w Y i).mp ((liftMem _ _ _).mp h) j
def copyEdge (E : α → α → Prop) (w : α → Nat) (x y : Copy w) := E x.1 y.1
theorem fillCov {E : α → α → Prop} {w : α → Nat} {Y : Finset (Copy w)} (yes : covers (copyEdge E w) Y) :
    covers E (filled w Y) := by
  intro i j r;by_contra! no
  obtain ⟨a,ha⟩ := not_forall.mp ((filledMem _ _ _).not.mp no.1)
  obtain ⟨b,hb⟩ := not_forall.mp ((filledMem _ _ _).not.mp no.2)
  exact (yes ⟨i,a⟩ ⟨j,b⟩ r).elim ha hb
theorem liftCov {E : α → α → Prop} (w : α → Nat) {C : Finset α} (yes : covers E C) :
    covers (copyEdge E w) (liftSet w C) :=
  fun x y h => (yes _ _ h).imp ((liftMem _ _ _).mpr) ((liftMem _ _ _).mpr)
noncomputable def compressHalf (w : α → Nat) (f : Copy w → Hue) (i : α) : Hue :=
  if p : (Finset.univ : Finset (Fin (w i))).Nonempty then
    ((Finset.univ : Finset (Fin (w i))).image (fun j => f ⟨i,j⟩)).min' (p.image _) else 2
theorem lowerHalf (w : α → Nat) (f : Copy w → Hue) (i : α) (j : Fin (w i)) : compressHalf w f i ≤ f ⟨i,j⟩ := by
  have ne : (Finset.univ : Finset (Fin (w i))).Nonempty := ⟨j,Finset.mem_univ _⟩
  simp only [compressHalf,ne,reduceDIte];exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
theorem halfWitness (w : α → Nat) (f : Copy w → Hue) (i : α) :
    compressHalf w f i=2 ∨ ∃ j : Fin (w i), f ⟨i,j⟩=compressHalf w f i := by
  by_cases p : (Finset.univ : Finset (Fin (w i))).Nonempty
  · right;unfold compressHalf;rw [dif_pos p];obtain ⟨j,_,eq⟩:= Finset.mem_image.mp (Finset.min'_mem _ (p.image (fun j => f ⟨i,j⟩)));exact ⟨j,eq⟩
  · left;simp [compressHalf,p]
theorem compressedOK {E : α → α → Prop} {w : α → Nat} {f : Copy w → Hue} (hf : halfC (copyEdge E w) f) :
    halfC E (compressHalf w f) := by
  intro x y e;rcases halfWitness w f x with hx|⟨i,hi⟩
  · simp [hx]
  rcases halfWitness w f y with hy|⟨j,hj⟩
  · simp [hy]
  rw [←hi,←hj];exact hf ⟨x,i⟩ ⟨y,j⟩ e
def price (w : α → Nat) (y : α → Hue) := ∑v,w v*(y v).val
theorem compressBill (w : α → Nat) (f : Copy w → Hue) : price w (compressHalf w f) ≤ halfCost f := by
  unfold price halfCost;rw [Fintype.sum_sigma];apply Finset.sum_le_sum;intro i _
  calc
    _ = ∑ _j : Fin (w i), (compressHalf w f i).val := by simp
    _ ≤ _ := Finset.sum_le_sum (fun j _ => lowerHalf w f i j)
def affordable (E : α → α → Prop) (w : α → Nat) (B : Nat) (U : Finset α) :=
  ∃ C,covers E C ∧ C.sum w≤B ∧ U⊆C
theorem positiveCore (E : α → α → Prop) (w : α → Nat) (opt r g : Nat) (U : Finset α)
    (slack : ∀ y,halfC E y → 2*opt≤price w y+g) (bad : ¬affordable E w (opt+r) U) :
    ∃ T⊆U,T.card≤g+2*(r+1) ∧ ¬affordable E w (opt+r) T := by
  classical
  have hy (f : Copy w → Hue) (h : halfC (copyEdge E w) f) : 2*opt≤halfCost f+g :=
    (slack _ (compressedOK h)).trans (Nat.add_le_add_right (compressBill w f) _)
  have no : ¬allows (copyEdge E w) (opt+r) (liftSet w U) := by
    rintro ⟨Y,h,cheap,sub⟩;apply bad ⟨filled w Y,fillCov h,(fillCost w Y).trans cheap,?_⟩
    intro i hi;apply (filledMem _ _ _).mpr;intro j;exact sub ((liftMem w U ⟨i,j⟩).mpr hi)
  obtain ⟨T,sub,size,fail⟩ := smallCore _ opt r g _ hy no
  refine ⟨T.image Sigma.fst,?_,Finset.card_image_le.trans size,?_⟩
  · intro i h;obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp h;exact (liftMem _ _ _).mp (sub hz)
  · rintro ⟨C,h,cheap,inside⟩;apply fail ⟨liftSet w C,liftCov w h,by rwa [liftCard],?_⟩
    intro z hz;exact (liftMem _ _ _).mpr (inside (Finset.mem_image_of_mem _ hz))
end PEqualNP.Outside.L_lib_1536_aux

namespace PEqualNP.Outside.L_lib_1536_aux
open scoped Classical
variable {α : Type} [Fintype α] [DecidableEq α]
abbrev Pin (α : Type) := α × Bool
def pins (P : Finset (Pin α)) (C : Finset α) := ∀a∈P,decide (a.1∈C)=a.2
def good (E : α → α → Prop) (w : α → Nat) (B : Nat) (P : Finset (Pin α)) :=
  ∃ C,covers E C ∧ C.sum w≤B ∧ pins P C
theorem pinDown {A B : Finset (Pin α)} {C : Finset α} (sub : A⊆B) (h : pins B C) : pins A C := fun a ha => h a (sub ha)
def need (E : α → α → Prop) (v : α) (q : Pin α) := (q.2=true ∧ q.1=v) ∨ (q.2=false ∧ (E q.1 v ∨ E v q.1))
theorem needed {C : Finset α} {E : α → α → Prop} (h : covers E C) {a : Pin α} {v} (rel : need E v a)
    (pin : decide (a.1∈C)=a.2) : v∈C := by
  rcases rel with ⟨b,rfl⟩|⟨b,ed⟩
  · rw [b] at pin;exact of_decide_eq_true pin
  · rw [b] at pin;have absent := of_decide_eq_false pin
    rcases ed with ed|ed
    · exact (h _ _ ed).resolve_left absent
    · exact (h _ _ ed).resolve_right absent
theorem signedCore (E : α → α → Prop) (w : α → Nat) (opt r g : Nat) (W : Finset (Pin α))
    (slack : ∀ y,halfC E y → 2*opt≤price w y+g) (bad : ¬good E w (opt+r) W) :
    ∃ V⊆W,V.card≤g+2*(r+1) ∧ ¬good E w (opt+r) V := by
  classical
  let N := Finset.univ.filter (fun v : α => (v,false)∈W)
  let U := Finset.univ.filter (fun v => ∃a∈W,need E v a)
  have memU v : v∈U ↔ ∃a∈W,need E v a := by simp [U]
  by_cases coll : ∃v,v∈N ∧ v∈U
  · obtain ⟨v,hv,hu⟩:=coll;obtain ⟨a,ha,use⟩:=(memU v).mp hu
    have neg : (v,false)∈W := (Finset.mem_filter.mp hv).2
    let V : Finset (Pin α) := {a,(v,false)}
    have size : V.card≤2 := Finset.card_le_two
    refine ⟨V,?_,by omega,?_⟩
    · exact Finset.insert_subset ha (Finset.singleton_subset_iff.mpr neg)
    · rintro ⟨C,h,_,set⟩
      have yes:=needed h use (set a (by simp [V]))
      have no:=set (v,false) (by simp [V])
      simpa [yes] using no
  have dis : Disjoint U N := Finset.disjoint_left.mpr (fun v hu hn => coll ⟨v,hn,hu⟩)
  have fail : ¬affordable E w (opt+r) U := by
    rintro ⟨C,h,bill,sub⟩
    have keep {v} (hu : v∈U) : v∈C\N := Finset.mem_sdiff.mpr ⟨sub hu,fun hn => Finset.disjoint_left.mp dis hu hn⟩
    refine bad ⟨C\N,?_,(Finset.sum_le_sum_of_subset (f:=w) Finset.sdiff_subset).trans bill,?_⟩
    · intro x y ed
      by_cases xn : x∈N
      · exact Or.inr (keep ((memU y).mpr ⟨(x,false),(Finset.mem_filter.mp xn).2,Or.inr ⟨rfl,Or.inl ed⟩⟩))
      by_cases yn : y∈N
      · exact Or.inl (keep ((memU x).mpr ⟨(y,false),(Finset.mem_filter.mp yn).2,Or.inr ⟨rfl,Or.inr ed⟩⟩))
      exact (h x y ed).imp (fun hx => Finset.mem_sdiff.mpr ⟨hx,xn⟩) (fun hy => Finset.mem_sdiff.mpr ⟨hy,yn⟩)
    · rintro ⟨v,b⟩ hp;cases b
      · have hv : v∈N := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩
        simp [hv]
      · exact decide_eq_true (keep ((memU v).mpr ⟨(v,true),hp,Or.inl ⟨rfl,rfl⟩⟩))
  obtain ⟨T,sub,small,obstruction⟩:=positiveCore _ _ _ _ _ _ slack fail
  have repr (v : ↥T) : ∃a∈W,need E v.val a := (memU v.val).mp (sub v.property)
  choose f inside forces using repr
  let V := Finset.univ.image f
  refine ⟨V,?_,?_,?_⟩
  · intro a ha;obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp ha;exact inside v
  · exact (Finset.card_image_le.trans (by simpa using small) : V.card≤_)
  · rintro ⟨C,h,bill,set⟩;apply obstruction ⟨C,h,bill,?_⟩
    intro v hv;let t : ↥T := ⟨v,hv⟩
    exact needed h (forces t) (set (f t) (Finset.mem_image_of_mem _ (Finset.mem_univ t)))
theorem withFixed (E : α → α → Prop) (w : α → Nat) (opt r g : Nat) (P Q : Finset (Pin α))
    (slack : ∀ y,halfC E y → 2*opt≤price w y+g) (bad : ¬good E w (opt+r) (P∪Q)) :
    ∃ T⊆Q,T.card≤g+2*(r+1) ∧ ¬good E w (opt+r) (P∪T) := by
  classical
  obtain ⟨V,sub,small,no⟩:=signedCore _ _ _ _ _ _ slack bad
  refine ⟨V∩Q,Finset.inter_subset_right,(Finset.card_le_card Finset.inter_subset_left).trans small,?_⟩
  rintro ⟨C,h,b,p⟩;apply no ⟨C,h,b,pinDown ?_ p⟩
  intro x hx;rcases Finset.mem_union.mp (sub hx) with hp|hq
  · exact Finset.mem_union_left _ hp
  · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx,hq⟩)
end PEqualNP.Outside.L_lib_1536_aux

namespace PEqualNP.Outside.L_lib_1536_aux.PathTools
open scoped Classical
variable {α : Type} [Fintype α] [DecidableEq α] {n : Nat}
noncomputable def graph (e : α ≃ Fin n) (R : α → α → Prop) :=
  Finset.univ.filter (fun p : Fin n × Fin n => p.1<p.2 ∧ (R (e.symm p.1) (e.symm p.2) ∨ R (e.symm p.2) (e.symm p.1)))
def Cov (G : Finset (Fin n × Fin n)) (C : Finset (Fin n)) := ∀t∈G,t.1∈C ∨ t.2∈C
def Bip (G : Finset (Fin n × Fin n)) (D S : Finset (Fin n)) :=
  ∀t∈G,t.1∉D → t.2∉D → (t.1∈S ↔ t.2∉S)
def Opt (G : Finset (Fin n × Fin n)) (w : Fin n → Nat) (C : Finset (Fin n)) := Cov G C ∧ ∀ B,Cov G B → C.sum w≤B.sum w
def Ind (R : α → α → Prop) (X : α → Bool) := ∀a b,R a b → ¬(X a=true ∧ X b=true)
def omitted (e : α ≃ Fin n) (C : Finset (Fin n)) (x : α) := decide (e x∉C)
def complement (e : α ≃ Fin n) (X : α → Bool) := Finset.univ.filter (fun i => X (e.symm i)=false)
theorem omitted_comp (e : α ≃ Fin n) (X : α → Bool) : omitted e (complement e X)=X := by
  funext x;cases hx : X x <;> simp [omitted,complement,hx]
theorem strictGraph (e : α ≃ Fin n) (R : α → α → Prop) : ∀t∈graph e R,t.1<t.2 :=
  fun _ h => (Finset.mem_filter.mp h).2.1
theorem graphCov (e : α ≃ Fin n) (R : α → α → Prop) (ir : ∀x,¬R x x) (C : Finset (Fin n)) :
    Cov (graph e R) C ↔ Ind R (omitted e C) := by
  constructor
  · intro h x y r both
    obtain ⟨a,b⟩ := both;simp only [omitted,decide_eq_true_eq] at a b
    have ne : e x≠e y := by intro eq;exact ir y (e.injective eq ▸ r)
    rcases lt_or_gt_of_ne ne with lt|gt
    · have inside : (e x,e y)∈graph e R := by simp [graph,lt,r]
      exact (h _ inside).elim a b
    · have inside : (e y,e x)∈graph e R := by simp [graph,gt,r]
      exact (h _ inside).elim b a
  · intro h t ht;by_contra! bad
    obtain ⟨_,_,r⟩ := Finset.mem_filter.mp ht
    have xx : omitted e C (e.symm t.1)=true := by simpa [omitted] using bad.1
    have yy : omitted e C (e.symm t.2)=true := by simpa [omitted] using bad.2
    rcases r with r|r
    · exact h _ _ r ⟨xx,yy⟩
    · exact h _ _ r ⟨yy,xx⟩
theorem compCovered (e : α ≃ Fin n) {R : α → α → Prop} (ir : ∀x,¬R x x) {X : α → Bool}
    (h : Ind R X) : Cov (graph e R) (complement e X) :=
  (graphCov e R ir _).mpr (by rwa [omitted_comp])
def gain (w : α → Nat) (X : α → Bool) := ∑x,if X x then w x else 0
theorem costId (e : α ≃ Fin n) (w : α → Nat) (C : Finset (Fin n)) :
    C.sum (fun i => w (e.symm i)) + gain w (omitted e C) = ∑x,w x := by
  classical
  let amt (i : Fin n) := w (e.symm i)
  have eq1 : gain w (omitted e C) = ∑i : Fin n,if i∈C then 0 else amt i := by
    rw [←e.sum_comp]; unfold gain;apply Finset.sum_congr rfl;intro x _
    by_cases h : e x∈C <;> simp [amt,omitted,h]
  have eq2 : ∑x,w x=∑i,amt i := by rw [←e.sum_comp];simp [amt]
  rw [eq1,eq2]
  have cf : C=Finset.univ.filter (fun x => x∈C) := by ext;simp
  calc
    _ = (Finset.univ.filter (fun x => x∈C)).sum amt+(∑i : Fin n,if i∈C then 0 else amt i) := by rw [←cf]
    _ = _ := by
      simp only [Finset.sum_filter,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl;intro i _;by_cases hi : i∈C <;> simp [hi]
def mark (e : α ≃ Fin n) (b : α → Bool) := Finset.univ.filter (fun i => b (e.symm i)=true)
theorem mem_mark (e : α ≃ Fin n) (b : α → Bool) (i) : i∈mark e b ↔ b (e.symm i)=true := by simp [mark]
theorem graphBip (e : α ≃ Fin n) (R : α → α → Prop) (D S : α → Bool)
    (cross : ∀ x y,R x y → D x=false → D y=false → S x = !S y) :
    Bip (graph e R) (mark e D) (mark e S) := by
  intro t ht hx hy
  simp only [mem_mark,Bool.not_eq_true] at hx hy ⊢
  rcases (Finset.mem_filter.mp ht).2.2 with r|r
  · rw [cross _ _ r hx hy];cases S (e.symm t.2) <;> decide
  · rw [cross _ _ r hy hx];cases S (e.symm t.1) <;> decide
end PEqualNP.Outside.L_lib_1536_aux.PathTools

namespace PEqualNP.Outside.L_lib_1536_aux.PathTools
open scoped Classical
abbrev Line (m : Nat) := Fin m × Fin 4
def nextV (a b : Fin 4) := b.val=a.val+1
instance (a b : Fin 4) : Decidable (nextV a b) := by unfold nextV;infer_instance
def pathEdge (x y : Line m) := x.1=y.1 ∧ nextV x.2 y.2
def lineOK (q : Fin 4 → Bool) := ∀a b,nextV a b → ¬(q a=true ∧ q b=true)
instance (q : Fin 4 → Bool) : Decidable (lineOK q) := by unfold lineOK;infer_instance
def worth (q : Fin 4 → Bool) := ∑a,if q a then 1 else 0
def leafAt (b : Bool) : Fin 4 := if b then 3 else 0
def pick (mask : Nat) (a : Fin 4) := mask.testBit a.val
def fixLeaf (s : Bool) := if s then pick 10 else pick 5
def lineSide (a : Fin 4) := a.val.testBit 0
theorem nextSide : ∀a b,nextV a b → lineSide a = !lineSide b := by decide +kernel
theorem noNext : ∀a,¬nextV a a := by decide +kernel
theorem smallDeg : ∀ a : Fin 4,(Finset.univ.filter (fun b => nextV a b ∨ nextV b a)).card≤2 := by decide +kernel
theorem lineBound : ∀q,lineOK q → worth q≤2 := by decide +kernel
theorem constrained : ∀q,lineOK q → (∀s,q (leafAt s)=false) → worth q≤1 := by decide +kernel
theorem baseline : lineOK (pick 9) ∧ worth (pick 9)=2 := by decide +kernel
theorem allPinned : lineOK (pick 2) ∧ worth (pick 2)=1 ∧ ∀s,pick 2 (leafAt s)=false := by decide +kernel
theorem released : ∀s,lineOK (fixLeaf s) ∧ worth (fixLeaf s)=2 ∧ ∀t,fixLeaf s (leafAt t)=true ↔ t=s := by decide +kernel
theorem leafInj : Function.Injective leafAt := by intro a b;cases a <;> cases b <;> decide
theorem lineIr (v : Line m) : ¬pathEdge v v := fun h => noNext _ h.2
def site (e : Line m ≃ Fin n) (v : Fin m × Bool) := e (v.1,leafAt v.2)
def leaves (e : Line m ≃ Fin n) := Finset.univ.image (site e)
theorem leafCount (e : Line m ≃ Fin n) : (leaves e).card=2*m := by
  rw [leaves,Finset.card_image_of_injective]
  · simp [Nat.mul_comm]
  · intro i j eq; have h:=e.injective eq;exact Prod.ext (congrArg (fun x : Line m => x.1) h) (leafInj (congrArg (fun x : Line m => x.2) h))
theorem pathOrient (e : Line m ≃ Fin n) : Bip (graph e pathEdge) ∅ (mark e (fun x => lineSide x.2)) := by
  have hz : mark e (fun _ => false)=∅ := by ext;simp [mark]
  rw [←hz];apply graphBip;intro x y h _ _;exact nextSide _ _ h.2
theorem indRow {X : Line m → Bool} (h : Ind pathEdge X) (i) : lineOK (fun a => X (i,a)) :=
  fun a b r => h _ _ ⟨rfl,r⟩
theorem byRows {X : Line m → Bool} (h : ∀i,lineOK (fun a => X (i,a))) : Ind pathEdge X := by
  rintro ⟨i,a⟩ ⟨j,b⟩ ⟨rfl,r⟩;exact h _ _ _ r
theorem readRows (X : Line m → Bool) : gain (fun _ => 1) X = ∑i,worth (fun a => X (i,a)) := by
  unfold gain worth;rw [Fintype.sum_prod_type]
theorem pathMax {X : Line m → Bool} (h : Ind pathEdge X) : gain (fun _ => 1) X ≤ m*2 := by
  rw [readRows];simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => lineBound _ (indRow h i))
theorem pinnedMax {X : Line m → Bool} (h : Ind pathEdge X) (q : ∀i s,X (i,leafAt s)=false) : gain (fun _ => 1) X ≤ m := by
  rw [readRows];simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => constrained _ (indRow h i) (q i))
def simplePolicy (mask : Nat) (v : Line m) := pick mask v.2
def partialPolicy (v : Fin m × Bool) (x : Line m) := if x.1=v.1 then fixLeaf v.2 x.2 else pick 2 x.2
theorem oneInd (v : Fin m × Bool) : Ind pathEdge (partialPolicy v) := by
  apply byRows;intro i;by_cases h : i=v.1
  · simpa only [partialPolicy,h,ite_true] using (released v.2).1
  · simpa only [partialPolicy,h,ite_false] using allPinned.1
theorem oneGain (v : Fin m × Bool) : gain (fun _ => 1) (partialPolicy v)=m+1 := by
  rw [readRows]
  have hr (i) : worth (fun a => partialPolicy v (i,a))=1+(if i=v.1 then 1 else 0) := by
    by_cases h : i=v.1
    · simpa only [partialPolicy,h,ite_true] using (released v.2).2.1
    · simpa only [partialPolicy,h,ite_false,Nat.add_zero] using allPinned.2.1
  simp [hr,Finset.sum_add_distrib]
theorem oneHits (v u : Fin m × Bool) : partialPolicy v (u.1,leafAt u.2)=true ↔ u=v := by
  by_cases h : u.1=v.1
  · simp only [partialPolicy,h,ite_true,(released v.2).2.2,Prod.ext_iff,h,true_and]
  · simp [partialPolicy,h,allPinned.2.2,Prod.ext_iff]
end PEqualNP.Outside.L_lib_1536_aux.PathTools

namespace PEqualNP.Outside.L_lib_1536_aux
open scoped Classical
open PathTools
abbrev K (g : Nat) := Fin 2 ⊕ Fin g
abbrev V (g r : Nat) := K g ⊕ Line r
abbrev Label (g r : Nat) := K g ⊕ (Fin r × Bool)
def idx : Label g r → V g r
  | .inl a => .inl a
  | .inr (i,b) => .inr (i,leafAt b)
theorem idxInj : Function.Injective (@idx g r) := by
  intro x y;cases x with
  | inl x => cases y <;> simp [idx]
  | inr x =>
    cases y with
    | inl y => simp [idx]
    | inr y => simp [idx,Prod.ext_iff,leafInj.eq_iff]
def rel : V g r → V g r → Prop
  | .inl a,.inl b => a≠b
  | .inr a,.inr b => pathEdge a b
  | _,_ => False
theorem ir (x : V g r) : ¬rel x x := by cases x <;> first | exact lineIr _ | exact fun h => h rfl
theorem joint (a : K g → Bool) (b : Line r → Bool)
    (ha : ∀x y,a x=true → a y=true → x=y) (hb : Ind pathEdge b) : Ind rel (Sum.elim a b) := by
  intro x y h p;cases x <;> cases y <;> first | exact h (ha _ _ p.1 p.2) | exact hb _ _ h p | exact h
def single (t : K g) (x : K g) := decide (x=t)
theorem singleOK (t : K g) : ∀x y,single t x=true → single t y=true → x=y := by simp [single]
theorem singleGain (t : K g) : gain (fun _ => 1) (single t)=1 := by simp [gain,single]
theorem splitGain (X : V g r → Bool) : gain (fun _ => 1) X =
    gain (fun _ => 1) (fun x => X (.inl x)) + gain (fun _ => 1) (fun x => X (.inr x)) := by
  unfold gain;exact Fintype.sum_sum_type _
theorem cliqueMax {X : V g r → Bool} (ok : Ind rel X) : gain (fun _ => 1) (fun x => X (.inl x)) ≤ 1 := by
  let A := Finset.univ.filter (fun a : K g => X (.inl a)=true)
  have size : A.card≤1 := by
    apply Finset.card_le_one.mpr;intro a ha b hb
    by_contra ne;exact ok (.inl a) (.inl b) ne ⟨(Finset.mem_filter.mp ha).2,(Finset.mem_filter.mp hb).2⟩
  simpa [gain,A] using size
theorem upperGain {X : V g r → Bool} (ok : Ind rel X) : gain (fun _ => 1) X≤1+r*2 := by
  rw [splitGain];exact Nat.add_le_add (cliqueMax ok) (pathMax (fun x y h => ok (.inr x) (.inr y) h))
theorem forcedGain {X : V g r → Bool} (ok : Ind rel X) (q : ∀l,X (idx l)=false) : gain (fun _ => 1) X≤r := by
  have zero (x : K g) : X (.inl x)=false := q (.inl x)
  rw [splitGain];simp only [zero,Bool.false_eq_true,ite_false,gain,Finset.sum_const_zero,Nat.zero_add]
  exact pinnedMax (fun x y h => ok (.inr x) (.inr y) h) (fun i b => q (.inr (i,b)))
theorem pathConstantOK {m} (mask) (h : lineOK (pick mask)) : Ind (@pathEdge m) (simplePolicy mask) := by
  apply byRows;intro i;exact h
theorem pathConstantGain {m} (mask) : gain (fun _ => 1) (@simplePolicy m mask)=m*worth (pick mask) := by
  rw [readRows];simp [simplePolicy]
theorem baseChoice (g r : Nat) : ∃ X : V g r → Bool,Ind rel X ∧ gain (fun _ => 1) X=1+r*2 := by
  let t : K g := .inl 0
  refine ⟨Sum.elim (single t) (simplePolicy 9),joint _ _ (singleOK t) (pathConstantOK _ baseline.1),?_⟩
  rw [splitGain];change gain _ (single t)+gain _ (simplePolicy 9)=_
  rw [singleGain,pathConstantGain,baseline.2]
theorem releaseChoice (l : Label g r) : ∃ X : V g r → Bool,Ind rel X ∧
    (∀u,u≠l → X (idx u)=false) ∧ gain (fun _ => 1) X=r+1 := by
  cases l with
  | inl t =>
    refine ⟨Sum.elim (single t) (simplePolicy 2),joint _ _ (singleOK t) (pathConstantOK _ allPinned.1),?_,?_⟩
    · intro u ne;cases u with
      | inl v => simpa [single,idx] using ne
      | inr v => exact allPinned.2.2 v.2
    · rw [splitGain];change gain _ (single t)+gain _ (simplePolicy 2)=_
      rw [singleGain,pathConstantGain,allPinned.2.1];omega
  | inr v =>
    refine ⟨Sum.elim (fun _ => false) (partialPolicy v),joint _ _ (by simp) (oneInd v),?_,?_⟩
    · intro u ne;cases u with
      | inl x => rfl
      | inr x =>
        have h : x≠v := fun eq => ne (congrArg Sum.inr eq)
        change partialPolicy v (x.1,leafAt x.2)=false
        simpa only [Bool.not_eq_true] using (oneHits v x).not.mpr h
    · rw [splitGain];change gain _ (fun _ : K g => false)+gain _ (partialPolicy v)=_
      rw [oneGain];simp [gain]
def deleted : V g r → Bool
  | .inl (.inr _) => true
  | _ => false
def shore : V g r → Bool
  | .inl (.inl x) => decide (x=0)
  | .inr x => lineSide x.2
  | _ => false
theorem crossing (x y : V g r) (h : rel x y) (hx : deleted x=false) (hy : deleted y=false) : shore x = !shore y := by
  cases x with
  | inr x => cases y with
    | inr y => exact nextSide _ _ h.2
    | inl y => exact False.elim h
  | inl x => cases y with
    | inr y => exact False.elim h
    | inl y =>
      cases x with
      | inr a => contradiction
      | inl a =>
        cases y with
        | inr b => contradiction
        | inl b => fin_cases a <;> fin_cases b <;> first | rfl | exact False.elim (h rfl)
def pathHue (x : Fin 4) : Fin 3 := if pick 9 x then 0 else 2
def tightHue : V g r → Fin 3 := Sum.elim (fun _ => 1) (fun x => pathHue x.2)
theorem validHue (x y : V g r) (h : rel x y) : 2≤(tightHue x).val+(tightHue y).val := by
  cases x <;> cases y <;> first | exact False.elim h | exact (by decide : 2≤(1 : Fin 3).val+(1 : Fin 3).val) | exact (show ∀a b,nextV a b → 2≤(pathHue a).val+(pathHue b).val by decide +kernel) _ _ h.2
theorem hueSum (g r : Nat) : (∑x : V g r,(tightHue x).val)=2+g+r*4 := by
  have path : (∑a,(pathHue a).val)=4 := by decide +kernel
  simp [Fintype.sum_sum_type,Fintype.sum_prod_type,tightHue,path]
end PEqualNP.Outside.L_lib_1536_aux

namespace PEqualNP.Outside.L_lib_1536_aux
open scoped Classical
open PathTools
def edge {n} (G : Finset (Fin n × Fin n)) (x y : Fin n) := (x,y)∈G
theorem covEdge {n} {G : Finset (Fin n × Fin n)} {C} : Cov G C ↔ covers (edge G) C :=
  ⟨fun h x y r => h _ r,fun h t r => h t.1 t.2 r⟩
def Slack {n} (G : Finset (Fin n × Fin n)) (w : Fin n → Nat) (C : Finset (Fin n)) (g : Nat) :=
  ∀y : Fin n → Hue,(∀t∈G,2≤(y t.1).val+(y t.2).val) → 2*C.sum w≤price w y+g
def rnd (a : Hue) (d s f : Bool) := decide (a=2) || (decide (a=1) && (d || (s == f)))
theorem edgeRound : ∀(a b : Hue) (d e s t f : Bool),2≤a.val+b.val →
    (d=false → e=false → (s=true ↔ t=false)) → rnd a d s f=true ∨ rnd b e t f=true := by decide +kernel
theorem billRound : ∀(a : Hue) (d s : Bool),(rnd a d s true).toNat+(rnd a d s false).toNat≤a.val+d.toNat := by decide +kernel
theorem boolBill {α : Type} [Fintype α] (w : α → Nat) (p : α → Bool) :
    (Finset.univ.filter (fun v => p v=true)).sum w=∑v,w v*(p v).toNat := by
  rw [Finset.sum_filter];apply Finset.sum_congr rfl;intro v _;cases h:p v <;> simp
theorem rounding {n} {G : Finset (Fin n × Fin n)} {w : Fin n → Nat} {C0 D S : Finset (Fin n)}
    (ho : Opt G w C0) (hb : Bip G D S) : Slack G w C0 (D.sum w) := by
  classical
  intro y hy
  let d (v : Fin n) := decide (v∈D)
  let s (v : Fin n) := decide (v∈S)
  let p f v := rnd (y v) (d v) (s v) f
  let c f := Finset.univ.filter (fun v => p f v=true)
  have cheap f : C0.sum w≤(c f).sum w := by
    apply ho.2
    intro t ht
    have h:=edgeRound (y t.1) (y t.2) (d t.1) (d t.2) (s t.1) (s t.2) f (hy t ht) (by
      intro hd he
      simpa [s] using hb t ht (of_decide_eq_false hd) (of_decide_eq_false he))
    simpa [c,p] using h
  have sumD : (∑v,w v*(d v).toNat)=D.sum w := by rw [←boolBill];simp [d]
  have bounds := Finset.sum_le_sum (s:=Finset.univ) (fun v _ => Nat.mul_le_mul_left (w v) (billRound (y v) (d v) (s v)))
  change (∑v,w v*((p true v).toNat+(p false v).toNat)) ≤ ∑v,w v*((y v).val+(d v).toNat) at bounds
  simp only [Nat.mul_add,Finset.sum_add_distrib,sumD] at bounds
  have bill f : (c f).sum w=∑v,w v*(p f v).toNat := boolBill _ _
  have htrue:=cheap true
  have hfalse:=cheap false
  rw [bill] at htrue hfalse
  unfold price
  omega
end PEqualNP.Outside.L_lib_1536_aux

namespace PEqualNP.Outside.L_lib_1536_aux
open scoped Classical
open PathTools
set_option maxHeartbeats 2000000 in
theorem sharpExample (g r : Nat) : ∃ (n : Nat) (G : Finset (Fin n × Fin n)) (D S C0 Q : Finset (Fin n)),
  (∀ t∈G,t.1<t.2) ∧ Opt G (fun _ => 1) C0 ∧ D.card=g ∧ Bip G D S ∧
  Slack G (fun _ => 1) C0 g ∧
  (∃ y : Fin n → Hue,(∀ t∈G,2≤(y t.1).val+(y t.2).val) ∧ (∑ v,(y v).val)+g=2*C0.card) ∧
  Q.card=g+2*(r+1) ∧ (∀ C,Cov G C → Q⊆C → C0.card+r<C.card) ∧
  ∀q∈Q,∃ C,Cov G C ∧ Q.erase q⊆C ∧ C.card≤C0.card+r := by
  classical
  let n := 2+g+r*4
  let e : V g r ≃ Fin n := Fintype.equivFinOfCardEq (by simp [n,V,K,Line])
  let G := graph e rel
  let w (_ : V g r) := 1
  have bill (C : Finset (Fin n)) : C.card+gain w (omitted e C)=2+g+r*4 := by simpa [w,V,K,Line] using costId e w C
  have cost (X : V g r → Bool) : (complement e X).card+gain w X=2+g+r*4 := by simpa only [omitted_comp] using bill (complement e X)
  obtain ⟨X,hX,maxX⟩:=baseChoice g r
  let C0 := complement e X
  have base : C0.card=1+g+r*2 := by have h:=cost X;change gain w X=_ at maxX;change C0.card+_=_ at h;omega
  have opt : Opt G (fun _ => 1) C0 := by
    refine ⟨compCovered e ir hX,?_⟩
    intro C h
    have bound:=upperGain ((graphCov e _ ir C).mp h)
    have total:=bill C
    change gain w (omitted e C)≤_ at bound
    simp only [Finset.sum_const,Nat.nsmul_eq_mul,Nat.mul_one];omega
  let del (j : Fin g) : Fin n := e (.inl (.inr j))
  have dmem : mark e deleted=Finset.univ.image del := by
    ext i
    obtain ⟨x,rfl⟩:=e.surjective i
    rw [mem_mark,Equiv.symm_apply_apply]
    cases x with
    | inr x => simp [deleted,del]
    | inl x => cases x <;> simp [deleted,del]
  have dcard : (mark e deleted).card=g := by
    rw [dmem,Finset.card_image_of_injective _ (by intro x y h;exact Sum.inr.inj (Sum.inl.inj (e.injective h)))]
    simp
  have bip := graphBip e rel deleted shore crossing
  let loc (l : Label g r) := e (idx l)
  have inj : Function.Injective loc := e.injective.comp idxInj
  let Q := Finset.univ.image loc
  have card : Q.card=g+2*(r+1) := by
    rw [show Q=Finset.univ.image loc from rfl,Finset.card_image_of_injective _ inj]
    simp [Label,K];omega
  refine ⟨n,G,mark e deleted,mark e shore,C0,Q,strictGraph _ _,opt,dcard,bip,?_,?_,card,?_,?_⟩
  · simpa [dcard] using rounding opt bip
  · let y (i : Fin n) := tightHue (e.symm i)
    refine ⟨y,?_,?_⟩
    · intro t ht
      rcases (Finset.mem_filter.mp ht).2.2 with h|h
      · exact validHue _ _ h
      · change 2≤(tightHue (e.symm t.1)).val+(tightHue (e.symm t.2)).val
        rw [Nat.add_comm];exact validHue _ _ h
    · have total : (∑v,(y v).val)=2+g+r*4 := by rw [←e.sum_comp];simpa [y] using hueSum g r
      omega
  · intro C h sub
    have p (l : Label g r) : omitted e C (idx l)=false := by
      have hl:=sub (Finset.mem_image_of_mem loc (Finset.mem_univ l))
      simpa [omitted,loc] using hl
    have bound:=forcedGain ((graphCov e rel ir C).mp h) p
    change gain w (omitted e C)≤_ at bound
    have total:=bill C;omega
  · intro q hq
    obtain ⟨l,_,rfl⟩:=Finset.mem_image.mp hq
    obtain ⟨Y,ok,other,gainY⟩:=releaseChoice l
    refine ⟨complement e Y,compCovered _ ir ok,?_,?_⟩
    · intro a ha;obtain ⟨ne,mem⟩:=Finset.mem_erase.mp ha
      obtain ⟨u,_,rfl⟩:=Finset.mem_image.mp mem
      simpa [complement,loc] using other u (fun eq => ne (congrArg loc eq))
    · have total:=cost Y;change gain w Y=_ at gainY;omega
end PEqualNP.Outside.L_lib_1536_aux

namespace PEqualNP.Outside.L_lib_1536_aux
open PathTools
noncomputable def fixedErase {α : Type*} (A : Finset α) (a : α) := @Finset.erase α (Classical.decEq α) A a
theorem eraseUnique {α : Type*} (d : DecidableEq α) (A : Finset α) (a : α) :
    @Finset.erase α d A a=fixedErase A a := by ext;simp only [fixedErase,Finset.mem_erase]
noncomputable def sameDecision (P : Prop) := @decide P (Classical.propDecidable P)
theorem decUnique (P : Prop) (d : Decidable P) : @decide P d=sameDecision P := by unfold sameDecision;congr 1
theorem unionSame {α : Type} (d e : DecidableEq α) (A B : Finset α) : @max _ (@Finset.instMax α d) A B = @max _ (@Finset.instMax α e) A B := by ext;simp only [Finset.mem_union]
theorem goodEdges {n} (G : Finset (Fin n × Fin n)) (w : Fin n → Nat) (B) (P : Finset (Fin n × Bool)) :
    good (edge G) w B P ↔ ∃ C,Cov G C ∧ C.sum w≤B ∧ pins P C := by
  unfold good;simp only [covEdge]
end PEqualNP.Outside.L_lib_1536_aux
open PEqualNP.Outside.L_lib_1536_aux PEqualNP.Outside.L_lib_1536_aux.PathTools in
theorem PEqualNP.Outside.L_lib_1536 : letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let cover := fun {N : Nat} (G : Finset (Fin N × Fin N)) (C : Finset (Fin N)) =>
  ∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C
let opt := fun {N : Nat} (G : Finset (Fin N × Fin N)) (w : Fin N → Nat) (C : Finset (Fin N)) =>
  cover G C ∧ ∀ B, cover G B → C.sum w ≤ B.sum w
let bip := fun {N : Nat} (G : Finset (Fin N × Fin N)) (D S : Finset (Fin N)) =>
  ∀ e ∈ G, e.1 ∉ D → e.2 ∉ D → (e.1 ∈ S ↔ e.2 ∉ S)
let pins := fun {n : Nat} (Q : Finset (Fin n × Bool)) (C : Finset (Fin n)) =>
  ∀ a ∈ Q, decide (a.1 ∈ C)=a.2
let slack := fun {n : Nat} (G : Finset (Fin n × Fin n)) (w : Fin n → Nat)
  (C0 : Finset (Fin n)) (g : Nat) =>
  ∀ y : Fin n → Fin 3, (∀ e ∈ G, 2 ≤ (y e.1).val + (y e.2).val) →
    2*C0.sum w ≤ (∑ v : Fin n, w v * (y v).val) + g
let good := fun {n : Nat} (G : Finset (Fin n × Fin n)) (w : Fin n → Nat)
  (B : Nat) (P : Finset (Fin n × Bool)) => ∃ C, cover G C ∧ C.sum w ≤ B ∧ pins P C
(∀ (n : Nat) (G : Finset (Fin n × Fin n)) (w : Fin n → Nat) (C0 : Finset (Fin n)),
 (∀ e ∈ G, e.1 < e.2) → opt G w C0 →
 (∀ D S : Finset (Fin n), bip G D S → slack G w C0 (D.sum w)) ∧
 ∀ (r g : Nat) (P Q : Finset (Fin n × Bool)), slack G w C0 g →
   ¬ good G w (C0.sum w+r) (P ∪ Q) →
   ∃ T ⊆ Q, T.card ≤ g+2*(r+1) ∧ ¬ good G w (C0.sum w+r) (P ∪ T)) ∧
∀ g r : Nat, ∃ (n : Nat) (G : Finset (Fin n × Fin n)) (D S C0 Q : Finset (Fin n)),
  (∀ e ∈ G, e.1 < e.2) ∧ opt G (fun _ => 1) C0 ∧ D.card=g ∧ bip G D S ∧
  slack G (fun _ => 1) C0 g ∧
  (∃ y : Fin n → Fin 3, (∀ e ∈ G, 2 ≤ (y e.1).val+(y e.2).val) ∧
    (∑ v : Fin n, (y v).val)+g=2*C0.card) ∧
  Q.card=g+2*(r+1) ∧
  (∀ C, cover G C → Q ⊆ C → C0.card+r < C.card) ∧
  ∀ q ∈ Q, ∃ C, cover G C ∧ Q.erase q ⊆ C ∧ C.card ≤ C0.card+r := by
  classical
  intro cover' opt' bip' pins' slack' good'
  constructor
  · intro n G w C0 _ opt0
    have ho : Opt G w C0 := opt0
    constructor
    · intro D S hb;exact rounding ho hb
    · intro r g P Q hs bad
      have hsl (y) (h : halfC (edge G) y) : 2*C0.sum w≤price w y+g :=
        hs y (fun t ht => h _ _ ht)
      have goodIff (A : Finset (Fin n × Bool)) : good (edge G) w (C0.sum w+r) A ↔ good' G w (C0.sum w+r) A := by
        rw [goodEdges];simp only [good',cover',pins',Cov,pins,decUnique]
      obtain ⟨T,sub,count,fail⟩:=withFixed (edge G) w (C0.sum w) r g P Q hsl (by
        intro h;apply bad;apply (goodIff _).mp;convert h using 1;exact unionSame _ _ _ _)
      refine ⟨T,sub,count,?_⟩;intro h;apply fail;apply (goodIff _).mpr;convert h using 1;exact unionSame _ _ _ _
  · intro g r
    simpa only [opt',Opt,cover',Cov,bip',Bip,slack',Slack,price,eraseUnique] using sharpExample g r
