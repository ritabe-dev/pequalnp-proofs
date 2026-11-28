import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1576_aux
abbrev W := Finset (Fin 3)
def row (k : Nat) : W := Finset.univ.filter (fun j => k.testBit j.val)
def ov (u : W → Nat) (j : Fin 3) := (Finset.univ.filter (fun x : W => j∉x)).sum (fun x => min (u x) (u (insert j x)))
theorem sumCube (u : W → Nat) : (∑ x,u x) = u (row 0) + u (row 1) + u (row 2) + u (row 3) + u (row 4) + u (row 5) + u (row 6) + u (row 7) := by
  rw [show (Finset.univ : Finset W) = {row 0,row 1,row 2,row 3,row 4,row 5,row 6,row 7} by decide +kernel]
  simp (disch := decide +kernel) only [Finset.sum_insert,Finset.sum_singleton]
  omega
theorem axis0 (u : W → Nat) : ov u 0 = min (u (row 0)) (u (row 1)) + min (u (row 2)) (u (row 3)) + min (u (row 4)) (u (row 5)) + min (u (row 6)) (u (row 7)) := by
  unfold ov
  rw [show (Finset.univ.filter (fun x : W => (0 : Fin 3)∉x)) = {row 0,row 2,row 4,row 6} by decide +kernel]
  have h0 : insert (0 : Fin 3) (row 0) = row 1 := by decide +kernel
  have h2 : insert (0 : Fin 3) (row 2) = row 3 := by decide +kernel
  have h4 : insert (0 : Fin 3) (row 4) = row 5 := by decide +kernel
  have h6 : insert (0 : Fin 3) (row 6) = row 7 := by decide +kernel
  simp (disch := decide +kernel) only [Finset.sum_insert,Finset.sum_singleton,h0,h2,h4,h6]
  omega
theorem axis1 (u : W → Nat) : ov u 1 = min (u (row 0)) (u (row 2)) + min (u (row 1)) (u (row 3)) + min (u (row 4)) (u (row 6)) + min (u (row 5)) (u (row 7)) := by
  unfold ov
  rw [show (Finset.univ.filter (fun x : W => (1 : Fin 3)∉x)) = {row 0,row 1,row 4,row 5} by decide +kernel]
  have h0 : insert (1 : Fin 3) (row 0) = row 2 := by decide +kernel
  have h1 : insert (1 : Fin 3) (row 1) = row 3 := by decide +kernel
  have h4 : insert (1 : Fin 3) (row 4) = row 6 := by decide +kernel
  have h5 : insert (1 : Fin 3) (row 5) = row 7 := by decide +kernel
  simp (disch := decide +kernel) only [Finset.sum_insert,Finset.sum_singleton,h0,h1,h4,h5]
  omega
theorem axis2 (u : W → Nat) : ov u 2 = min (u (row 0)) (u (row 4)) + min (u (row 1)) (u (row 5)) + min (u (row 2)) (u (row 6)) + min (u (row 3)) (u (row 7)) := by
  unfold ov
  rw [show (Finset.univ.filter (fun x : W => (2 : Fin 3)∉x)) = {row 0,row 1,row 2,row 3} by decide +kernel]
  have h0 : insert (2 : Fin 3) (row 0) = row 4 := by decide +kernel
  have h1 : insert (2 : Fin 3) (row 1) = row 5 := by decide +kernel
  have h2 : insert (2 : Fin 3) (row 2) = row 6 := by decide +kernel
  have h3 : insert (2 : Fin 3) (row 3) = row 7 := by decide +kernel
  simp (disch := decide +kernel) only [Finset.sum_insert,Finset.sum_singleton,h0,h1,h2,h3]
  omega
theorem balanced (a b c d e f g h : Nat) (mass : a+b+c+d+e+f+g+h=4)
    (full : 2 ≤ min a b+min c d+min e f+min g h) : a=b ∧ c=d ∧ e=f ∧ g=h := by omega
theorem upper (u : W → Nat) (mass : (∑x,u x)=4) (j : Fin 3) : ov u j≤2 := by
  rw [sumCube] at mass
  have cases : j=0 ∨ j=1 ∨ j=2 := by omega
  rcases cases with rfl|rfl|rfl
  · rw [axis0];omega
  · rw [axis1];omega
  · rw [axis2];omega
end PEqualNP.Outside.L_lib_1576_aux

namespace PEqualNP.Outside.L_lib_1576_aux
open scoped Classical
abbrev Profile := W → Fin 5
def mass (p : Profile) := ∑x,(p x).val
def flip (p : Profile) := ov (fun x => (p x).val)
def light (j : Fin 3) (A : W) (x : W) : Fin 5 := if x=A ∨ x=insert j A then 1 else 0
theorem lightFacts : ∀j A,j∉A → mass (light j A)=2 ∧ ∀i,flip (light j A) i=if i=j then 1 else 0 := by decide +kernel
theorem lightUnique : ∀j A B,j∉A → j∉B → light j A=light j B → A=B := by decide +kernel
theorem lightCount (j : Fin 3) : (Finset.univ.filter (fun A : W => j∉A)).card=4 := by fin_cases j <;> decide +kernel
theorem getLight (p : Profile) (j : Fin 3) (m : mass p=2) (hit : 0<flip p j) :
    ∃ A : W,j∉A ∧ p=light j A := by
  classical
  change (∑x,(p x).val)=2 at m
  let support := Finset.univ.filter (fun A : W => j∉A)
  have ex : ∃A∈support,0 < min (p A).val (p (insert j A)).val := by
    by_contra! no
    have zero : support.sum (fun A => min (p A).val (p (insert j A)).val)=0 :=
      Finset.sum_eq_zero (fun x hx => Nat.eq_zero_of_le_zero (no x hx))
    change 0<support.sum (fun A => min (p A).val (p (insert j A)).val) at hit;omega
  obtain ⟨A,ha,good⟩:=ex
  have out:=(Finset.mem_filter.mp ha).2
  let B := insert j A
  have ne : A≠B := fun eq => out (eq ▸ Finset.mem_insert_self j A)
  have sumTwo : (p A).val+(p B).val≤2 := by
    have bound:=Finset.sum_le_sum_of_subset (f:=fun x => (p x).val) (Finset.subset_univ ({A,B} : Finset W))
    simpa [ne,m] using bound
  change 0 < min (p A).val (p B).val at good
  have pA : (p A).val=1 := by omega
  have pB : (p B).val=1 := by omega
  refine ⟨A,out,?_⟩
  funext x
  by_cases h:x=A
  · subst x;apply Fin.ext;simpa [light] using pA
  by_cases k:x=B
  · subst x;apply Fin.ext;simpa [light,B] using pB
  have bound:=Finset.sum_le_sum_of_subset (f:=fun x => (p x).val) (Finset.subset_univ ({x,A,B} : Finset W))
  simp [h,k,ne,pA,pB,m] at bound
  apply Fin.ext;change (p x).val=(light j A x).val
  have lhs : (p x).val=0 := by omega
  simpa [light,h,show x≠insert j A from k] using lhs
theorem lightBudget (p : Profile) (m : mass p=2) : flip p 0+flip p 1+flip p 2≤1 := by
  by_cases h:∃j,0<flip p j
  · obtain ⟨j,hj⟩:=h;obtain ⟨A,ha,rfl⟩:=getLight p j m hj
    simp only [(lightFacts j A ha).2];fin_cases j <;> decide
  · push_neg at h;have := h 0;have :=h 1;have :=h 2;omega
def dir (s : Bool) : Fin 3 := if s then 2 else 1
def square (s b : Bool) (x : W) : Fin 5 := if decide (dir (!s)∈x)=b then 1 else 0
theorem squareFacts : ∀s b,mass (square s b)=4 ∧ flip (square s b) 0=2 ∧
    flip (square s b) (dir s)=2 ∧ flip (square s b) (dir (!s))=0 := by decide +kernel
theorem squareUnique : ∀s a b,square s a=square s b → a=b := by decide +kernel
theorem rowCases : ∀ x : W,x=row 0 ∨ x=row 1 ∨ x=row 2 ∨ x=row 3 ∨ x=row 4 ∨ x=row 5 ∨ x=row 6 ∨ x=row 7 := by decide +kernel
set_option maxHeartbeats 1500000 in
theorem getSquare (p : Profile) (s : Bool) (m : mass p=4) (first : 2≤flip p 0) (hit : 0<flip p (dir s)) :
    ∃ b,p=square s b := by
  change (∑x,(p x).val)=4 at m;rw [sumCube] at m
  unfold flip at first hit;rw [axis0] at first
  obtain ⟨e01,e23,e45,e67⟩:=balanced _ _ _ _ _ _ _ _ m first
  cases s <;> simp only [dir,Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true] at hit
  · rw [axis1] at hit
    by_cases left : (p (row 0)).val=1
    · refine ⟨false,?_⟩;funext x;apply Fin.ext
      rcases rowCases x with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · change (p (row 0)).val=1;omega
      · change (p (row 1)).val=1;omega
      · change (p (row 2)).val=1;omega
      · change (p (row 3)).val=1;omega
      · change (p (row 4)).val=0;omega
      · change (p (row 5)).val=0;omega
      · change (p (row 6)).val=0;omega
      · change (p (row 7)).val=0;omega
    · refine ⟨true,?_⟩;funext x;apply Fin.ext
      rcases rowCases x with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · change (p (row 0)).val=0;omega
      · change (p (row 1)).val=0;omega
      · change (p (row 2)).val=0;omega
      · change (p (row 3)).val=0;omega
      · change (p (row 4)).val=1;omega
      · change (p (row 5)).val=1;omega
      · change (p (row 6)).val=1;omega
      · change (p (row 7)).val=1;omega
  · rw [axis2] at hit
    by_cases left : (p (row 0)).val=1
    · refine ⟨false,?_⟩;funext x;apply Fin.ext
      rcases rowCases x with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · change (p (row 0)).val=1;omega
      · change (p (row 1)).val=1;omega
      · change (p (row 2)).val=0;omega
      · change (p (row 3)).val=0;omega
      · change (p (row 4)).val=1;omega
      · change (p (row 5)).val=1;omega
      · change (p (row 6)).val=0;omega
      · change (p (row 7)).val=0;omega
    · refine ⟨true,?_⟩;funext x;apply Fin.ext
      rcases rowCases x with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · change (p (row 0)).val=0;omega
      · change (p (row 1)).val=0;omega
      · change (p (row 2)).val=1;omega
      · change (p (row 3)).val=1;omega
      · change (p (row 4)).val=0;omega
      · change (p (row 5)).val=0;omega
      · change (p (row 6)).val=1;omega
      · change (p (row 7)).val=1;omega
theorem heavyBudget (p : Profile) (m : mass p=4) (first : 2≤flip p 0) : flip p 1+flip p 2≤2 := by
  by_cases h : 0<flip p 1
  · obtain ⟨b,rfl⟩:=getSquare p false m first h
    have facts:=squareFacts false b;change _ ∧ _ ∧ flip _ 1=2 ∧ flip _ 2=0 at facts;omega
  · have up:=upper (fun x => (p x).val) m (2 : Fin 3);change flip p 2≤2 at up;omega
end PEqualNP.Outside.L_lib_1576_aux

namespace PEqualNP.Outside.L_lib_1576_aux
open scoped Classical
def fiber (f : Fin m → Fin n) (a : Fin n) := Finset.univ.filter (fun t => f t=a)
def len (f : Fin m → Fin n) (a) := (fiber f a).card
def ord (f : Fin m → Fin n) (a) : Fin (len f a) ≃o ↥(fiber f a) := (fiber f a).orderIsoOfFin rfl
def site (f : Fin m → Fin n) (a) (i : Fin (len f a)) : Fin m := (ord f a i).val
theorem nameSite (f : Fin m → Fin n) (a) (i : Fin (len f a)) : f (site f a i)=a := (Finset.mem_filter.mp (ord f a i).property).2
def ix (f : Fin m → Fin n) (t : Fin m) := ((ord f (f t)).symm ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩).val
theorem ixLt (f : Fin m → Fin n) (t) : ix f t < len f (f t) := Fin.isLt _
theorem ixSite (f : Fin m → Fin n) (a) (i : Fin (len f a)) : ix f (site f a i)=i.val := by
  generalize eq:site f a i=t
  have nm : f t=a := eq ▸ nameSite f a i
  subst a
  have eq' : (ord f (f t)) i=⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩ := Subtype.ext eq
  unfold ix;rw [←eq',OrderIso.symm_apply_apply]
theorem siteIx {f : Fin m → Fin n} {a} (t) (eq : f t=a) :
    ∃i : Fin (len f a),site f a i=t ∧ i.val=ix f t := by
  subst a;let x : ↥(fiber f (f t)) := ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  exact ⟨(ord f (f t)).symm x,congrArg Subtype.val ((ord f (f t)).apply_symm_apply x),rfl⟩
theorem siteLt (f : Fin m → Fin n) (a) (i j : Fin (len f a)) : site f a i < site f a j ↔ i < j := (ord f a).lt_iff_lt
def near (f : Fin m → Fin n) (s t : Fin m) := s < t ∧ f s=f t ∧ ∀u,s < u → u < t → f u≠f t
theorem nearIff {f : Fin m → Fin n} {s t} : near f s t ↔ f s=f t ∧ ix f s+1=ix f t := by
  constructor
  · rintro ⟨st,eq,gap⟩
    obtain ⟨i,si,ri⟩:=siteIx s eq;obtain ⟨j,sj,rj⟩:=siteIx (f:=f) t rfl
    have lt : i < j := (siteLt f _ i j).mp (by simpa only [si,sj] using st)
    refine ⟨eq,?_⟩
    by_contra bad
    let k : Fin (len f (f t)) := ⟨i.val+1,by omega⟩
    have hik : i < k := by change i.val < i.val+1;omega
    have hkj : k < j := by change i.val+1 < j.val;omega
    have x:= (siteLt f _ i k).mpr hik;rw [si] at x
    have y:= (siteLt f _ k j).mpr hkj;rw [sj] at y
    exact gap _ x y (nameSite f _ _)
  · rintro ⟨eq,rank⟩
    obtain ⟨i,si,ri⟩:=siteIx s eq;obtain ⟨j,sj,rj⟩:=siteIx (f:=f) t rfl
    have lt : i < j := by change i.val < j.val;omega
    refine ⟨by simpa only [←si,←sj] using (siteLt f _ i j).mpr lt,eq,?_⟩
    intro u su ut nm;obtain ⟨k,sk,rk⟩:=siteIx u nm
    have x:=(siteLt f _ i k).mp (by simpa only [si,sk] using su)
    have y:=(siteLt f _ k j).mp (by simpa only [sk,sj] using ut)
    omega
def active (f : Fin m → Fin n) (s) := ∃t,near f s t
theorem actIff {f : Fin m → Fin n} {s} : active f s ↔ ix f s+1 < len f (f s) := by
  constructor
  · rintro ⟨t,st⟩;obtain ⟨eq,r⟩:=nearIff.mp st;rw [eq,r];exact ixLt f t
  · intro h;let i : Fin (len f (f s)) := ⟨ix f s+1,h⟩
    exact ⟨site f _ i,nearIff.mpr ⟨(nameSite f _ i).symm,(ixSite f _ i).symm⟩⟩
theorem uniqueIndex {f : Fin m → Fin n} {s t} (eq : f s=f t) (idx : ix f s=ix f t) : s=t := by
  obtain ⟨i,si,ri⟩:=siteIx s eq;obtain ⟨j,sj,rj⟩:=siteIx (f:=f) t rfl
  have h : i=j := Fin.ext (ri.trans (idx.trans rj.symm))
  exact si.symm.trans ((congrArg (site f _) h).trans sj)
theorem activeCount {f : Fin m → Fin n} (surj : Function.Surjective f) :
    (Finset.univ.filter (fun s => active f s)).card=m-n := by
  classical
  let last := Finset.univ.filter (fun s => ¬active f s)
  have term (s : ↥last) : ix f s.val+1=len f (f s.val) := by
    have no:=(actIff (f:=f) (s:=s.val)).not.mp (Finset.mem_filter.mp s.property).2;have:=ixLt f s.val;omega
  let g (s : ↥last) := f s.val
  have inj : Function.Injective g := by
    intro s t eq;apply Subtype.ext;apply uniqueIndex eq
    have a:=term s;have b:=term t;change f s.val=f t.val at eq;rw [eq] at a;omega
  have onto : Function.Surjective g := by
    intro a;obtain ⟨s,eq⟩:=surj a
    have pos:=ixLt f s;rw [eq] at pos
    let i : Fin (len f a) := ⟨len f a-1,by omega⟩
    have nm:=nameSite f a i
    have no : ¬active f (site f a i) := by rw [actIff,ixSite,nm];change ¬len f a-1+1 < len f a;omega
    exact ⟨⟨_,Finset.mem_filter.mpr ⟨Finset.mem_univ _,no⟩⟩,nm⟩
  have card : last.card=n := by simpa using Fintype.card_congr (Equiv.ofBijective g ⟨inj,onto⟩)
  have eq:=Finset.card_filter_add_card_filter_not (s:=Finset.univ) (active f)
  change _+last.card=(Finset.univ : Finset (Fin m)).card at eq;rw [Finset.card_univ,Fintype.card_fin,card] at eq
  exact Nat.eq_sub_of_add_eq eq
end PEqualNP.Outside.L_lib_1576_aux

namespace PEqualNP.Outside.L_lib_1576_aux
open scoped Classical
def prev (f : Fin m → Fin n) (t) := ∃s,near f s t
noncomputable def flow {α : Type} [Fintype α] (R : α → α → Prop) (w : α → Nat) (t : α) :=
  (Finset.univ.filter (fun s => R s t)).sum w
theorem flowSingle {α : Type} [Fintype α] {R : α → α → Prop} {s t} (h : R s t)
    (one : ∀z,R z t → z=s) (w : α → Nat) : flow R w t=w s := by
  classical
  have eq : Finset.univ.filter (fun i => R i t)={s} := by ext i;simp;exact ⟨one _,fun e => e ▸ h⟩
  unfold flow
  have same : Finset.univ.filter (fun i => R i t)={s} := eq
  rw [same,Finset.sum_singleton]
theorem succUnique {f : Fin m → Fin n} {s a b} (h : near f s a) (g : near f s b) : a=b := by
  obtain ⟨eq,idx⟩:=nearIff.mp h;obtain ⟨eq',idx'⟩:=nearIff.mp g
  exact uniqueIndex (eq.symm.trans eq') (idx.symm.trans idx')
theorem predUnique {f : Fin m → Fin n} {s t a} (h : near f s a) (g : near f t a) : s=t := by
  obtain ⟨eq,idx⟩:=nearIff.mp h;obtain ⟨eq',idx'⟩:=nearIff.mp g
  exact uniqueIndex (eq.trans eq'.symm) (by omega)
theorem sumFlow {α : Type} [Fintype α] (R : α → α → Prop) (uniq : ∀s a b,R s a → R s b → a=b)
    (w : α → Nat) : (∑t,flow R w t) = ∑s,if ∃t,R s t then w s else 0 := by
  classical
  unfold flow;simp only [Finset.sum_filter];rw [Finset.sum_comm];apply Finset.sum_congr rfl;intro s _
  by_cases h:∃t,R s t
  · obtain ⟨t,ht⟩:=h
    have iff (u) : R s u ↔ t=u := ⟨fun g => uniq _ _ _ ht g,fun e => e ▸ ht⟩
    simp [iff]
  · push_neg at h;simp [h]
noncomputable def inc (f : Fin m → Fin n) := flow (near f)
noncomputable def out (f : Fin m → Fin n) := flow (fun s t => near f t s)
theorem sumInc (f : Fin m → Fin n) (w : Fin m → Nat) :
    (∑t,inc f w t) = ∑s,if active f s then w s else 0 :=
  by
    rw [inc,sumFlow (near f) (fun _ _ _ => succUnique)]
    apply Finset.sum_congr rfl;intro t _;by_cases h:active f t
    · simp [h,show ∃s,near f t s from h]
    · simp [h,show ¬∃s,near f t s from h]
theorem sumOut (f : Fin m → Fin n) (w : Fin m → Nat) :
    (∑t,out f w t) = ∑s,if prev f s then w s else 0 :=
  by
    rw [out,sumFlow (fun i j => near f j i) (fun _ _ _ => predUnique)]
    apply Finset.sum_congr rfl;intro t _;by_cases h:prev f t
    · simp [h,show ∃s,near f s t from h]
    · simp [h,show ¬∃s,near f s t from h]
theorem gapValue {f : Fin m → Fin n} {s t} (e : near f s t) (w : Fin m → Nat) :
    inc f w t=w s ∧ out f w s=w t :=
  ⟨flowSingle e (fun _ g => predUnique g e) w,flowSingle (R:=fun i j => near f j i) e (fun _ g => succUnique g e) w⟩
end PEqualNP.Outside.L_lib_1576_aux

namespace PEqualNP.Outside.L_lib_1576_aux
open scoped Classical
abbrev Tags (m n : Nat) := Fin 3 → Fin m → Fin n
abbrev Bank (m : Nat) := Fin 3 → Fin m → Profile
def weight (w : Bank m) (j : Fin 3) (s : Fin m) (i : Fin 3) := flip (w j s) i
def quota (tag : Tags m n) (w : Bank m) :=
  (∀j t,mass (w j t)=(if j=0 then (if active (tag 0) t then 4 else 0) else 2)) ∧
  (∀t,active (tag 0) t → 2≤weight w 0 t 0) ∧
  (∀j s t,j≠0 → near (tag j) s t → 1≤weight w j s 2+weight w j t 1) ∧
  ∀t,2≤weight w 0 t 1+weight w 1 t 0+weight w 2 t 0+inc (tag 0) (fun s => weight w 0 s 2) t
noncomputable def arrow (f : Fin m → Fin n) (u : Fin m → Nat) (t : Fin m) := if active f t then u t else 0
noncomputable def back (f : Fin m → Fin n) (u : Fin m → Nat) (t : Fin m) := if prev f t then u t else 0
noncomputable def gap (tag : Tags m n) (w : Bank m) (j : Fin 3) (s : Fin m) :=
  arrow (tag j) (fun t => weight w j t 2) s+out (tag j) (fun t => weight w j t 1) s
noncomputable def bin (tag : Tags m n) (w : Bank m) (t : Fin m) :=
  weight w 0 t 1+weight w 1 t 0+weight w 2 t 0+inc (tag 0) (fun s => weight w 0 s 2) t
noncomputable def heavy (tag : Tags m n) (w : Bank m) (s : Fin m) :=
  weight w 0 s 1+arrow (tag 0) (fun t => weight w 0 t 2) s
noncomputable def lite (tag : Tags m n) (w : Bank m) (j : Fin 3) (s : Fin m) :=
  weight w j s 0+back (tag j) (fun t => weight w j t 1) s+arrow (tag j) (fun t => weight w j t 2) s
theorem bookkeeping (tag : Tags m n) (w : Bank m) :
    (∑t,bin tag w t)+(∑t,gap tag w 1 t)+(∑t,gap tag w 2 t)=
      (∑t,heavy tag w t)+(∑t,lite tag w 1 t)+(∑t,lite tag w 2 t) := by
  simp only [bin,gap,heavy,lite,Finset.sum_add_distrib,sumInc,sumOut,arrow,back];abel
theorem massZero {u : Profile} (zero : mass u=0) : u=fun _ => 0 := by
  funext x;apply Fin.ext;have bound:=Finset.single_le_sum (s:=Finset.univ) (f:=fun a => (u a).val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
  change (u x).val ≤ mass u at bound;omega
theorem arrowLe (f : Fin m → Fin n) (u : Fin m → Nat) (t) : arrow f u t≤u t := by unfold arrow;split <;> omega
theorem backLe (f : Fin m → Fin n) (u : Fin m → Nat) (t) : back f u t≤u t := by unfold back;split <;> omega
noncomputable def one (f : Fin m → Fin n) (s : Fin m) := (decide (active f s)).toNat
theorem oneSum (f : Fin m → Fin n) (surj : Function.Surjective f) : (∑s,one f s)=m-n := by
  have eq s : one f s=if active f s then 1 else 0 := by by_cases h:active f s <;> simp [one,h]
  simp [eq,activeCount surj]
theorem saturated {tag : Tags m n} {w : Bank m} (surj : ∀j,Function.Surjective (tag j)) (h : quota tag w) :
    (∀s,bin tag w s=2) ∧ (∀j s,j≠0 → gap tag w j s=one (tag j) s) ∧
    (∀s,heavy tag w s=2*one (tag 0) s) ∧ ∀j s,j≠0 → lite tag w j s=1 := by
  classical
  have gb (j : Fin 3) (s) (hj : j≠0) : one (tag j) s≤gap tag w j s := by
    by_cases ha:active (tag j) s
    · obtain ⟨t,ht⟩:=ha
      have ok:=h.2.2.1 j s t hj ht
      have outEq:=(gapValue ht (fun a => weight w j a 1)).2
      simpa [one,gap,arrow,show active (tag j) s from ⟨t,ht⟩,outEq] using ok
    · simp [one,ha]
  have hh (s) : heavy tag w s≤2*one (tag 0) s := by
    by_cases ha:active (tag 0) s
    · have m4 : mass (w 0 s)=4 := by simpa [ha] using h.1 0 s
      have up:=heavyBudget _ m4 (h.2.1 s ha)
      simpa [one,heavy,arrow,weight,ha] using up
    · have m0 : mass (w 0 s)=0 := by simpa [ha] using h.1 0 s
      simp [one,heavy,arrow,weight,ha,massZero m0,flip,ov]
  have ll (j : Fin 3) (s) (hj : j≠0) : lite tag w j s≤1 := by
    have mass2 : mass (w j s)=2 := by simpa [hj] using h.1 j s
    have up:=lightBudget _ mass2
    change weight w j s 0+weight w j s 1+weight w j s 2≤1 at up
    have a:=arrowLe (tag j) (fun t => weight w j t 2) s;have b:=backLe (tag j) (fun t => weight w j t 1) s
    unfold lite;omega
  have sB:=Finset.sum_le_sum (s:=Finset.univ) (fun s _ => h.2.2.2 s)
  change (∑_ : Fin m,2)≤∑ s,bin tag w s at sB
  have sG (j) (hj:j≠0):=Finset.sum_le_sum (s:=Finset.univ) (fun s _ => gb j s hj)
  have sH:=Finset.sum_le_sum (s:=Finset.univ) (fun s _ => hh s)
  have sL (j) (hj:j≠0):=Finset.sum_le_sum (s:=Finset.univ) (fun s _ => ll j s hj)
  have b1:=sG 1 (by decide);have b2:=sG 2 (by decide);have a1:=sL 1 (by decide);have a2:=sL 2 (by decide)
  have h0:=oneSum _ (surj 0);have h1:=oneSum _ (surj 1);have h2:=oneSum _ (surj 2)
  rw [←Finset.mul_sum,h0] at sH;rw [h1] at b1;rw [h2] at b2;simp at sB a1 a2
  have acct:=bookkeeping tag w
  have localEq {f g : Fin m → Nat} (le : ∀i,f i≤g i) (sum : ∑i,f i=∑i,g i) (i) : f i=g i :=
    (Finset.sum_eq_sum_iff_of_le (s:=Finset.univ) (fun i _ => le i)).mp sum i (Finset.mem_univ i)
  refine ⟨fun s => (localEq (f:=fun _ => 2) (g:=bin tag w) h.2.2.2 (by simp;omega) s).symm,?_,?_,?_⟩
  · intro j s hj
    have eq : j=1 ∨ j=2 := by omega
    rcases eq with rfl|rfl <;> exact (localEq (fun s => gb _ s hj) (by first | rw [h1];omega | rw [h2];omega) s).symm
  · exact fun s => localEq hh (by rw [←Finset.mul_sum,h0];omega) s
  · intro j s hj;have eq : j=1 ∨ j=2 := by omega
    rcases eq with rfl|rfl <;> exact localEq (fun s => ll _ s hj) (by simp;omega) s
end PEqualNP.Outside.L_lib_1576_aux

namespace PEqualNP.Outside.L_lib_1576_aux
open scoped Classical
def same (f : Fin m → Fin n) (S : Finset (Fin m)) (a) := S.filter (fun t => f t=a)
def tailSet (f : Fin m → Fin n) (S : Finset (Fin m)) (t) := S.filter (fun z => f z=f t ∧ t<z)
def afterN (f : Fin m → Fin n) (S : Finset (Fin m)) (t) := (tailSet f S t).card
def tick (S : Finset (Fin m)) (t) := (decide (t∈S)).toNat
def oneEach (f : Fin m → Fin n) (S : Finset (Fin m)) := ∀a,(same f S a).card=1
def consistent (f : Fin m → Fin n) (S : Finset (Fin m)) (a : Fin m → Nat) :=
  (∀s,¬active f s → a s=0) ∧ (∀t,¬prev f t → tick S t+a t=1) ∧ ∀s t,near f s t → tick S t+a t=a s
theorem lastAfter {f : Fin m → Fin n} {t} (no : ¬active f t) (S : Finset (Fin m)) : afterN f S t=0 := by
  have stop := (actIff (f:=f) (s:=t)).not.mp no
  unfold afterN;apply Finset.card_eq_zero.mpr;apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z inside;have ⟨nm,lt⟩:=(Finset.mem_filter.mp inside).2
  obtain ⟨i,hi,ri⟩:=siteIx t (f:=f) rfl;obtain ⟨j,hj,rj⟩:=siteIx z nm
  have h:= (siteLt f _ i j).mp (by simpa only [hi,hj] using lt);omega
theorem noBefore {f : Fin m → Fin n} {t} (no : ¬prev f t) {z} (nm : f z=f t) : t≤z := by
  obtain ⟨i,hi,ri⟩:=siteIx t (f:=f) rfl;obtain ⟨j,hj,rj⟩:=siteIx z nm
  by_contra! lt;have ji:= (siteLt f _ j i).mp (by simpa only [hi,hj] using lt)
  let k : Fin (len f (f t)) := ⟨i.val-1,by omega⟩
  apply no ⟨site f _ k,nearIff.mpr ⟨nameSite f _ k,?_⟩⟩
  rw [ixSite];change i.val-1+1=ix f t;omega
theorem tailSplit {f : Fin m → Fin n} {t u} (h : near f t u) (S : Finset (Fin m)) :
    tick S u+afterN f S u=afterN f S t := by
  have ord {z} (nm : f z=f t) (lt : t<z) : u≤z := by
    by_contra! bad;exact h.2.2 z lt bad (nm.trans h.2.1)
  have excl : u∉tailSet f S u := by simp [tailSet]
  by_cases hu:u∈S
  · have eq : tailSet f S t=insert u (tailSet f S u) := by
      ext z;simp only [tailSet,Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨memb,nm,lt⟩;rcases (ord nm lt).eq_or_lt with eq|lt'
        · exact Or.inl eq.symm
        · exact Or.inr ⟨memb,nm.trans h.2.1,lt'⟩
      · rintro (rfl|⟨mem,nm,lt⟩)
        · exact ⟨hu,h.2.1.symm,h.1⟩
        · exact ⟨mem,nm.trans h.2.1.symm,h.1.trans lt⟩
    simp [tick,hu,afterN,eq,Finset.card_insert_of_notMem excl,Nat.add_comm]
  · have eq : tailSet f S t=tailSet f S u := by
      ext z;simp only [tailSet,Finset.mem_filter]
      constructor
      · rintro ⟨mem,nm,lt⟩;exact ⟨mem,nm.trans h.2.1,lt_of_le_of_ne (ord nm lt) (fun e => hu (e ▸ mem))⟩
      · rintro ⟨mem,nm,lt⟩;exact ⟨mem,nm.trans h.2.1.symm,h.1.trans lt⟩
    simp [tick,hu,afterN,eq]
theorem headSplit {f : Fin m → Fin n} {t} (no : ¬prev f t) (S : Finset (Fin m)) :
    tick S t+afterN f S t=(same f S (f t)).card := by
  have excl : t∉tailSet f S t := by simp [tailSet]
  by_cases ht:t∈S
  · have eq : same f S (f t)=insert t (tailSet f S t) := by
      ext z;simp only [same,tailSet,Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨hz,nm⟩;rcases (noBefore no nm).eq_or_lt with e|lt
        · exact Or.inl e.symm
        · exact Or.inr ⟨hz,nm,lt⟩
      · rintro (rfl|⟨mem,nm,_⟩)
        · exact ⟨ht,rfl⟩
        · exact ⟨mem,nm⟩
    simp [tick,ht,afterN,eq,Finset.card_insert_of_notMem excl,Nat.add_comm]
  · have eq : same f S (f t)=tailSet f S t := by
      ext z;simp only [same,tailSet,Finset.mem_filter]
      exact ⟨fun ⟨mem,nm⟩ => ⟨mem,nm,lt_of_le_of_ne (noBefore no nm) (fun e => ht (e ▸ mem))⟩,fun ⟨mem,nm,_⟩ => ⟨mem,nm⟩⟩
    simp [tick,ht,afterN,eq]
theorem canonical {f : Fin m → Fin n} {S : Finset (Fin m)} (one : oneEach f S) : consistent f S (afterN f S) :=
  ⟨fun _ h => lastAfter h S,fun t h => (headSplit h S).trans (one _),fun _ _ h => tailSplit h S⟩
theorem recoverAt {f : Fin m → Fin n} {S : Finset (Fin m)} {a} (c : consistent f S a) (t : Fin m) :
    a t=afterN f S t := by
  by_cases h : active f t
  · obtain ⟨u,next⟩:=h
    have e:=recoverAt c u;have p:=c.2.2 t u next;have q:=tailSplit next S;omega
  · exact (c.1 _ h).trans (lastAfter h S).symm
termination_by m-t.val
decreasing_by have := next.1;omega
theorem recover {f : Fin m → Fin n} {S : Finset (Fin m)} (surj : Function.Surjective f) {a} (c : consistent f S a) :
    a=afterN f S ∧ oneEach f S := by
  have eq := recoverAt c
  refine ⟨funext eq,?_⟩
  intro v;obtain ⟨t,nm⟩:=surj v
  have pos:=ixLt f t;rw [nm] at pos
  let i : Fin (len f v) := ⟨0,by omega⟩
  let s := site f v i
  have name : f s=v := nameSite _ _ _
  have zero : ix f s=0 := ixSite _ _ _
  have no : ¬prev f s := by rintro ⟨z,h⟩;have q:=(nearIff.mp h).2;omega
  have hh:=c.2.1 s no;rw [eq] at hh;rw [←name,←headSplit no];exact hh
end PEqualNP.Outside.L_lib_1576_aux

namespace PEqualNP.Outside.L_lib_1576_aux
open scoped Classical
def rootSet (w : Bank m) := Finset.univ.filter (fun t => weight w 1 t 0=1)
def hstep (w : Bank m) (s : Fin m) := (decide (weight w 0 s 1=2)).toNat
def lstep (w : Bank m) (j : Fin 3) (t : Fin m) := weight w j t 2
theorem zeroFlip (j : Fin 3) : flip (fun _ => 0) j=0 := by simp [flip,ov]
theorem hprofile {tag : Tags m n} {w : Bank m} (surj : ∀j,Function.Surjective (tag j)) (h : quota tag w)
    (s : Fin m) (act : active (tag 0) s) : ∃d b,w 0 s=square d b := by
  have mass4 : mass (w 0 s)=4 := by simpa [act] using h.1 0 s
  have exact2:=(saturated surj h).2.2.1 s
  simp [heavy,arrow,one,act] at exact2
  by_cases hi : 0<weight w 0 s 1
  · obtain ⟨b,eq⟩:=getSquare _ false mass4 (h.2.1 s act) hi;exact ⟨false,b,eq⟩
  · have next : 0<weight w 0 s 2 := by omega
    obtain ⟨b,eq⟩:=getSquare _ true mass4 (h.2.1 s act) next;exact ⟨true,b,eq⟩
theorem hzero {tag : Tags m n} {w : Bank m} (h : quota tag w) (s) (no : ¬active (tag 0) s) :
    w 0 s=fun _ => 0 := massZero (by simpa [no] using h.1 0 s)
theorem hvalue {tag : Tags m n} {w : Bank m} (surj : ∀j,Function.Surjective (tag j)) (h : quota tag w) (s) :
    weight w 0 s 1=2*hstep w s ∧ (active (tag 0) s → weight w 0 s 2+2*hstep w s=2) ∧
      (¬active (tag 0) s → hstep w s=0) := by
  by_cases act:active (tag 0) s
  · obtain ⟨d,b,eq⟩:=hprofile surj h s act
    have facts:=squareFacts d b
    cases d <;> simp [weight,hstep,eq,dir] at facts ⊢ <;> simp_all [act]
  · have eq:=hzero h s act;simp [weight,hstep,eq,zeroFlip,act]
theorem lvalue {tag : Tags m n} {w : Bank m} (surj : ∀j,Function.Surjective (tag j)) (h : quota tag w)
    (j) (hj : j≠0) (s) : weight w j s 0+weight w j s 1+weight w j s 2=1 ∧
    (¬active (tag j) s → weight w j s 2=0) ∧ (¬prev (tag j) s → weight w j s 1=0) := by
  have up:=lightBudget (w j s) (by simpa [hj] using h.1 j s)
  change weight w j s 0+weight w j s 1+weight w j s 2≤1 at up
  have sat:=(saturated surj h).2.2.2 j s hj
  have a:=arrowLe (tag j) (fun t => weight w j t 2) s
  have b:=backLe (tag j) (fun t => weight w j t 1) s
  unfold lite at sat
  refine ⟨by omega,?_,?_⟩
  · intro no;simp [arrow,no] at sat;omega
  · intro no;simp [back,no] at sat;omega
theorem noInc {f : Fin m → Fin n} {s} (no : ¬prev f s) (w : Fin m → Nat) : inc f w s=0 := by
  have a : ∀t,¬near f t s := fun t h => no ⟨t,h⟩
  simp [inc,flow,a]
theorem readBin {tag : Tags m n} {w : Bank m} (surj : ∀j,Function.Surjective (tag j)) (h : quota tag w) (t) :
    tick (rootSet w) t=weight w 1 t 0 ∧ weight w 2 t 0=weight w 1 t 0 ∧
    (¬prev (tag 0) t → tick (rootSet w) t+hstep w t=1) ∧
    ∀s,near (tag 0) s t → tick (rootSet w) t+hstep w t=hstep w s := by
  let a:=weight w 1 t 0
  let b:=weight w 2 t 0
  have A : a≤1 := by have hh:=(lvalue surj h 1 (by decide) t).1;dsimp [a];omega
  have B : b≤1 := by have hh:=(lvalue surj h 2 (by decide) t).1;dsimp [b];omega
  have first:=(hvalue surj h t).1
  have total:=(saturated surj h).1 t
  change weight w 0 t 1 + a + b + inc (tag 0) (fun s => weight w 0 s 2) t=2 at total
  have mem : t∈rootSet w ↔ a=1 := by simp [rootSet,a]
  have tickEq : tick (rootSet w) t=a := by
    unfold tick
    by_cases ha:a=1
    · simp [mem.mpr ha,ha]
    · have no:=mem.not.mpr ha;have zero : a=0 := by omega
      simp [no,zero]
  refine ⟨tickEq,?_,?_,?_⟩
  · by_cases p:prev (tag 0) t
    · obtain ⟨s,link⟩:=p
      have hin:=(gapValue link (fun s => weight w 0 s 2)).1
      have out:=(hvalue surj h s).2.1 ⟨t,link⟩;rw [hin] at total;change b=a;omega
    · rw [noInc p] at total;change b=a;omega
  · intro no;rw [noInc no] at total;rw [tickEq];omega
  · intro s link
    rw [(gapValue link (fun s => weight w 0 s 2)).1] at total
    have out:=(hvalue surj h s).2.1 ⟨t,link⟩;rw [tickEq];omega
theorem hpath {tag : Tags m n} {w : Bank m} (surj : ∀j,Function.Surjective (tag j)) (h : quota tag w) :
    consistent (tag 0) (rootSet w) (hstep w) := by
  exact ⟨fun s => (hvalue surj h s).2.2,fun s => (readBin surj h s).2.2.1,fun s t => (readBin surj h t).2.2.2 s⟩
theorem lpath {tag : Tags m n} {w : Bank m} (surj : ∀j,Function.Surjective (tag j)) (h : quota tag w)
    (j) (hj : j≠0) : consistent (tag j) (rootSet w) (lstep w j) := by
  have tk s : tick (rootSet w) s=weight w j s 0 := by
    have d:=readBin surj h s;have eq : j=1 ∨ j=2 := by omega
    rcases eq with rfl|rfl
    · exact d.1
    · exact d.1.trans d.2.1.symm
  refine ⟨fun s => (lvalue surj h j hj s).2.1,?_,?_⟩
  · intro t no;have b:=(lvalue surj h j hj t);rw [tk];unfold lstep;have :=b.2.2 no;omega
  · intro s t link
    have eq:=(saturated surj h).2.1 j s hj
    have yes : active (tag j) s:=⟨t,link⟩
    simp [gap,arrow,one,yes,(gapValue link (fun t => weight w j t 1)).2] at eq
    have total:=(lvalue surj h j hj t).1;rw [tk];unfold lstep;omega
end PEqualNP.Outside.L_lib_1576_aux

namespace PEqualNP.Outside.L_lib_1576_aux
open scoped Classical
def cover (tag : Tags m n) (S : Finset (Fin m)) := ∀j,oneEach (tag j) S
def hdir (f : Fin m → Fin n) (S : Finset (Fin m)) (t) := decide (afterN f S t=0)
def ldir (f : Fin m → Fin n) (S : Finset (Fin m)) (t : Fin m) : Fin 3 :=
  if t∈S then 0 else if afterN f S t=1 then 2 else 1
def shape (tag : Tags m n) (S : Finset (Fin m)) (j : Fin 3) (t : Fin m) (p : Profile) :=
  if j=0 then if active (tag 0) t then ∃b,p=square (hdir (tag 0) S t) b else p=fun _ => 0
  else ∃A,ldir (tag j) S t∉A ∧ p=light (ldir (tag j) S t) A
theorem rootCover {tag : Tags m n} {w : Bank m} (surj : ∀j,Function.Surjective (tag j)) (h : quota tag w) :
    cover tag (rootSet w) := by
  intro j;by_cases zero:j=0
  · subst j;exact (recover (surj _) (hpath surj h)).2
  · exact (recover (surj _) (lpath surj h j zero)).2
theorem getShapes {tag : Tags m n} {w : Bank m} (surj : ∀j,Function.Surjective (tag j)) (h : quota tag w) :
    ∀j t,shape tag (rootSet w) j t (w j t) := by
  intro j t
  by_cases zero:j=0
  · subst j
    by_cases yes:active (tag 0) t
    · obtain ⟨s,b,eq⟩:=hprofile surj h t yes
      have path:=recoverAt (hpath surj h) t
      have d : hdir (tag 0) (rootSet w) t=s := by
        have fs:=squareFacts s b
        unfold hdir;rw [←path];cases s <;> simp_all [hstep,weight,dir]
      simpa [shape,yes,d] using (show ∃a,w 0 t=square s a from ⟨b,eq⟩)
    · simpa [shape,yes] using hzero h t yes
  · have mass2 : mass (w j t)=2 := by simpa [zero] using h.1 j t
    have sum:=(lvalue surj h j zero t).1
    have hj : j=1 ∨ j=2 := by omega
    have bin0 : tick (rootSet w) t=weight w j t 0 := by
      rcases hj with rfl|rfl;exact (readBin surj h t).1;exact (readBin surj h t).1.trans (readBin surj h t).2.1.symm
    have tail:=recoverAt (lpath surj h j zero) t
    change weight w j t 2=afterN (tag j) (rootSet w) t at tail
    have pos : 0<weight w j t (ldir (tag j) (rootSet w) t) := by
      by_cases inside:t∈rootSet w
      · simp [tick,inside] at bin0;simp [ldir,inside];omega
      · simp [tick,inside] at bin0
        by_cases on:afterN (tag j) (rootSet w) t=1 <;> simp [ldir,inside,on] <;> omega
    simpa [shape,zero] using getLight _ _ mass2 pos
theorem headBound {f : Fin m → Fin n} {S : Finset (Fin m)} (h : oneEach f S) (t) :
    tick S t + afterN f S t ≤ 1 := by
  have sub : tailSet f S t⊆same f S (f t) := fun z hz => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2.1⟩
  by_cases mem:t∈S
  · have ins : insert t (tailSet f S t)⊆same f S (f t) := Finset.insert_subset (Finset.mem_filter.mpr ⟨mem,rfl⟩) sub
    have hh:=Finset.card_le_card ins
    have out : t∉tailSet f S t := by simp [tailSet]
    rw [Finset.card_insert_of_notMem out,h] at hh;simpa [tick,mem,afterN,Nat.add_comm] using hh
  · have hh:=Finset.card_le_card sub;rw [h] at hh;simpa [tick,mem,afterN] using hh
theorem lightRead {f : Fin m → Fin n} {S : Finset (Fin m)} (h : oneEach f S) (t) {A} (off : ldir f S t∉A) :
    let p:=light (ldir f S t) A
    mass p=2 ∧ flip p 0=tick S t ∧ flip p 2=afterN f S t ∧ flip p 0+flip p 1+flip p 2=1 := by
  intro p
  have hb:=headBound h t
  have facts:=lightFacts _ _ off
  change mass p=2 ∧ ∀i,flip p i=_ at facts
  refine ⟨facts.1,?_,?_,?_⟩
  · rw [facts.2];by_cases mem:t∈S <;> simp [ldir,tick,mem] <;> split <;> decide
  · rw [facts.2];by_cases mem:t∈S <;> simp [tick,mem] at hb <;> by_cases on:afterN f S t=1 <;> simp [ldir,mem,on] <;> omega
  · simp only [facts.2];generalize eq:ldir f S t=i;fin_cases i <;> decide
theorem heavyRead {f : Fin m → Fin n} {S : Finset (Fin m)} (h : oneEach f S) (t b) :
    let p:=square (hdir f S t) b
    mass p=4 ∧ flip p 0=2 ∧ flip p 1=2*afterN f S t ∧ flip p 2+2*afterN f S t=2 := by
  have hb:=headBound h t;have facts:=squareFacts (hdir f S t) b
  by_cases zero:afterN f S t=0
  · simp_all [hdir,zero,dir]
  · have one : afterN f S t=1 := by omega
    simpa [hdir,zero,one,dir] using facts
end PEqualNP.Outside.L_lib_1576_aux

namespace PEqualNP.Outside.L_lib_1576_aux
open scoped Classical
theorem assembleBank {tag : Tags m n} {w : Bank m} {S : Finset (Fin m)}
    (cv : cover tag S) (sh : ∀j t,shape tag S j t (w j t)) : quota tag w ∧ rootSet w=S := by
  have H (t) : (active (tag 0) t → mass (w 0 t)=4 ∧ weight w 0 t 0=2 ∧ weight w 0 t 2+2*afterN (tag 0) S t=2) ∧
      (¬active (tag 0) t → mass (w 0 t)=0) ∧ weight w 0 t 1=2*afterN (tag 0) S t := by
    by_cases act:active (tag 0) t
    · have localShape:=sh 0 t
      simp only [shape,ite_true,act] at localShape
      obtain ⟨b,eq⟩:=localShape;have facts:=heavyRead (cv 0) t b
      simp only [weight,eq,act,true_implies,not_true_eq_false,false_implies,and_true,true_and] at *
      exact ⟨⟨facts.1,facts.2.1,facts.2.2.2⟩,facts.2.2.1⟩
    · have eq : w 0 t=fun _ => 0 := by simpa [shape,act] using sh 0 t
      simp [weight,act,eq,zeroFlip,lastAfter act S,mass]
  have L (j) (hj:j≠0) (t) : mass (w j t)=2 ∧ weight w j t 0=tick S t ∧
      weight w j t 2=afterN (tag j) S t ∧ weight w j t 0+weight w j t 1+weight w j t 2=1 := by
    have localShape:=sh j t
    simp only [shape,hj,ite_false] at localShape
    obtain ⟨A,off,eq⟩:=localShape
    simpa only [weight,eq] using lightRead (cv j) t off
  constructor
  · refine ⟨?_,fun t a => ((H t).1 a).2.1.ge,?_,?_⟩
    · intro j t;by_cases z:j=0
      · subst j;by_cases act:active (tag 0) t
        · simpa [act] using ((H t).1 act).1
        · simpa [act] using (H t).2.1 act
      · simpa [z] using (L j z t).1
    · intro j s t hj link
      have a:=L j hj s;have b:=L j hj t;have c:=tailSplit link S;omega
    · intro t
      have b1:=L 1 (by decide) t;have b2:=L 2 (by decide) t;have h1:=(H t).2.2
      by_cases p:prev (tag 0) t
      · obtain ⟨s,link⟩:=p
        rw [(gapValue link (fun s => weight w 0 s 2)).1]
        have eq:=((H s).1 ⟨t,link⟩).2.2;have c:=tailSplit link S;omega
      · rw [noInc p];have c:=(canonical (cv 0)).2.1 t p;omega
  · ext t;have link:=(L 1 (by decide) t).2.1
    by_cases ht:t∈S <;> simp_all [rootSet,tick]
end PEqualNP.Outside.L_lib_1576_aux

namespace PEqualNP.Outside.L_lib_1576_aux
open scoped Classical
noncomputable def options (tag : Tags m n) (S : Finset (Fin m)) (j t) := Finset.univ.filter (shape tag S j t)
noncomputable def family (tag : Tags m n) (S : Finset (Fin m)) :=
  Finset.univ.filter (fun w : Bank m => ∀j t,shape tag S j t (w j t))
theorem hcount (tag : Tags m n) (S : Finset (Fin m)) (t) :
    (options tag S 0 t).card=if active (tag 0) t then 2 else 1 := by
  classical
  by_cases act:active (tag 0) t
  · let dir := hdir (tag 0) S t
    have im : options tag S 0 t=Finset.univ.image (square dir) := by ext p;simp [options,shape,act,dir,eq_comm,or_comm]
    rw [im,Finset.card_image_of_injective _ (squareUnique dir)];simp [act]
  · have eq : options tag S 0 t={fun _ => 0} := by ext p;simp [options,shape,act]
    rw [eq];simp [act]
theorem lcount (tag : Tags m n) (S : Finset (Fin m)) (j : Fin 3) (hj : j≠0) (t) :
    (options tag S j t).card=4 := by
  classical
  let i:=ldir (tag j) S t
  let B := Finset.univ.filter (fun A : W => i∉A)
  have im : options tag S j t=B.image (light i) := by ext p;simp [options,shape,hj,B,i,eq_comm]
  rw [im,Finset.card_image_of_injOn]
  · exact lightCount _
  · intro a ha b hb eq;exact lightUnique i a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 eq
noncomputable def separate (tag : Tags m n) (S : Finset (Fin m)) :
    ↥(family tag S) ≃ ((j : Fin 3) → (t : Fin m) → ↥(options tag S j t)) where
  toFun w j t := ⟨w.val j t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp w.property).2 j t⟩⟩
  invFun x := ⟨fun j t => (x j t).val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun j t => (Finset.mem_filter.mp (x j t).property).2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem familyCount (tag : Tags m n) (surj : ∀j,Function.Surjective (tag j)) (S : Finset (Fin m)) :
    (family tag S).card=2^(m-n)*4^(2*m) := by
  classical
  have eq:=Fintype.card_congr (separate tag S)
  simp only [Fintype.card_coe,Fintype.card_pi,Finset.prod_attach] at eq
  have heavyCount : (∏t,(options tag S 0 t).card)=2^(m-n) := by
    simp only [hcount,Finset.prod_ite,Finset.prod_const,one_pow,mul_one]
    congr 1;exact activeCount (surj 0)
  have lightCount' (j) (hj:j≠0) : (∏t,(options tag S j t).card)=4^m := by simp [lcount tag S j hj]
  rw [Fin.prod_univ_three,heavyCount,lightCount' 1 (by decide),lightCount' 2 (by decide)] at eq
  rw [show 2*m=m+m by omega,pow_add];simpa only [Nat.mul_assoc] using eq
noncomputable def solutions (tag : Tags m n) := Finset.univ.filter (cover tag)
noncomputable def banks (tag : Tags m n) := Finset.univ.filter (quota tag)
theorem census (tag : Tags m n) (surj : ∀j,Function.Surjective (tag j)) :
    (banks tag).card=2^(m-n)*4^(2*m)*(solutions tag).card := by
  classical
  have union : banks tag=(solutions tag).biUnion (family tag) := by
    ext w;simp only [banks,solutions,family,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_biUnion]
    exact ⟨fun q => ⟨rootSet w,rootCover surj q,getShapes surj q⟩,fun ⟨S,cv,sh⟩ => (assembleBank cv sh).1⟩
  have dis : (solutions tag : Set (Finset (Fin m))).PairwiseDisjoint (family tag) := by
    intro A hA B hB ne;apply Finset.disjoint_left.mpr;intro w h w'
    have id (S) (inS:S∈solutions tag) (inW:w∈family tag S) : rootSet w=S :=
      (assembleBank (Finset.mem_filter.mp inS).2 (Finset.mem_filter.mp inW).2).2
    exact ne ((id A hA h).symm.trans (id B hB w'))
  rw [union,Finset.card_biUnion dis];simp [familyCount tag surj,Nat.mul_comm]
end PEqualNP.Outside.L_lib_1576_aux

namespace PEqualNP.Outside.L_lib_1576_aux
noncomputable def fixedFilter {α : Type*} (P : α → Prop) (A : Finset α) := @Finset.filter α P (fun _ => Classical.propDecidable _) A
theorem filterUnique {α : Type*} (P : α → Prop) (d : DecidablePred P) (A : Finset α) :
    @Finset.filter α P d A=fixedFilter P A := by ext;simp only [fixedFilter,Finset.mem_filter]
noncomputable def sameDecision (P : Prop) := @decide P (Classical.propDecidable P)
theorem decUnique (P : Prop) (d : Decidable P) : @decide P d=sameDecision P := by unfold sameDecision;congr 1
noncomputable def fixedInsert {α : Type} (a : α) (A : Finset α) := letI := Classical.decEq α;insert a A
theorem insertUnique {α : Type} (d : DecidableEq α) (a : α) (A : Finset α) :
    (letI := d;insert a A)=fixedInsert a A := by ext;simp only [fixedInsert,Finset.mem_insert]
noncomputable def sameIf {α : Type} (P : Prop) (a b : α) := @ite α P (Classical.propDecidable P) a b
theorem ifUnique {α : Type} (P : Prop) (d : Decidable P) (a b : α) : @ite α P d a b=sameIf P a b := by unfold sameIf;by_cases h:P <;> simp [h]
theorem insertSame {α : Type} (d e : DecidableEq α) (a : α) (S : Finset α) :
    (letI := d;insert a S)=(letI := e;insert a S) := by ext;simp only [Finset.mem_insert]
noncomputable def fixedUniv (α : Type) [Finite α] := @Finset.univ α (Fintype.ofFinite α)
theorem univUnique {α : Type} [Finite α] (d : Fintype α) : @Finset.univ α d=fixedUniv α := by ext;simp only [fixedUniv,Finset.mem_univ]
end PEqualNP.Outside.L_lib_1576_aux
open PEqualNP.Outside.L_lib_1576_aux in
theorem PEqualNP.Outside.L_lib_1576 : ∀ (m n : Nat) (tag : Fin 3 → Fin m → Fin n), (∀ j, Function.Surjective (tag j)) →
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  let W := Finset (Fin 3)
  let near := fun (j : Fin 3) (s t : Fin m) =>
    s < t ∧ tag j s = tag j t ∧ ∀ u, s < u → u < t → tag j u ≠ tag j t
  let active := fun s => ∃ t, near 0 s t
  let Bank := Fin 3 → Fin m → W → Fin 5
  let flips := fun (u : W → Fin 5) (j : Fin 3) =>
    ∑ A ∈ (Finset.univ.filter (fun A : W => j ∉ A)), min (u A).val (u (insert j A)).val
  let banks := Finset.univ.filter (fun w : Bank =>
    (∀ j t, (∑ A, (w j t A).val) = (if j = 0 then (if active t then 4 else 0) else 2)) ∧
    (∀ t, active t → 2 ≤ flips (w 0 t) 0) ∧
    (∀ j s t, j ≠ 0 → near j s t → 1 ≤ flips (w j s) 2 + flips (w j t) 1) ∧
    ∀ t, 2 ≤ flips (w 0 t) 1 + flips (w 1 t) 0 + flips (w 2 t) 0 +
      ∑ s ∈ (Finset.univ.filter (fun s : Fin m => near 0 s t)), flips (w 0 s) 2)
  let covers := Finset.univ.filter (fun S : Finset (Fin m) =>
    ∀ j v, (S.filter (fun t => tag j t = v)).card = 1)
  banks.card = 2^(m-n) * 4^(2*m) * covers.card := by
  classical
  intro m n tag surj W' near' active' Bank' flips' banks' covers'
  have nEq j s t : near' j s t ↔ near (tag j) s t := Iff.rfl
  have aEq t : active' t ↔ active (tag 0) t := Iff.rfl
  have fEq (p : Profile) j : flips' p j=flip p j := by
    simp only [flips',PEqualNP.Outside.L_lib_1576_aux.flip,ov,filterUnique]
    refine Finset.sum_congr ?_ ?_
    · apply congrArg (fixedFilter _);ext;simp
    · intro x _;apply congrArg (min (p x).val);apply congrArg (fun A => (p A).val);exact insertSame _ _ _ _
  have bEq : banks'=banks tag := by
    ext w;simp only [banks',banks,Finset.mem_filter,Finset.mem_univ,true_and];simp only [quota,weight,mass,fEq,nEq,aEq,inc,flow,filterUnique,ifUnique,univUnique];rfl
  have cEq : covers'=solutions tag := by
    ext S;simp only [covers',solutions,Finset.mem_filter,Finset.mem_univ,true_and];simp only [cover,oneEach,same,filterUnique]
  rw [bEq,cEq];exact census tag surj
