import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1546_aux
abbrev Mask (k : Nat) := Finset (Fin k)
def independent (u v w : Mask k) := u≠∅ ∧ v≠∅ ∧ u≠v ∧ w≠∅ ∧ w≠u ∧ w≠v ∧ w≠(u\v)∪(v\u)
def bit (x S : Mask k) := decide ((x∩S).card % 2=1)
def yes (u v w S : Mask k) := bit u S && bit v S && bit w S
def hits (e : Nat) (mask : Fin n → Mask k) := ∀u v w,independent u v w →
  e<(Finset.univ.filter (fun j => yes u v w (mask j)=true)).card
def frequent (e : Nat) (mask : Fin n → Mask k) := ∀S : Mask k,S.card=2 ∨ S.card=3 →
  e<(Finset.univ.filter (fun j => mask j=S)).card
theorem bitOne (x : Fin k) (S : Mask k) : bit {x} S=true ↔ x∈S := by
  by_cases h : x∈S <;> simp [bit,Finset.singleton_inter,h]
theorem symTwo {a b : Fin k} (h : a≠b) :
    (({a} : Mask k)\{b})∪(({b} : Mask k)\{a})={a,b} := by ext;simp;grind
theorem isolates (hk : 6≤k) (S : Mask k) (size : S.card=2 ∨ S.card=3) :
    ∃u v w,independent u v w ∧ ∀T : Mask k,T.card≤3 → yes u v w T=true → T=S := by
  rcases size with two|three
  · obtain ⟨a,b,ab,rfl⟩:=Finset.card_eq_two.mp two
    let W : Mask k := Finset.univ.erase a
    have wc : W.card=k-1 := by simp [W]
    have pc : ({a,b} : Mask k).card=2 := by simp [ab]
    have nz : W≠∅ := by intro h;rw [h] at wc;simp at wc;omega
    have diff (x : Fin k) : W≠{x} := by intro h;rw [h,Finset.card_singleton] at wc;omega
    have np : W≠{a,b} := by intro h;rw [h,pc] at wc;omega
    refine ⟨{a},{b},W,⟨by simp,by simp,by simpa using ab,nz,diff _,diff _,by rwa [symTwo ab]⟩,?_⟩
    intro T cap h;simp only [yes,Bool.and_eq_true,bitOne] at h
    obtain ⟨⟨ha,hb⟩,odd⟩:=h
    have inter : W∩T=T.erase a := by ext x;simp [W]
    have parity := of_decide_eq_true odd
    change (W∩T).card % 2=1 at parity
    rw [inter,Finset.card_erase_of_mem ha] at parity
    have sub : ({a,b} : Mask k)⊆T := Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb)
    have lo:=Finset.card_le_card sub
    exact (Finset.eq_of_subset_of_card_le sub (by omega)).symm
  · obtain ⟨a,b,c,ab,ac,bc,rfl⟩:=Finset.card_eq_three.mp three
    have np : ({c} : Mask k)≠{a,b} := by intro h;have hh:=congrArg Finset.card h;simp [ab] at hh
    refine ⟨{a},{b},{c},⟨by simp,by simp,by simpa using ab,by simp,by simpa using ac.symm,by simpa using bc.symm,by rwa [symTwo ab]⟩,?_⟩
    intro T cap h;simp only [yes,Bool.and_eq_true,bitOne] at h
    have sub : ({a,b,c} : Mask k)⊆T := Finset.insert_subset h.1.1 (Finset.insert_subset h.1.2 (Finset.singleton_subset_iff.mpr h.2))
    exact (Finset.eq_of_subset_of_card_le sub (by omega)).symm
theorem necessary {e} {mask : Fin n → Mask k} (hk : 6≤k) (small : ∀j,(mask j).card≤3) (ok : hits e mask) : frequent e mask := by
  intro S size;obtain ⟨u,v,w,hi,force⟩:=isolates hk S size
  apply (ok u v w hi).trans_le;apply Finset.card_le_card;intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,force _ (small j) (Finset.mem_filter.mp hj).2⟩
end PEqualNP.Outside.L_lib_1546_aux

namespace PEqualNP.Outside.L_lib_1546_aux
abbrev Color := Bool × Bool × Bool
def z : Color := (false,false,false)
def allOn : Color := (true,true,true)
def add (a b : Color) : Color := (xor a.1 b.1,xor a.2.1 b.2.1,xor a.2.2 b.2.2)
def dot (a b : Color) := xor (xor (a.1 && b.1) (a.2.1 && b.2.1)) (a.2.2 && b.2.2)
def col (u v w : Mask k) (i : Fin k) : Color := (decide (i∈u),decide (i∈v),decide (i∈w))
def spans (p : Color → Bool) := ∀ a,a≠z → ∃b,p b=true ∧ dot a b=true
instance (p : Color → Bool) : Decidable (spans p) := by unfold spans;infer_instance
theorem observed {u v w : Mask k} (ind : independent u v w) :
    spans (fun c => decide (∃i,col u v w i=c)) := by
  intro a az
  by_contra! h
  have h0 (i : Fin k) : dot a (col u v w i)=false := by simpa only [Bool.not_eq_true] using h _ (decide_eq_true ⟨i,rfl⟩)
  obtain ⟨u0,v0,uv,w0,wu,wv,ws⟩:=ind
  rcases a with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c
  · exact az rfl
  · apply w0;ext i; simpa [dot,col] using h0 i
  · apply v0;ext i; simpa [dot,col] using h0 i
  · apply wv;ext i; specialize h0 i;by_cases V : i∈v <;> by_cases W : i∈w <;> simp_all [dot,col]
  · apply u0;ext i; simpa [dot,col] using h0 i
  · apply wu;ext i; specialize h0 i;by_cases U : i∈u <;> by_cases W : i∈w <;> simp_all [dot,col]
  · apply uv;ext i; specialize h0 i;by_cases U : i∈u <;> by_cases V : i∈v <;> simp_all [dot,col]
  · apply ws;ext i; specialize h0 i
    by_cases U : i∈u <;> by_cases V : i∈v <;> by_cases W : i∈w <;> simp_all [dot,col]
def words (p : Color → Bool) (t : Color) :=
  t=z ∨ p t=true ∨ (∃ a b,a≠b ∧ p a=true ∧ p b=true ∧ add a b=t) ∨
    ∃ a b c,a≠b ∧ a≠c ∧ b≠c ∧ p a=true ∧ p b=true ∧ p c=true ∧ add (add a b) c=t
instance (p : Color → Bool) (t : Color) : Decidable (words p t) := by unfold words;infer_instance

def basis (a b c : Color) := a≠b ∧ a≠c ∧ b≠c ∧ ∀t : Color,
  t=z ∨ t=a ∨ t=b ∨ t=c ∨ add a b=t ∨ add a c=t ∨ add b c=t ∨ add (add a b) c=t
instance (a b c : Color) : Decidable (basis a b c) := by unfold basis;infer_instance
theorem basisWords {p : Color → Bool} {a b c : Color} (bas : basis a b c)
    (ha : p a=true) (hb : p b=true) (hc : p c=true) (t) : words p t := by
  obtain ⟨ab,ac,bc,rep⟩:=bas
  rcases rep t with h|h|h|h|h|h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl (h ▸ ha))
  · exact Or.inr (Or.inl (h ▸ hb))
  · exact Or.inr (Or.inl (h ▸ hc))
  · exact Or.inr (Or.inr (Or.inl ⟨_,_,ab,ha,hb,h⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨_,_,ac,ha,hc,h⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨_,_,bc,hb,hc,h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨_,_,_,ab,ac,bc,ha,hb,hc,h⟩))
theorem plane1 {p : Color → Bool} (hp : spans p) (h1 : p (false,false,true)≠true) (h3 : p (false,true,true)≠true) (h5 : p (true,false,true)≠true) (h7 : p (true,true,true)≠true) : False := by
  obtain ⟨⟨a,b,c⟩,inside,yes⟩:=hp (false,false,true) (by decide)
  cases a <;> cases b <;> cases c <;> simp_all [dot]
theorem plane2 {p : Color → Bool} (hp : spans p) (h2 : p (false,true,false)≠true) (h3 : p (false,true,true)≠true) (h6 : p (true,true,false)≠true) (h7 : p (true,true,true)≠true) : False := by
  obtain ⟨⟨a,b,c⟩,inside,yes⟩:=hp (false,true,false) (by decide)
  cases a <;> cases b <;> cases c <;> simp_all [dot]
theorem plane3 {p : Color → Bool} (hp : spans p) (h1 : p (false,false,true)≠true) (h2 : p (false,true,false)≠true) (h5 : p (true,false,true)≠true) (h6 : p (true,true,false)≠true) : False := by
  obtain ⟨⟨a,b,c⟩,inside,yes⟩:=hp (false,true,true) (by decide)
  cases a <;> cases b <;> cases c <;> simp_all [dot]
theorem plane4 {p : Color → Bool} (hp : spans p) (h4 : p (true,false,false)≠true) (h5 : p (true,false,true)≠true) (h6 : p (true,true,false)≠true) (h7 : p (true,true,true)≠true) : False := by
  obtain ⟨⟨a,b,c⟩,inside,yes⟩:=hp (true,false,false) (by decide)
  cases a <;> cases b <;> cases c <;> simp_all [dot]
theorem plane5 {p : Color → Bool} (hp : spans p) (h1 : p (false,false,true)≠true) (h3 : p (false,true,true)≠true) (h4 : p (true,false,false)≠true) (h6 : p (true,true,false)≠true) : False := by
  obtain ⟨⟨a,b,c⟩,inside,yes⟩:=hp (true,false,true) (by decide)
  cases a <;> cases b <;> cases c <;> simp_all [dot]
theorem plane6 {p : Color → Bool} (hp : spans p) (h2 : p (false,true,false)≠true) (h3 : p (false,true,true)≠true) (h4 : p (true,false,false)≠true) (h5 : p (true,false,true)≠true) : False := by
  obtain ⟨⟨a,b,c⟩,inside,yes⟩:=hp (true,true,false) (by decide)
  cases a <;> cases b <;> cases c <;> simp_all [dot]
theorem plane7 {p : Color → Bool} (hp : spans p) (h1 : p (false,false,true)≠true) (h2 : p (false,true,false)≠true) (h4 : p (true,false,false)≠true) (h7 : p (true,true,true)≠true) : False := by
  obtain ⟨⟨a,b,c⟩,inside,yes⟩:=hp (true,true,true) (by decide)
  cases a <;> cases b <;> cases c <;> simp_all [dot]
set_option maxHeartbeats 2000000 in
theorem shortWords (p : Color → Bool) (hp : spans p) (t) : words p t := by
  by_cases h1 : p (false,false,true)=true
  · by_cases h2 : p (false,true,false)=true
    · by_cases h3 : p (false,true,true)=true
      · by_cases h4 : p (true,false,false)=true
        · exact basisWords (by decide : basis (false,false,true) (false,true,false) (true,false,false)) h1 h2 h4 t
        · by_cases h5 : p (true,false,true)=true
          · exact basisWords (by decide : basis (false,false,true) (false,true,false) (true,false,true)) h1 h2 h5 t
          · by_cases h6 : p (true,true,false)=true
            · exact basisWords (by decide : basis (false,false,true) (false,true,false) (true,true,false)) h1 h2 h6 t
            · by_cases h7 : p (true,true,true)=true
              · exact basisWords (by decide : basis (false,false,true) (false,true,false) (true,true,true)) h1 h2 h7 t
              · exact False.elim (plane4 hp h4 h5 h6 h7)
      · by_cases h4 : p (true,false,false)=true
        · exact basisWords (by decide : basis (false,false,true) (false,true,false) (true,false,false)) h1 h2 h4 t
        · by_cases h5 : p (true,false,true)=true
          · exact basisWords (by decide : basis (false,false,true) (false,true,false) (true,false,true)) h1 h2 h5 t
          · by_cases h6 : p (true,true,false)=true
            · exact basisWords (by decide : basis (false,false,true) (false,true,false) (true,true,false)) h1 h2 h6 t
            · by_cases h7 : p (true,true,true)=true
              · exact basisWords (by decide : basis (false,false,true) (false,true,false) (true,true,true)) h1 h2 h7 t
              · exact False.elim (plane4 hp h4 h5 h6 h7)
    · by_cases h3 : p (false,true,true)=true
      · by_cases h4 : p (true,false,false)=true
        · exact basisWords (by decide : basis (false,false,true) (false,true,true) (true,false,false)) h1 h3 h4 t
        · by_cases h5 : p (true,false,true)=true
          · exact basisWords (by decide : basis (false,false,true) (false,true,true) (true,false,true)) h1 h3 h5 t
          · by_cases h6 : p (true,true,false)=true
            · exact basisWords (by decide : basis (false,false,true) (false,true,true) (true,true,false)) h1 h3 h6 t
            · by_cases h7 : p (true,true,true)=true
              · exact basisWords (by decide : basis (false,false,true) (false,true,true) (true,true,true)) h1 h3 h7 t
              · exact False.elim (plane4 hp h4 h5 h6 h7)
      · by_cases h4 : p (true,false,false)=true
        · by_cases h5 : p (true,false,true)=true
          · by_cases h6 : p (true,true,false)=true
            · exact basisWords (by decide : basis (false,false,true) (true,false,false) (true,true,false)) h1 h4 h6 t
            · by_cases h7 : p (true,true,true)=true
              · exact basisWords (by decide : basis (false,false,true) (true,false,false) (true,true,true)) h1 h4 h7 t
              · exact False.elim (plane2 hp h2 h3 h6 h7)
          · by_cases h6 : p (true,true,false)=true
            · exact basisWords (by decide : basis (false,false,true) (true,false,false) (true,true,false)) h1 h4 h6 t
            · by_cases h7 : p (true,true,true)=true
              · exact basisWords (by decide : basis (false,false,true) (true,false,false) (true,true,true)) h1 h4 h7 t
              · exact False.elim (plane2 hp h2 h3 h6 h7)
        · by_cases h5 : p (true,false,true)=true
          · by_cases h6 : p (true,true,false)=true
            · exact basisWords (by decide : basis (false,false,true) (true,false,true) (true,true,false)) h1 h5 h6 t
            · by_cases h7 : p (true,true,true)=true
              · exact basisWords (by decide : basis (false,false,true) (true,false,true) (true,true,true)) h1 h5 h7 t
              · exact False.elim (plane2 hp h2 h3 h6 h7)
          · exact False.elim (plane6 hp h2 h3 h4 h5)
  · by_cases h2 : p (false,true,false)=true
    · by_cases h3 : p (false,true,true)=true
      · by_cases h4 : p (true,false,false)=true
        · exact basisWords (by decide : basis (false,true,false) (false,true,true) (true,false,false)) h2 h3 h4 t
        · by_cases h5 : p (true,false,true)=true
          · exact basisWords (by decide : basis (false,true,false) (false,true,true) (true,false,true)) h2 h3 h5 t
          · by_cases h6 : p (true,true,false)=true
            · exact basisWords (by decide : basis (false,true,false) (false,true,true) (true,true,false)) h2 h3 h6 t
            · by_cases h7 : p (true,true,true)=true
              · exact basisWords (by decide : basis (false,true,false) (false,true,true) (true,true,true)) h2 h3 h7 t
              · exact False.elim (plane4 hp h4 h5 h6 h7)
      · by_cases h4 : p (true,false,false)=true
        · by_cases h5 : p (true,false,true)=true
          · exact basisWords (by decide : basis (false,true,false) (true,false,false) (true,false,true)) h2 h4 h5 t
          · by_cases h6 : p (true,true,false)=true
            · by_cases h7 : p (true,true,true)=true
              · exact basisWords (by decide : basis (false,true,false) (true,false,false) (true,true,true)) h2 h4 h7 t
              · exact False.elim (plane1 hp h1 h3 h5 h7)
            · by_cases h7 : p (true,true,true)=true
              · exact basisWords (by decide : basis (false,true,false) (true,false,false) (true,true,true)) h2 h4 h7 t
              · exact False.elim (plane1 hp h1 h3 h5 h7)
        · by_cases h5 : p (true,false,true)=true
          · by_cases h6 : p (true,true,false)=true
            · exact basisWords (by decide : basis (false,true,false) (true,false,true) (true,true,false)) h2 h5 h6 t
            · exact False.elim (plane5 hp h1 h3 h4 h6)
          · by_cases h6 : p (true,true,false)=true
            · by_cases h7 : p (true,true,true)=true
              · exact basisWords (by decide : basis (false,true,false) (true,true,false) (true,true,true)) h2 h6 h7 t
              · exact False.elim (plane1 hp h1 h3 h5 h7)
            · exact False.elim (plane5 hp h1 h3 h4 h6)
    · by_cases h3 : p (false,true,true)=true
      · by_cases h4 : p (true,false,false)=true
        · by_cases h5 : p (true,false,true)=true
          · exact basisWords (by decide : basis (false,true,true) (true,false,false) (true,false,true)) h3 h4 h5 t
          · by_cases h6 : p (true,true,false)=true
            · exact basisWords (by decide : basis (false,true,true) (true,false,false) (true,true,false)) h3 h4 h6 t
            · exact False.elim (plane3 hp h1 h2 h5 h6)
        · by_cases h5 : p (true,false,true)=true
          · by_cases h6 : p (true,true,false)=true
            · by_cases h7 : p (true,true,true)=true
              · exact basisWords (by decide : basis (false,true,true) (true,false,true) (true,true,true)) h3 h5 h7 t
              · exact False.elim (plane7 hp h1 h2 h4 h7)
            · by_cases h7 : p (true,true,true)=true
              · exact basisWords (by decide : basis (false,true,true) (true,false,true) (true,true,true)) h3 h5 h7 t
              · exact False.elim (plane7 hp h1 h2 h4 h7)
          · by_cases h6 : p (true,true,false)=true
            · by_cases h7 : p (true,true,true)=true
              · exact basisWords (by decide : basis (false,true,true) (true,true,false) (true,true,true)) h3 h6 h7 t
              · exact False.elim (plane7 hp h1 h2 h4 h7)
            · exact False.elim (plane3 hp h1 h2 h5 h6)
      · by_cases h4 : p (true,false,false)=true
        · by_cases h5 : p (true,false,true)=true
          · by_cases h6 : p (true,true,false)=true
            · exact basisWords (by decide : basis (true,false,false) (true,false,true) (true,true,false)) h4 h5 h6 t
            · by_cases h7 : p (true,true,true)=true
              · exact basisWords (by decide : basis (true,false,false) (true,false,true) (true,true,true)) h4 h5 h7 t
              · exact False.elim (plane2 hp h2 h3 h6 h7)
          · by_cases h6 : p (true,true,false)=true
            · by_cases h7 : p (true,true,true)=true
              · exact basisWords (by decide : basis (true,false,false) (true,true,false) (true,true,true)) h4 h6 h7 t
              · exact False.elim (plane1 hp h1 h3 h5 h7)
            · exact False.elim (plane3 hp h1 h2 h5 h6)
        · by_cases h5 : p (true,false,true)=true
          · by_cases h6 : p (true,true,false)=true
            · by_cases h7 : p (true,true,true)=true
              · exact basisWords (by decide : basis (true,false,true) (true,true,false) (true,true,true)) h5 h6 h7 t
              · exact False.elim (plane7 hp h1 h2 h4 h7)
            · exact False.elim (plane5 hp h1 h3 h4 h6)
          · exact False.elim (plane6 hp h2 h3 h4 h5)
end PEqualNP.Outside.L_lib_1546_aux

namespace PEqualNP.Outside.L_lib_1546_aux
def eval (u v w S : Mask k) : Color := (bit u S,bit v S,bit w S)
theorem evalYes {u v w S : Mask k} : yes u v w S=true ↔ eval u v w S=allOn := by
  simp [yes,eval,allOn,Prod.ext_iff,and_assoc]
def flip (i : Fin k) (S : Mask k) := if i∈S then S.erase i else insert i S
theorem flipFlip (i : Fin k) (S : Mask k) : flip i (flip i S)=S := by
  by_cases h : i∈S <;> simp [flip,h]
theorem flipBit (x S : Mask k) (i : Fin k) : bit x (flip i S)=xor (bit x S) (decide (i∈x)) := by
  by_cases h : i∈S
  · rw [flip,if_pos h]
    by_cases hx : i∈x
    · have id : x∩S.erase i=(x∩S).erase i := by ext;simp;tauto
      have hin:=Finset.mem_inter.mpr ⟨hx,h⟩
      have pos:=Finset.card_pos.mpr ⟨i,hin⟩
      by_cases odd : (x∩S).card % 2=1
      · have hno : ((x∩S).card-1)%2≠1 := by omega
        simp [bit,id,Finset.card_erase_of_mem hin,hx,odd,hno]
      · have hyes : ((x∩S).card-1)%2=1 := by omega
        simp [bit,id,Finset.card_erase_of_mem hin,hx,odd,hyes]
    · have id : x∩S.erase i=x∩S := by ext a;by_cases ha : a=i <;> simp_all
      simp [bit,id,hx]
  · rw [flip,if_neg h]
    by_cases hx : i∈x
    · have id : x∩insert i S=insert i (x∩S) := by ext a;by_cases ha : a=i <;> simp_all
      have hn : i∉x∩S := fun hi => h (Finset.mem_inter.mp hi).2
      by_cases odd : (x∩S).card % 2=1
      · have hno : ((x∩S).card+1)%2≠1 := by omega
        simp [bit,id,Finset.card_insert_of_notMem hn,hx,odd,hno]
      · have hyes : ((x∩S).card+1)%2=1 := by omega
        simp [bit,id,Finset.card_insert_of_notMem hn,hx,odd,hyes]
    · have id : x∩insert i S=x∩S := by ext a;by_cases ha : a=i <;> simp_all
      simp [bit,id,hx]
theorem evalFlip (u v w S : Mask k) (i : Fin k) :
    eval u v w (flip i S)=add (eval u v w S) (col u v w i) := by simp [eval,col,add,flipBit]
theorem evalEmpty (u v w : Mask k) : eval u v w ∅=z := by simp [eval,bit,z]
def flipEquiv (i : Fin k) : Mask k ≃ Mask k := ⟨flip i,flip i,flipFlip i,flipFlip i⟩
theorem addZero : ∀a,add z a=a ∧ add a z=a := by decide +kernel
theorem addAssoc : ∀a b c,add (add a b) c=add a (add b c) := by decide +kernel
theorem addCancel : ∀a b,add a (add a b)=b := by decide +kernel
theorem addComm : ∀a b,add a b=add b a := by decide +kernel
theorem evalOne (u v w : Mask k) (i : Fin k) : eval u v w {i}=col u v w i := by
  simpa [flip,evalEmpty,(addZero _).1] using evalFlip u v w ∅ i
theorem evalPair (u v w : Mask k) {i j : Fin k} (ne : i≠j) :
    eval u v w {i,j}=add (col u v w i) (col u v w j) := by
  simpa [flip,ne,evalOne,addComm (col u v w j)] using evalFlip u v w {j} i
theorem evalTriple (u v w : Mask k) {i j l : Fin k} (ij : i≠j) (il : i≠l) (jl : j≠l) :
    eval u v w {i,j,l}=add (add (col u v w i) (col u v w j)) (col u v w l) := by
  rw [addAssoc,addComm (col u v w i)]
  simpa [flip,ij,il,evalPair u v w jl] using evalFlip u v w {j,l} i
end PEqualNP.Outside.L_lib_1546_aux

namespace PEqualNP.Outside.L_lib_1546_aux
def part (c : Color) : Bool × Bool := (xor c.1 c.2.1,xor c.1 c.2.2)
theorem partEq : ∀a b,part a=part b → add a b=allOn ∨ add (add allOn a) b=allOn := by decide +kernel
theorem collide (hk : 6≤k) (i : Fin k) (f : Fin k → Color) :
    ∃ j l,j≠i ∧ l≠i ∧ j≠l ∧ part (f j)=part (f l) := by
  classical
  let A := Finset.univ.erase i
  let key (j : ↥A) := part (f j.val)
  have no : ¬Function.Injective key := by
    intro hin
    have bound:=Fintype.card_le_of_injective key hin
    simp [A] at bound;omega
  unfold Function.Injective at no
  push_neg at no
  obtain ⟨x,y,eq,ne⟩:=no
  exact ⟨x,y,(Finset.mem_erase.mp x.property).1,(Finset.mem_erase.mp y.property).1,fun h => ne (Subtype.ext h),eq⟩
theorem shortHit {u v w : Mask k} (hk : 6≤k) (ind : independent u v w) :
    ∃S : Mask k,(S.card=2 ∨ S.card=3) ∧ yes u v w S=true := by
  let f := col u v w
  have pairs (i j : Fin k) (ij : i≠j) (sum : add (f i) (f j)=allOn) :
      ∃ S : Mask k,(S.card=2 ∨ S.card=3) ∧ yes u v w S=true :=
    ⟨{i,j},Or.inl (by simp [ij]),evalYes.mpr ((evalPair u v w ij).trans sum)⟩
  have triples (i j l : Fin k) (ij : i≠j) (il : i≠l) (jl : j≠l) (sum : add (add (f i) (f j)) (f l)=allOn) :
      ∃ S : Mask k,(S.card=2 ∨ S.card=3) ∧ yes u v w S=true :=
    ⟨{i,j,l},Or.inr (by simp [ij,il,jl]),evalYes.mpr ((evalTriple u v w ij il jl).trans sum)⟩
  obtain zero|one|two|three:=shortWords _ (observed ind) allOn
  · exact False.elim ((by decide : allOn≠z) zero)
  · obtain ⟨i,hi⟩:=of_decide_eq_true one
    obtain ⟨j,l,ji,li,jl,key⟩:=collide hk i f
    rcases partEq _ _ key with h|h
    · exact pairs j l jl h
    · exact triples i j l ji.symm li.symm jl (by simpa only [show f i=allOn from hi] using h)
  · obtain ⟨a,b,ab,ha,hb,eq⟩:=two
    obtain ⟨i,rfl⟩:=of_decide_eq_true ha;obtain ⟨j,rfl⟩:=of_decide_eq_true hb
    exact pairs i j (fun h => ab (congrArg f h)) eq
  · obtain ⟨a,b,c,ab,ac,bc,ha,hb,hc,eq⟩:=three
    obtain ⟨i,rfl⟩:=of_decide_eq_true ha;obtain ⟨j,rfl⟩:=of_decide_eq_true hb;obtain ⟨l,rfl⟩:=of_decide_eq_true hc
    exact triples i j l (fun h => ab (congrArg f h)) (fun h => ac (congrArg f h)) (fun h => bc (congrArg f h)) eq
theorem sufficient {mask : Fin n → Mask k} (hk : 6≤k) (many : frequent e mask) : hits e mask := by
  intro u v w ind;obtain ⟨S,size,ok⟩:=shortHit hk ind
  apply (many S size).trans_le;apply Finset.card_le_card;intro j h
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp h).2 ▸ ok⟩
end PEqualNP.Outside.L_lib_1546_aux

namespace PEqualNP.Outside.L_lib_1546_aux
def req (k : Nat) : Finset (Mask k) :=
  Finset.univ.powersetCard 2 ∪ Finset.univ.powersetCard 3
theorem memReq {S : Mask k} : S∈req k ↔ S.card=2 ∨ S.card=3 := by simp [req,Finset.mem_powersetCard]
theorem countReq k : (req k).card=Nat.choose k 2+Nat.choose k 3 := by
  unfold req;rw [Finset.card_union_of_disjoint]
  · simp [Finset.card_powersetCard]
  · apply Finset.disjoint_left.mpr;intro S h h';have a:=(Finset.mem_powersetCard.mp h).2;have b:=(Finset.mem_powersetCard.mp h').2;omega
theorem requiredLower {mask : Fin n → Mask k} (h : frequent e mask) : (e+1)*(k.choose 2+k.choose 3)≤n := by
  have a:=Finset.sum_le_sum (s:=req k) (fun S hS => Nat.succ_le_of_lt (h S (memReq.mp hS)))
  rw [Finset.sum_card_fiberwise_eq_card_filter] at a
  have b:=Finset.card_le_univ (Finset.univ.filter (fun i => mask i∈req k))
  simpa [countReq,Nat.mul_comm] using a.trans b
theorem listAll (k n e : Nat) (enough : (e+1)*(k.choose 2+k.choose 3)≤n) :
    ∃mask : Fin n → Mask k,(∀j,(mask j).card≤3) ∧ frequent e mask := by
  classical
  let A := ↥(req k) × Fin (e+1)
  have hcard : Fintype.card A≤n := by simpa [A,countReq,Nat.mul_comm] using enough
  let f : A ↪ Fin n := (Fintype.equivFin A).toEmbedding.trans (Fin.castLEEmb hcard)
  let m (j : Fin n) : Mask k := if h : ∃a,f a=j then (Classical.choose h).1.val else ∅
  have read (a : A) : m (f a)=a.1.val := by
    have ex : ∃b,f b=f a := ⟨a,rfl⟩
    simp only [m,dif_pos ex];rw [f.injective (Classical.choose_spec ex)]
  refine ⟨m,?_,?_⟩
  · intro j;by_cases hj : ∃a,f a=j
    · obtain ⟨a,rfl⟩:=hj;rw [read];have h:=memReq.mp a.1.property;omega
    · simp [m,hj]
  · intro S hs
    let a : ↥(req k) := ⟨S,memReq.mpr hs⟩
    let images (i : Fin (e+1)) := f (a,i)
    have inj : Function.Injective images := fun i j eq => congrArg Prod.snd (f.injective eq)
    have sub : Finset.univ.image images⊆Finset.univ.filter (fun j => m j=S) := by
      intro j hj;obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,read (a,i)⟩
    have h:=Finset.card_le_card sub;rw [Finset.card_image_of_injective _ inj] at h;simpa using h
end PEqualNP.Outside.L_lib_1546_aux

namespace PEqualNP.Outside.L_lib_1546_aux
def Trans (u v w : Mask k) (c : Color) := ∃F : Mask k ≃ Mask k,∀S,eval u v w (F S)=add (eval u v w S) c
theorem transAdd {u v w : Mask k} {a b : Color} (ha : Trans u v w a) (hb : Trans u v w b) : Trans u v w (add a b) := by
  obtain ⟨A,hA⟩:=ha;obtain ⟨B,hB⟩:=hb
  exact ⟨A.trans B,fun S => by change eval u v w (B (A S))=_;rw [hB,hA,addAssoc]⟩
theorem allTrans {u v w : Mask k} (ind : independent u v w) (t : Color) : Trans u v w t := by
  have one (a : Color) (obs : decide (∃i,col u v w i=a)=true) : Trans u v w a := by
    obtain ⟨i,rfl⟩:=of_decide_eq_true obs
    exact ⟨flipEquiv i,fun S => evalFlip u v w S i⟩
  rcases shortWords _ (observed ind) t with h|h|h|h
  · subst t;exact ⟨Equiv.refl _,fun S => ((addZero _).2).symm⟩
  · exact one _ h
  · obtain ⟨a,b,_,ha,hb,rfl⟩:=h;exact transAdd (one _ ha) (one _ hb)
  · obtain ⟨a,b,c,_,_,_,ha,hb,hc,rfl⟩:=h;exact transAdd (transAdd (one _ ha) (one _ hb)) (one _ hc)
theorem uniform {u v w : Mask k} (ind : independent u v w) :
    8*(Finset.univ.filter (fun S => yes u v w S=true)).card=Fintype.card (Mask k) := by
  classical
  let f := eval u v w
  let fib (c : Color) := Finset.univ.filter (fun S => f S=c)
  have ccard (c : Color) : (fib c).card=(fib allOn).card := by
    let d := add c allOn
    obtain ⟨F,action⟩:=allTrans ind d
    have flip (s : Color) : add s d=allOn ↔ s=c := by
      have h : ∀a b t : Color,add a (add b t)=t ↔ a=b := by decide +kernel
      exact h s c allOn
    have im : (fib c).image F=fib allOn := by
      ext S;obtain ⟨T,rfl⟩:=F.surjective S
      simp only [Finset.mem_image,fib,Finset.mem_filter,Finset.mem_univ,true_and,F.injective.eq_iff,exists_eq_right]
      exact (flip (f T)).symm.trans (by change (add (f T) d=allOn) ↔ eval u v w (F T)=allOn;rw [action])
    rw [←im,Finset.card_image_of_injective _ F.injective]
  have cnt:=Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Mask k)) Finset.univ f
  change (∑ c,(fib c).card)=_ at cnt
  simp only [ccard,Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul,Finset.mem_univ,Finset.filter_true_of_mem,Finset.card_univ] at cnt
  have same : Finset.univ.filter (fun S => yes u v w S=true)=fib allOn := by ext;simp [fib,f,evalYes]
  rw [same];simpa [Color] using cnt
end PEqualNP.Outside.L_lib_1546_aux

namespace PEqualNP.Outside.L_lib_1546_aux
open scoped Classical
variable {A M : Type} [Fintype A] [Fintype M] [Nonempty M]
def score (h : A → M → Bool) (m : Fin t → M) (a : A) := ∑i,(h a (m i)).toNat
def weight (h : A → M → Bool) (m : Fin t → M) (a : A) := (1/2 : ℚ)^score h m a
def total (h : A → M → Bool) (m : Fin t → M) := ∑a,weight h m a
theorem scale (h : A → M → Bool) (m : Fin t → M) (a : A) (x : M) :
    weight h (Fin.cons x m) a = if h a x=true then weight h m a/2 else weight h m a := by
  unfold weight score;rw [Fin.sum_univ_succ];simp only [Fin.cons_zero,Fin.cons_succ]
  cases hx:h a x <;> simp [pow_add] <;> ring
theorem mean (h : A → M → Bool) (unif : ∀a,8*(Finset.univ.filter (fun x => h a x=true)).card=Fintype.card M)
    (m : Fin t → M) : ∑x,total h (Fin.cons x m)=(Fintype.card M : ℚ)*((15/16)*total h m) := by
  classical
  have each (a : A) : (∑x,weight h (Fin.cons x m) a)=(Fintype.card M : ℚ)*((15/16)*weight h m a) := by
    simp only [scale,Finset.sum_ite,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    have hp := Finset.card_filter_add_card_filter_not (s:=(Finset.univ : Finset M)) (fun x => h a x=true)
    rw [Finset.card_univ] at hp
    have huv : (8 : ℚ)*((Finset.univ.filter (fun x => h a x=true)).card : ℚ)=(Fintype.card M : ℚ) := by exact_mod_cast unif a
    have part : ((Finset.univ.filter (fun x => h a x=true)).card : ℚ)+((Finset.univ.filter (fun x => ¬h a x=true)).card : ℚ)=(Fintype.card M : ℚ) := by exact_mod_cast hp
    linear_combination (weight h m a)*part-(weight h m a/16)*huv
  unfold total;rw [Finset.sum_comm];simp only [each,Finset.mul_sum]
theorem sample (h : A → M → Bool) (unif : ∀a,8*(Finset.univ.filter (fun x => h a x=true)).card=Fintype.card M)
    (t : Nat) : ∃m : Fin t → M,total h m ≤ (Fintype.card A : ℚ)*(15/16)^t := by
  classical
  induction t with
  | zero => exact ⟨Fin.elim0,by simp [total,weight,score]⟩
  | succ t ih =>
    obtain ⟨m,old⟩:=ih
    have chooseOne : ∃x,total h (Fin.cons x m)≤(15/16)*total h m := by
      by_contra! bad
      have strict:=Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun x _ => bad x)
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mean h unif m] at strict
      exact (lt_irrefl _ strict)
    obtain ⟨x,small⟩:=chooseOne
    refine ⟨Fin.cons x m,small.trans ?_⟩
    calc
      (15/16)*total h m ≤ (15/16)*((Fintype.card A : ℚ)*(15/16)^t) := by gcongr
      _ = _ := by rw [pow_succ];ring
end PEqualNP.Outside.L_lib_1546_aux

namespace PEqualNP.Outside.L_lib_1546_aux
open scoped Classical
theorem enoughSteps {k e : Nat} {card : Nat} (hcard : card≤2^(3*k)) :
    (card : ℚ)*(15/16)^(16*(3*k+e+1))<(1/2 : ℚ)^e := by
  have small : (15/16 : ℚ)^16≤1/2 := by norm_num
  have bound : (card : ℚ)≤(2 : ℚ)^(3*k) := by exact_mod_cast hcard
  have half : (2 : ℚ)^(3*k)*(1/2 : ℚ)^(3*k)=1 := by rw [←mul_pow];norm_num
  rw [pow_mul]
  calc
    _ ≤ (2 : ℚ)^(3*k)*(1/2 : ℚ)^(3*k+e+1) := by gcongr
    _ = (1/2 : ℚ)^e / 2 := by rw [pow_succ,pow_add];linear_combination ((1/2 : ℚ)^e/2)*half
    _ < _ := by have pos : 0<(1/2 : ℚ)^e := by positivity
                linarith
theorem unrestricted (k e : Nat) : ∃m : Fin (16*(3*k+e+1)) → Mask k,hits e m := by
  classical
  let A := {t : Mask k × Mask k × Mask k // independent t.1 t.2.1 t.2.2}
  let h (a : A) (s : Mask k) := yes a.val.1 a.val.2.1 a.val.2.2 s
  have bound : Fintype.card A≤2^(3*k) := by
    have b:=Fintype.card_le_of_injective (fun a : A => a.val) Subtype.val_injective
    calc
      _ ≤ _ := b
      _ = 2^(3*k) := by simp [Mask,show 3*k=k+(k+k) by omega,pow_add]
  obtain ⟨m,totalBound⟩:=sample h (fun a => uniform a.property) (16*(3*k+e+1))
  refine ⟨m,?_⟩;intro u v w ind
  let a : A := ⟨(u,v,w),ind⟩
  have one := Finset.single_le_sum (s:=Finset.univ) (f:=weight h m) (fun i _ => show 0≤weight h m i by unfold weight;positivity) (Finset.mem_univ a)
  have lt : (1/2 : ℚ)^score h m a<(1/2 : ℚ)^e := one.trans_lt (totalBound.trans_lt (enoughSteps bound))
  have gt : e<score h m a := by
    by_contra! low
    have opp : (1/2 : ℚ)^e≤(1/2 : ℚ)^score h m a := pow_le_pow_of_le_one (by norm_num) (by norm_num) low
    linarith
  have value (j) : (h a (m j)).toNat = if yes u v w (m j)=true then 1 else 0 := by
    change (yes u v w (m j)).toNat=_;cases yes u v w (m j) <;> rfl
  simpa [score,value] using gt
end PEqualNP.Outside.L_lib_1546_aux

namespace PEqualNP.Outside.L_lib_1546_aux
noncomputable def fixedFilter {α : Type*} (P : α → Prop) (A : Finset α) := @Finset.filter α P (fun _ => Classical.propDecidable _) A
theorem filterUnique {α : Type*} (P : α → Prop) (d : DecidablePred P) (A : Finset α) :
    @Finset.filter α P d A=fixedFilter P A := by ext;simp only [fixedFilter,Finset.mem_filter]
noncomputable def sameDecision (P : Prop) := @decide P (Classical.propDecidable P)
theorem decUnique (P : Prop) (d : Decidable P) : @decide P d=sameDecision P := by unfold sameDecision;congr 1
noncomputable def cup {α : Type} (A B : Finset α) := @max _ (@Finset.instMax α (Classical.decEq α)) A B
theorem cupEq {α : Type} (d : DecidableEq α) (A B : Finset α) : @max _ (@Finset.instMax α d) A B=cup A B := by ext;simp only [cup,Finset.mem_union]
noncomputable def cap {α : Type} (A B : Finset α) := @min _ (@Finset.instMin α (Classical.decEq α)) A B
theorem capEq {α : Type} (d : DecidableEq α) (A B : Finset α) : @min _ (@Finset.instMin α d) A B=cap A B := by ext;simp only [cap,Finset.mem_inter]
noncomputable def diff {α : Type} (A B : Finset α) := @SDiff.sdiff _ (@Finset.instSDiff α (Classical.decEq α)) A B
theorem diffEq {α : Type} (d : DecidableEq α) (A B : Finset α) : @SDiff.sdiff _ (@Finset.instSDiff α d) A B=diff A B := by ext;simp only [diff,Finset.mem_sdiff]
theorem result (k e : Nat) (hk : 6≤k) :
    (∀ (n : Nat) (mask : Fin n → Mask k),(∀j,(mask j).card≤3) → (hits e mask ↔ frequent e mask)) ∧
    (∀n,(∃mask : Fin n → Mask k,(∀j,(mask j).card≤3) ∧ hits e mask) ↔ (e+1)*(k.choose 2+k.choose 3)≤n) ∧
    ∃mask : Fin (16*(3*k+e+1)) → Mask k,hits e mask := by
  refine ⟨fun _ _ small => ⟨necessary hk small,sufficient hk⟩,?_,unrestricted k e⟩
  intro n;constructor
  · rintro ⟨m,small,ok⟩;exact requiredLower (necessary hk small ok)
  · intro enough;obtain ⟨m,small,many⟩:=listAll k n e enough;exact ⟨m,small,sufficient hk many⟩
end PEqualNP.Outside.L_lib_1546_aux
open PEqualNP.Outside.L_lib_1546_aux in
theorem PEqualNP.Outside.L_lib_1546 : letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
∀ (k e : Nat), 6 ≤ k →
let L := Finset (Fin k)
let independent := fun (u v w : L) =>
  u ≠ ∅ ∧ v ≠ ∅ ∧ u ≠ v ∧ w ≠ ∅ ∧ w ≠ u ∧ w ≠ v ∧ w ≠ (u \ v) ∪ (v \ u)
let bit := fun (x S : L) => decide ((x ∩ S).card % 2 = 1)
let hits := fun {n : Nat} (mask : Fin n → L) => ∀ u v w : L, independent u v w →
  e < (Finset.univ.filter (fun j : Fin n => bit u (mask j) && bit v (mask j) && bit w (mask j))).card
(∀ (n : Nat) (mask : Fin n → L), (∀ j, (mask j).card ≤ 3) →
  (hits mask ↔ ∀ S : L, S.card = 2 ∨ S.card = 3 →
    e < (Finset.univ.filter (fun j : Fin n => mask j = S)).card)) ∧
(∀ n : Nat, (∃ mask : Fin n → L, (∀ j, (mask j).card ≤ 3) ∧ hits mask) ↔
  (e+1)*(Nat.choose k 2 + Nat.choose k 3) ≤ n) ∧
∃ mask : Fin (16*(3*k+e+1)) → L, hits mask := by
  classical
  intro k e hk L independent' bit' hits'
  have indEq (u v w : L) : independent' u v w ↔ independent u v w := by
    simp only [L,independent',independent,cupEq,diffEq]
  have bitEq (x s : L) : bit' x s=bit x s := by
    simp only [L,bit',bit,capEq,decUnique]
  have hitsEq {n} (m : Fin n → L) : hits' m ↔ hits e m := by
    simp only [hits',hits,indEq,yes,←bitEq,filterUnique];rfl
  simpa only [hitsEq,frequent,filterUnique] using result k e hk
