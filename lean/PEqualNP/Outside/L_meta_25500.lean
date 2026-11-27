import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25491
import PEqualNP.Outside.L_lib_370
import PEqualNP.MetaComplexity.Helpers.RepPath


namespace PEqualNP.Outside.L_meta_25500_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def lit {r h : ℕ} (b : Fin r → Fin h → Bool) (x : Fin r) (c : Fin (2*h)) :=
  b x ⟨c.val/2,(Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ 1)).2
    (lt_of_lt_of_eq c.isLt (Nat.mul_comm 2 h))⟩ == c.val.testBit 0

def lc {h : ℕ} (j : Fin h) (s : Bool) : Fin (2*h) :=
  ⟨2*j.val+s.toNat,by have := j.isLt; cases s <;> simp <;> omega⟩

@[simp] lemma lit_lc {r h : ℕ} (b : Fin r → Fin h → Bool) (u : Fin r) (j : Fin h) (s : Bool) :
    lit b u (lc j s) = (b u j == s) := by
  cases s <;> simp [lit,lc,Nat.testBit_zero,Nat.mul_add_mod,Nat.mul_mod_right,Nat.mul_add_div]

lemma litSep {r h : ℕ} {b : Fin r → Fin h → Bool} (inj : Function.Injective b)
    (u v : Fin r) (ne : u ≠ v) : ∃ c : Fin (2*h), lit b u c = true ∧ lit b v c = false := by
  classical
  have bit : ∃ j, b u j ≠ b v j := by
    by_contra! all
    exact ne (inj (funext all))
  obtain ⟨j,hj⟩ := bit
  refine ⟨lc j (b u j),?_,?_⟩
  · simp
  · simp [Ne.symm hj]

lemma nameBitsInj {k m : ℕ} {name : Fin m → Fin (2^k)} (inj : Function.Injective name) :
    Function.Injective (fun (a : Fin m) (j : Fin k) => (name a).val.testBit j.val) := by
  intro u v eqv
  apply inj
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < k
  · exact congrFun eqv ⟨i,h⟩
  · have pow : 2^k ≤ (2:Nat)^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow ((name u).isLt.trans_le pow), Nat.testBit_lt_two_pow ((name v).isLt.trans_le pow)]

abbrev OnlyRowOr {r : ℕ} (C : Circuit) : Prop :=
  ∀ u : Fin r, readsIn C (Finset.range C.size) u.val=1 ∧
    ∃ (j : Fin C.gates.length) (w : ℕ), (C.gates.get j).op=GateOp.or ∧
      ((C.gates.get j).inputs=[u.val,w] ∨ (C.gates.get j).inputs=[w,u.val])

end PEqualNP.Outside.L_meta_25500_aux



namespace PEqualNP.Outside.L_meta_25500_aux
open PEqualNP.Represents

private def slot500 {h : Nat} (c : Fin (2*h)) : Fin h :=
  ⟨c.val/2,(Nat.div_lt_iff_lt_mul (by decide : 0<2)).2 (by have := c.isLt;omega)⟩

private theorem lcSlot500 {h : Nat} (c : Fin (2*h)) : lc (slot500 c) (c.val.testBit 0) = c := by
  apply Fin.ext
  change 2*(c.val/2)+(c.val.testBit 0).toNat=c.val
  have bound := Nat.mod_lt c.val (by decide : 0<2)
  have total := Nat.mod_add_div c.val 2
  by_cases e : c.val % 2=1
  · simp [Nat.testBit_zero,e]; omega
  · have zero : c.val % 2=0 := by omega
    simp [Nat.testBit_zero,zero]; omega

private theorem lcInj500 {h : Nat} {i j : Fin h} {a b : Bool} (e : lc i a=lc j b) :
    i=j ∧ a=b := by
  have v := congrArg Fin.val e
  cases a <;> cases b <;> simp [lc] at v ⊢ <;> omega

private theorem literalSub500 {r h q t : Nat} (b : Fin r → Fin h → Bool) (f : Fin q → Fin h)
    (inj : Function.Injective f) (bound : RepSizeAtMost (lit b) t) :
    RepSizeAtMost (lit (fun a j => b a (f j))) t := by
  let e (c : Fin (2*q)) := lc (f (slot500 c)) (c.val.testBit 0)
  have ie : Function.Injective e := by
    intro u v he
    obtain ⟨hf,hs⟩ := lcInj500 he
    have hj := inj hf
    calc
      u = lc (slot500 u) (u.val.testBit 0) := (lcSlot500 u).symm
      _ = lc (slot500 v) (v.val.testBit 0) := by rw [hj,hs]
      _ = v := lcSlot500 v
  have H := PEqualNP.Outside.L_lib_370 _ _ _ _ _ (lit b) id e Function.injective_id ie bound
  have eqv : (fun u c => lit b (id u) (e c)) = lit (fun a j => b a (f j)) := by
    funext u c
    change lit b u (lc _ _) = _
    rw [lit_lc]
    rfl
  rwa [eqv] at H

theorem trim500 {r h t : Nat} (b : Fin r → Fin h → Bool) (hr : 3≤r) (hh : 2≤h)
    (inj : Function.Injective b) (rep : RepSizeAtMost (lit b) t)
    (missing : ¬ (∀ j, ∃ u v, b u j=false ∧ b v j=true)) :
    ∃ (q : Nat) (e : Fin q → Fin h), 2≤q ∧ q<h ∧ Function.Injective e ∧
      Function.Injective (fun a j => b a (e j)) ∧ RepSizeAtMost (lit (fun a j => b a (e j))) t := by
  classical
  cases h with
  | zero => omega
  | succ q =>
    obtain ⟨j,hj⟩ := not_forall.mp missing
    have fixed (a a' : Fin r) : b a j=b a' j := by
      cases ha : b a j <;> cases ha' : b a' j
      · rfl
      · exact (hj ⟨a,a',ha,ha'⟩).elim
      · exact (hj ⟨a',a,ha',ha⟩).elim
      · rfl
    have ie : Function.Injective j.succAbove := Fin.succAbove_right_injective
    have ri : Function.Injective (fun a l => b a (j.succAbove l)) := by
      intro a a' he
      apply inj
      funext l
      by_cases e : l=j
      · rw [e]; exact fixed _ _
      · obtain ⟨i,hi⟩ := Fin.exists_succAbove_eq_iff.mpr e
        rw [←hi]
        exact congrFun he i
    have qtwo : 2≤q := by
      have card := Fintype.card_le_of_injective _ ri
      simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool] at card
      by_contra hn
      have one : q=1 := by omega
      rw [one] at card
      simp at card
      omega
    exact ⟨q,j.succAbove,qtwo,by omega,ie,ri,literalSub500 b _ ie rep⟩

end PEqualNP.Outside.L_meta_25500_aux



namespace PEqualNP.Outside.L_meta_25500_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.RepReads PEqualNP.Represents

lemma another500 {r : ℕ} (hr : 2≤r) (u : Fin r) : ∃ v : Fin r, u ≠ v := by
  let a : Fin r := ⟨0,by omega⟩
  let b : Fin r := ⟨1,by omega⟩
  by_cases e : u=a
  · exact ⟨b,by rw [e]; intro he; have := congrArg Fin.val he; simp [a,b] at this⟩
  · exact ⟨a,e⟩

lemma allForcedLeft500 {r h : ℕ} {b : Fin r → Fin h → Bool} (hr : 2≤r)
    (inj : Function.Injective b) : forcedL (lit b) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro u
  obtain ⟨v,ne⟩ := another500 hr u
  obtain ⟨j,hu,hv⟩ := litSep inj u v ne
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,hu,v,hv⟩

lemma forcedPos500 {r h : ℕ} (b : Fin r → Fin h → Bool) (u : Fin r) (j : Fin h) :
    lc j (b u j) ∈ forcedR (lit b) := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,u,by simp,lc j (!(b u j)),?_⟩
  simp

private lemma lc_distinct {h : ℕ} {j j' : Fin h} {a b : Bool} (ne : j ≠ j') : lc j a ≠ lc j' b := by
  intro eqv
  apply ne
  apply Fin.ext
  have H := congrArg Fin.val eqv
  cases a <;> cases b <;> simp [lc] at H <;> omega

theorem pairBound500 {r h t : ℕ} (b : Fin r → Fin h → Bool) (hr : r=2) (hh : 2≤h)
    (inj : Function.Injective b) (rep : RepSizeAtMost (lit b) t) : 4≤t := by
  classical
  let u : Fin r := ⟨0,by omega⟩
  obtain ⟨v,ne⟩ := another500 (by omega) u
  obtain ⟨j,diff⟩ : ∃ j, b u j ≠ b v j := by
    by_contra! eqv
    exact ne (inj (funext eqv))
  obtain ⟨l,jl⟩ := another500 hh j
  let x := lc j (b u j)
  let y := lc j (b v j)
  let z := lc l (b u l)
  have xz : x ≠ z := lc_distinct jl
  have yz : y ≠ z := lc_distinct jl
  have xy : x ≠ y := by
    intro e
    have eqv := congrArg Fin.val e
    change 2*j.val+(b u j).toNat = 2*j.val+(b v j).toNat at eqv
    cases hu : b u j <;> cases hv : b v j <;> simp_all
  have hx : x ∈ forcedR (lit b) := forcedPos500 b u j
  have hy : y ∈ forcedR (lit b) := forcedPos500 b v j
  have hz : z ∈ forcedR (lit b) := forcedPos500 b u l
  have sub : ({x,y,z} : Finset _) ⊆ forcedR (lit b) := by
    intro c hc
    simp only [Finset.mem_insert,Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl <;> assumption
  have cards := Finset.card_le_card sub
  have sc : ({x,y,z} : Finset _).card=3 := by simp [xy,xz,yz]
  rw [sc] at cards
  have H := reads_le (lit b) rep
  rw [allForcedLeft500 (by omega) inj] at H
  simp only [Finset.card_univ,Fintype.card_fin] at H
  omega

end PEqualNP.Outside.L_meta_25500_aux





namespace PEqualNP.Outside.L_meta_25500_aux
open PEqualNP.MetaComplexity PEqualNP.Represents

private theorem sharedValue {r h} (hr : 3≤r) (j : Fin h) (b : Fin r → Fin h → Bool) :
    ∃ u x : Fin r, u≠x ∧ b u j=b x j := by
  let p : Fin r := ⟨0,by omega⟩
  let q : Fin r := ⟨1,by omega⟩
  let z : Fin r := ⟨2,by omega⟩
  have pq : p≠q := by intro he; have e:=congrArg Fin.val he; dsimp [p,q] at e;omega
  have pz : p≠z := by intro he; have e:=congrArg Fin.val he; dsimp [p,z] at e;omega
  have qz : q≠z := by intro he; have e:=congrArg Fin.val he; dsimp [q,z] at e;omega
  by_cases e : b p j=b q j
  · exact ⟨p,q,pq,e⟩
  by_cases f : b p j=b z j
  · exact ⟨p,z,pz,f⟩
  refine ⟨q,z,qz,?_⟩
  cases h₁ : b p j <;> cases h₂ : b q j <;> cases h₃ : b z j <;> simp_all

theorem allBound500 {r h t : Nat} (b : Fin r → Fin h → Bool) (hr : 3≤r) (hh : 2≤h)
    (inj : Function.Injective b) (full : ∀ j, ∃ u v, b u j=false ∧ b v j=true)
    (rep : RepSizeAtMost (lit b) t) : r+2*h≤t := by
  classical
  let j : Fin h := ⟨0,by omega⟩
  have rowMiss (u : Fin r) : ∃ c, lit b u c=false := by
    refine ⟨lc j (!(b u j)),?_⟩
    rw [lit_lc];cases b u j <;> rfl
  have colBoth (c : Fin (2*h)) : ∃ a e, lit b a c=true ∧ lit b e c=false := by
    let k : Fin h := ⟨c.val/2,by have := c.isLt; omega⟩
    obtain ⟨a,e,ha,he⟩ := full k
    cases v : c.val.testBit 0 with
    | false =>
      refine ⟨a,e,?_⟩
      change (b a k == c.val.testBit 0) = true ∧ (b e k == c.val.testBit 0) = false
      rw [ha,he,v];decide
    | true =>
      refine ⟨e,a,?_⟩
      change (b e k == c.val.testBit 0) = true ∧ (b a k == c.val.testBit 0) = false
      rw [ha,he,v];decide
  have hL : RepReads.forcedL (lit b) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro a
    let c := lc j (b a j)
    obtain ⟨_,e,_,hfalse⟩ := colBoth c
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,c,by simp [c],e,hfalse⟩
  have hR : RepReads.forcedR (lit b) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro c
    obtain ⟨a,_,htrue,_⟩ := colBoth c
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,htrue,rowMiss a⟩
  obtain ⟨u,x,ne,matchJ⟩ := sharedValue hr j b
  obtain ⟨w,uw,xw⟩ := litSep inj u x ne
  let v := lc j (b u j)
  have uv : lit b u v=true := by simp [v]
  have xv : lit b x v=true := by simp [v,matchJ]
  obtain ⟨_,y,_,no⟩ := colBoth v
  have z := RepPath.path r (2*h) t (lit b) u x v w uv uw xv xw (rowMiss u) ⟨y,no⟩ rep
  change (RepReads.forcedL (lit b)).card + (RepReads.forcedR (lit b)).card ≤ t at z
  simpa only [hL,hR,Finset.card_univ,Fintype.card_fin] using z

end PEqualNP.Outside.L_meta_25500_aux



namespace PEqualNP.Outside.L_meta_25500_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

private structure Choice500 {m k : Nat} (bit : Fin m → Fin k → Bool) (s : Nat) where
  r : Nat
  h : Nat
  t : Nat
  row : Fin r → Fin m
  coord : Fin h → Fin k
  ri : Function.Injective row
  ci : Function.Injective coord
  bi : Function.Injective (fun a j => bit (row a) (coord j))
  rmin : 2 ≤ r
  hmin : 2 ≤ h
  rmax : r ≤ m
  rep : RepSizeAtMost (lit (fun a j => bit (row a) (coord j))) t
  ledger : t + 2*(m-r) ≤ s

private theorem split500 {r h t : Nat} {b : Fin r → Fin h → Bool} (hr : 3≤r)
    (inj : Function.Injective b) (rep : RepSizeAtMost (lit b) t) :
    (∃ (q : Nat) (e : Fin q → Fin r) (t' : Nat), q+1=r ∧
      Function.Injective e ∧ t'+2≤t ∧ RepSizeAtMost (lit (fun a j => b (e a) j)) t') ∨
    (∃ C : Circuit, Monotone2 C ∧ C.size ≤ t ∧ ReadsBack (r+2*h) C ∧
      Represents (lit b) C ∧ OnlyRowOr (r:=r) C) := by
  cases r with
  | zero => omega
  | succ n =>
    rcases PEqualNP.Outside.L_meta_25491 n (2*h) t (lit b) (by omega) (litSep inj) rep with
      ⟨u,t',ht',rp⟩|alt
    · exact .inl ⟨n,u.succAbove,t',rfl,Fin.succAbove_right_injective,ht',rp⟩
    · exact .inr alt

theorem extract500
    (pairBound : ∀ {r h t : Nat} (b : Fin r → Fin h → Bool), r=2 → 2≤h →
      Function.Injective b → RepSizeAtMost (lit b) t → 4≤t)
    (trim : ∀ {r h t : Nat} (b : Fin r → Fin h → Bool), 3≤r → 2≤h →
      Function.Injective b → RepSizeAtMost (lit b) t →
      ¬(∀ j, ∃ u v, b u j=false ∧ b v j=true) →
      ∃ (q : Nat) (e : Fin q → Fin h), 2≤q ∧ q<h ∧ Function.Injective e ∧
        Function.Injective (fun a j => b a (e j)) ∧
        RepSizeAtMost (lit (fun a j => b a (e j))) t)
    (allBound : ∀ {r h t : Nat} (b : Fin r → Fin h → Bool), 3≤r → 2≤h →
      Function.Injective b → (∀ j, ∃ u v, b u j=false ∧ b v j=true) →
      RepSizeAtMost (lit b) t → r+2*h≤t)
    {k m s : Nat} (bit : Fin m → Fin k → Bool) (hk : 2≤k) (hm : 2≤m)
    (hin : Function.Injective bit) (hs : RepSizeAtMost (lit bit) s) (hlt : s<2*m) :
    ∃ (r h : Nat) (row : Fin r → Fin m) (coord : Fin h → Fin k) (D : Circuit),
      let b := fun a j => bit (row a) (coord j)
      Function.Injective row ∧ Function.Injective coord ∧ Function.Injective b ∧
      2≤h ∧ 2*h<r ∧ (∀ j, ∃ u v, b u j=false ∧ b v j=true) ∧
      Monotone2 D ∧ ReadsBack (r+2*h) D ∧ Represents (lit b) D ∧
      D.size+2*(m-r)≤s ∧ D.size<2*r ∧ OnlyRowOr (r:=r) D := by
  classical
  let initial : Choice500 bit s := ⟨m,k,s,id,id,fun _ _ e => e,fun _ _ e => e, hin,
    hm,hk,le_rfl,hs,by simp⟩
  let P := fun d => ∃ A : Choice500 bit s, A.r+A.h=d
  have hp : ∃ d, P d := ⟨m+k,initial,rfl⟩
  obtain ⟨A,ha⟩ := Nat.find_spec hp
  have least (B : Choice500 bit s) : A.r+A.h ≤ B.r+B.h := by
    rw [ha]
    exact Nat.find_min' hp ⟨B,rfl⟩
  let b := fun a j => bit (A.row a) (A.coord j)
  have small : A.t < 2*A.r := by
    have := A.ledger
    have := A.rmax
    omega
  have three : 3≤A.r := by
    by_contra hn
    have e : A.r=2 := by have := A.rmin;omega
    have := pairBound b e A.hmin A.bi A.rep
    omega
  have full : ∀ j, ∃ u v, b u j=false ∧ b v j=true := by
    by_contra hn
    obtain ⟨q,e,hq,lt,ie,ie',rp⟩ := trim b three A.hmin A.bi A.rep hn
    let B : Choice500 bit s := ⟨A.r,q,A.t,A.row,A.coord ∘ e,A.ri,A.ci.comp ie,ie',
      A.rmin,hq,A.rmax,rp,A.ledger⟩
    have bad := least B
    change A.r+A.h≤A.r+q at bad
    omega
  have many : 2*A.h < A.r := by
    have := allBound b three A.hmin A.bi full A.rep
    omega
  rcases split500 three A.bi A.rep with ⟨q,e,t',qe,ie,save,rp⟩|⟨D,mon,ds,rb,rep,form⟩
  · let B : Choice500 bit s := ⟨q,A.h,t',A.row ∘ e,A.coord,A.ri.comp ie,A.ci,A.bi.comp ie,
      by omega,A.hmin,by have := A.rmax;omega,rp,by have := A.rmax;have := A.ledger;omega⟩
    have bad := least B
    change A.r+A.h≤q+A.h at bad
    omega
  · exact ⟨A.r,A.h,A.row,A.coord,D,A.ri,A.ci,A.bi,A.hmin,many,full,mon,rb,rep,
      by have := A.ledger;omega,by omega,form⟩

end PEqualNP.Outside.L_meta_25500_aux


open PEqualNP.Outside.L_meta_25500_aux in
theorem PEqualNP.Outside.L_meta_25500 : ∀ (k m s : ℕ) (name : Fin m → Fin (2 ^ k)),
  let bit := fun (a : Fin m) (j : Fin k) => (name a).val.testBit j.val
  let literals {r h : ℕ} (b : Fin r → Fin h → Bool)
      (x : Fin r) (c : Fin (2 * h)) :=
    b x ⟨c.val / 2, (Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ 1)).2
      (lt_of_lt_of_eq c.isLt (Nat.mul_comm 2 h))⟩ == c.val.testBit 0
  2 ≤ k → 2 ≤ m → Function.Injective name →
  PEqualNP.Represents.RepSizeAtMost (literals bit) s → s < 2 * m →
  ∃ (r h : ℕ) (row : Fin r → Fin m) (coord : Fin h → Fin k)
      (D : PEqualNP.CircuitLowerBounds.Circuit),
    let b := fun a' j' => bit (row a') (coord j')
    Function.Injective row ∧ Function.Injective coord ∧ Function.Injective b ∧
    2 ≤ h ∧ 2 * h < r ∧
    (∀ i, ∃ u v, b u i = false ∧ b v i = true) ∧
    PEqualNP.MetaComplexity.Monotone2 D ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (r + 2 * h) D ∧
    PEqualNP.Represents.Represents (literals b) D ∧
    D.size + 2 * (m - r) ≤ s ∧ D.size < 2 * r ∧
    ∀ u : Fin r,
      PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) u.val = 1 ∧
      ∃ (j : Fin D.gates.length) (w : ℕ),
        (D.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        ((D.gates.get j).inputs = [u.val, w] ∨ (D.gates.get j).inputs = [w, u.val]) := by
  intro k m s name
  dsimp only
  intro hk hm hn hs small
  exact extract500 pairBound500 trim500 allBound500 (fun a j => (name a).val.testBit j.val)
    hk hm (nameBitsInj hn) hs small
