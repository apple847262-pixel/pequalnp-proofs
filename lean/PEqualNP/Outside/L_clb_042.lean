import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_042_aux.Builder
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

abbrev BitFn (n : Nat) := (Fin n → Bool) → Bool

structure Bank (n : Nat) where
  gates : List Gate
  fan : Monotone2 ⟨gates,0⟩
  back : ReadsBack n ⟨gates,0⟩

namespace Bank
variable {n : Nat}

def val (B : Bank n) (i : Nat) (x : Fin n → Bool) : Bool :=
  ((⟨B.gates,0⟩ : Circuit).wires (List.ofFn x)).getD i false

def Has (B : Bank n) (f : BitFn n) : Prop :=
  ∃ i < n + B.gates.length, ∀ x, B.val i x = f x

def Ext (B D : Bank n) : Prop := ∀ {f}, B.Has f → D.Has f

def Grow (B : Bank n) (cost : Nat) (p : Bank n → Prop) : Prop :=
  ∃ D, B.Ext D ∧ D.gates.length ≤ B.gates.length + cost ∧ p D

def empty (n : Nat) : Bank n := ⟨[],by simp [Monotone2],by simp [ReadsBack]⟩

lemma input (i : Fin n) : (empty n).Has (fun x => x i) := by
  refine ⟨i,i.isLt,?_⟩
  intro x
  simp [val,empty,Circuit.wires,List.getD_eq_getElem?_getD,i.isLt]

lemma Grow.pure (B : Bank n) {p : Bank n → Prop} (h : p B) : B.Grow 0 p :=
  ⟨B,fun h => h,by omega,h⟩

lemma Grow.weaken {B : Bank n} {p q : Bank n → Prop} {a b : Nat} (h : B.Grow a p)
    (hab : a ≤ b) (hpq : ∀ D, p D → q D) : B.Grow b q := by
  obtain ⟨D,e,c,t⟩ := h
  exact ⟨D,e,by omega,hpq D t⟩

lemma Grow.bind {B : Bank n} {p q : Bank n → Prop} {a b : Nat} (h : B.Grow a p)
    (f : ∀ D, B.Ext D → p D → D.Grow b q) : B.Grow (a+b) q := by
  obtain ⟨D,e,c,t⟩ := h
  obtain ⟨E,e',c',t'⟩ := f D e t
  exact ⟨E,fun h => e' (e h),by omega,t'⟩

private lemma wireLen (gs : List Gate) (x : List Bool) :
    ((⟨gs,0⟩ : Circuit).wires x).length = x.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp [Circuit.wires,List.foldl_append] at ih ⊢
    omega

private lemma gate (B : Bank n) (g : Gate)
    (ok : g.op ∈ ({GateOp.and, .or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (back : ∀ i ∈ g.inputs, i < n+B.gates.length) :
    B.Grow 1 (fun D => D.Has (fun x => g.op.eval (g.inputs.map fun i => B.val i x))) := by
  let D : Bank n :=
    { gates := B.gates ++ [g]
      fan := by
        intro g' h
        change g' ∈ B.gates ++ [g] at h
        rcases List.mem_append.mp h with h|h
        · exact B.fan g' h
        · simpa using (show g' = g from List.mem_singleton.mp h) ▸ ok
      back := by
        intro j hj w hw
        change j < (B.gates ++ [g]).length at hj
        change w ∈ ((B.gates ++ [g]).getD j _).inputs at hw
        by_cases h : j < B.gates.length
        · rw [List.getD_append _ _ _ _ h] at hw
          exact B.back j h w hw
        · have he : j = B.gates.length := by simp at hj; omega
          subst j
          simp at hw
          exact back w hw }
  have hv (x : Fin n → Bool) :
      ((⟨D.gates,0⟩ : Circuit).wires (List.ofFn x)) =
        ((⟨B.gates,0⟩ : Circuit).wires (List.ofFn x)) ++
        [g.op.eval (g.inputs.map fun i => B.val i x)] := by
    simp [D,val,Circuit.wires,List.foldl_append]
  have hl (x : Fin n → Bool) :
      ((⟨B.gates,0⟩ : Circuit).wires (List.ofFn x)).length = n+B.gates.length := by
    simp [wireLen]
  refine ⟨D,?_,by simp [D],n+B.gates.length,by simp [D],?_⟩
  · intro f hf
    obtain ⟨i,hi,he⟩ := hf
    refine ⟨i,by simp [D]; omega,?_⟩
    intro x
    unfold val
    rw [hv,List.getD_append _ _ _ _ (by rw [hl]; exact hi)]
    exact he x
  · intro x
    unfold val
    rw [hv,← hl x]
    simp [val,List.getD_eq_getElem?_getD]

lemma const (B : Bank n) (b : Bool) : B.Grow 1 (fun D => D.Has (fun _ => b)) := by
  cases b with
  | false => simpa [GateOp.eval] using B.gate ⟨.or,[]⟩ (by simp) (by simp)
  | true => simpa [GateOp.eval] using B.gate ⟨.and,[]⟩ (by simp) (by simp)

lemma meet {B : Bank n} {f g : BitFn n} (a : B.Has f) (b : B.Has g) :
    B.Grow 1 (fun D => D.Has (fun x => f x && g x)) := by
  obtain ⟨i,hi,he⟩ := a
  obtain ⟨j,hj,hf⟩ := b
  simpa [GateOp.eval,he,hf] using B.gate ⟨.and,[i,j]⟩ (by simp) (by simp [hi,hj])

lemma join {B : Bank n} {f g : BitFn n} (a : B.Has f) (b : B.Has g) :
    B.Grow 1 (fun D => D.Has (fun x => f x || g x)) := by
  obtain ⟨i,hi,he⟩ := a
  obtain ⟨j,hj,hf⟩ := b
  simpa [GateOp.eval,he,hf] using B.gate ⟨.or,[i,j]⟩ (by simp) (by simp [hi,hj])

lemma finish {f : BitFn n} {b : Nat} (h : (empty n).Grow b (fun B => B.Has f)) :
    ∃ C : Circuit, Monotone2 C ∧ ReadsBack n C ∧ C.size ≤ b ∧
      ∀ bits, C.eval (List.ofFn bits) = f bits := by
  obtain ⟨B,_,budget,i,_,he⟩ := h
  exact ⟨⟨B.gates,i⟩, B.fan, B.back, by simpa [Circuit.size, empty] using budget, he⟩

end Bank
end PEqualNP.Outside.L_clb_042_aux.Builder
namespace PEqualNP.Outside.L_clb_042_aux
abbrev Q (w : Nat) := Fin (2^w)
abbrev I (n w : Nat) := n*2^(w+1)
def edgeCode (w : Nat) (s : Q w) (b : Bool) := s.val + b.toNat * 2^w
lemma edgeLt (w : Nat) (s : Q w) (b : Bool) : edgeCode w s b < 2^(w+1) := by
  have := s.isLt; cases b <;> simp [edgeCode,Nat.pow_succ] <;> omega
def next (w : Nat) (s : Q w) (b : Bool) : Q w :=
  ⟨edgeCode w s b / 2,by have := edgeLt w s b;rw [Nat.pow_succ] at this;omega⟩
def addr {n} (w : Nat) (i : Fin n) (s : Q w) (b : Bool) : Fin (I n w) :=
  ⟨i.val*2^(w+1)+edgeCode w s b,by
    have h := Nat.mul_le_mul_right (2^(w+1)) (show i.val+1≤n from i.isLt)
    rw [Nat.add_mul,Nat.one_mul] at h
    have := edgeLt w s b;unfold I;omega⟩
def allow (w n : Nat) (i : Fin n) (s : Q w) (b : Bool) (x : Fin (I n w)→Bool) := x (addr w i s b)
end PEqualNP.Outside.L_clb_042_aux

namespace PEqualNP.Outside.L_clb_042_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_clb_042_aux.Builder
def tableBits {n w : Nat} (hn : 0<n) (table : Fin n → (Fin (w+1)→Bool) → Bool) (j : Fin (I n w)) :=
  table ⟨(j.val/2^(w+1))%n,Nat.mod_lt _ hn⟩ (fun r => j.val.testBit r.val)
lemma allowBits {n w : Nat} (hn : 0<n) (table : Fin n → (Fin (w+1)→Bool) → Bool)
    (i : Fin n) (s : Q w) (b : Bool) : allow w n i s b (tableBits hn table) =
      table i (fun j => (edgeCode w s b).testBit j.val) := by
  let a := addr w i s b
  have div : a.val / 2^(w+1) = i.val := by
    dsimp [a,addr]; rw [Nat.mul_comm i.val,Nat.mul_add_div (by positivity),Nat.div_eq_of_lt (edgeLt ..),Nat.add_zero]
  have rem : a.val % 2^(w+1) = edgeCode w s b := by
    dsimp [a,addr]; rw [Nat.mul_comm i.val,Nat.mul_add_mod,Nat.mod_eq_of_lt (edgeLt ..)]
  have ei : (⟨(a.val/2^(w+1))%n,Nat.mod_lt _ hn⟩ : Fin n)=i := Fin.ext (by change (a.val/2^(w+1))%n=i.val;rw [div,Nat.mod_eq_of_lt i.isLt])
  change table ⟨(a.val/2^(w+1))%n,_⟩ (fun j=>a.val.testBit j.val) = _
  rw [ei]
  apply congrArg (table i)
  funext j;rw [←rem,Nat.testBit_mod_two_pow];simp [j.isLt]
end PEqualNP.Outside.L_clb_042_aux


namespace PEqualNP.Outside.L_clb_042_aux

open PEqualNP.Outside.L_clb_042_aux.Builder
open PEqualNP.Outside.L_clb_042_aux.Builder.Bank

def revAllow (w n : Nat) (x : Fin (I n w) → Bool) (d : Nat) (s : Q w) (b : Bool) : Bool :=
  if h : d<n then allow w n ⟨n-(d+1),by omega⟩ s b x else false

def suffix (w n : Nat) (x : Fin (I n w) → Bool) : Nat → Q w → Q w → Bool
  | 0, a, s => decide (s = a)
  | d+1, a, s =>
    (revAllow w n x d s false && suffix w n x d a (next w s false)) ||
    (revAllow w n x d s true && suffix w n x d a (next w s true))

def zeroBranch (w n : Nat) (x : Fin (I n w) → Bool) (d : Nat) (a s : Q w) : Bool :=
  revAllow w n x d s false && suffix w n x d a (next w s false)

lemma revAllow_eq {w n d} (x : Fin (I n w) → Bool) (hd : d<n) (s : Q w) (b : Bool) :
    revAllow w n x d s b = allow w n ⟨n-(d+1),by omega⟩ s b x := dite_eq_left hd

lemma suffix_succ {w n d} (x : Fin (I n w) → Bool) (a s : Q w) :
    suffix w n x (d+1) a s = (zeroBranch w n x d a s ||
        (revAllow w n x d s true && suffix w n x d a (next w s true))) := rfl

def BackWires (w n d : Nat) (B : Bank (I n w)) : Prop :=
  (∀ b : Bool, B.Has (fun _ => b)) ∧
  (∀ a s : Q w, B.Has (fun x => suffix w n x d a s)) ∧
  ∀ j<d, ∀ a s : Q w, B.Has (fun x => zeroBranch w n x j a s)

private lemma collectB {m : Nat} {α : Type} (B : Bank m) (l : List α) (cost : Nat)
    (P : α → Bank m → Prop) (up : ∀ i {D E : Bank m}, D.Ext E → P i D → P i E)
    (step : ∀ D : Bank m, B.Ext D → ∀ i ∈ l, D.Grow cost (P i)) :
    B.Grow (l.length*cost) (fun E => ∀ i ∈ l, P i E) := by
  induction l with
  | nil => simpa using (Grow.pure B (p:=fun E => ∀ i ∈ ([] : List α), P i E) (by simp))
  | cons a l ih =>
    have h := ih (fun D e i hi => step D e i (by simp [hi]))
    obtain ⟨D,e,c,p⟩ := h
    obtain ⟨E,f,g,q⟩ := step D e a (by simp)
    refine ⟨E,fun v => f (e v),?_,?_⟩
    · simp [Nat.succ_mul]; omega
    · intro i hi
      rcases List.mem_cons.mp hi with rfl|ht
      · exact q
      · exact up i f (p i ht)

private lemma produceLayer {w n d : Nat} {D : Bank (I n w)} (hd : d<n)
    (inp : (Bank.empty (I n w)).Ext D) (old : BackWires w n d D) :
    D.Grow (3*(2^w)*(2^w)) (BackWires w n (d+1)) := by
  let P := fun (a s : Q w) (E : Bank (I n w)) =>
    E.Has (fun x => zeroBranch w n x d a s) ∧ E.Has (fun x => suffix w n x (d+1) a s)
  have single (E : Bank (I n w)) (ext : D.Ext E) (a s : Q w) : E.Grow 3 (P a s) := by
    have edge (b : Bool) : E.Has (fun x => revAllow w n x d s b) := by
      simpa only [revAllow_eq _ hd,allow] using ext (inp (Bank.input (addr w ⟨n-(d+1),by omega⟩ s b)))
    obtain ⟨F,f,c,k0⟩ := meet (edge false) (ext (old.2.1 a (next w s false)))
    obtain ⟨G,g,h,k1⟩ := meet (f (edge true)) (f (ext (old.2.1 a (next w s true))))
    obtain ⟨H,j,o,hs⟩ := join (g k0) k1
    exact ⟨H,fun t=>j (g (f t)),by omega,j (g k0),hs⟩
  have up (a s : Q w) {E F : Bank (I n w)} (e : E.Ext F) (h : P a s E) : P a s F :=
    ⟨e h.1,e h.2⟩
  let states := List.finRange (2^w)
  have row (E : Bank (I n w)) (e : D.Ext E) (a : Q w) :
      E.Grow (states.length*3) (fun F => ∀ s ∈ states, P a s F) :=
    collectB E states 3 (P a) (up a) (fun F f s _ => single F (fun h => f (e h)) a s)
  let R := fun a (E : Bank (I n w)) => ∀ s ∈ states, P a s E
  obtain ⟨E,e,c,h⟩ := collectB D states (states.length*3) R
    (fun a _ _ f v s hs => up a s f (v s hs)) (fun F f a _ => row F f a)
  have pair (a s : Q w) := h a (List.mem_finRange a) s (List.mem_finRange s)
  refine ⟨E,e,?_,fun b => e (old.1 b),fun a s => (pair a s).2,?_⟩
  · simpa [states,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using c
  · intro j hj a s
    by_cases hdj : j=d
    · subst j; exact (pair a s).1
    · exact e (old.2.2 j (by omega) a s)

lemma backward (w n d : Nat) (hd : d≤n) :
    (Bank.empty (I n w)).Grow (3*d*(2^w)*(2^w)+2) (BackWires w n d) := by
  let B := Bank.empty (I n w)
  induction d with
  | zero =>
    obtain ⟨D,e,a,hf⟩ := B.const false
    obtain ⟨E,f,c,ht⟩ := D.const true
    have v (b : Bool) : E.Has (fun _ => b) := by cases b <;> first | exact f hf | exact ht
    refine ⟨E,fun h=>f (e h),?_,v,fun a s=>v (decide (s=a)),?_⟩
    · change E.gates.length ≤ B.gates.length + _
      simp; omega
    · intro j hj;omega
  | succ d ih =>
    obtain ⟨D,e,c,t⟩ := ih (by omega)
    obtain ⟨E,f,h,p⟩ := produceLayer (show d<n by omega) e t
    refine ⟨E,fun a=>f (e a),?_,p⟩
    rw [show 3*(d+1)*(2^w)*(2^w)+2 = (3*d*(2^w)*(2^w)+2) + 3*(2^w)*(2^w) by ring]
    omega

end PEqualNP.Outside.L_clb_042_aux

namespace PEqualNP.Outside.L_clb_042_aux
def chooseBit {w n} (x : Fin (I n w)→Bool) (a : Q w) (t : Nat) (s : Q w) :=
  !zeroBranch w n x (n-(t+1)) a s
def trace {w n} (x : Fin (I n w)→Bool) (a : Q w) : Nat → Q w
  | 0 => a
  | t+1 => let s := trace x a t; next w s (chooseBit x a t s)
abbrev label {w n} (x : Fin (I n w)→Bool) (a : Q w) (t : Nat) := chooseBit x a t (trace x a t)
lemma greedyStep {w n t} (x : Fin (I n w) → Bool) (a s : Q w) (ht : t<n)
    (ok : suffix w n x (n-t) a s = true) :
    allow w n ⟨t,ht⟩ s (chooseBit x a t s) x = true ∧
    suffix w n x (n-(t+1)) a (next w s (chooseBit x a t s)) = true := by
  let d := n-(t+1)
  have dl : d<n := by dsimp[d];omega
  have eqn : n-t=d+1 := by dsimp[d];omega
  rw [eqn] at ok
  change (zeroBranch w n x d a s || (revAllow w n x d s true && suffix w n x d a (next w s true))) = true at ok
  have rev (b : Bool) : revAllow w n x d s b = allow w n ⟨t,ht⟩ s b x := by
    rw [revAllow_eq x dl]
    congr 2;dsimp [d];omega
  change allow w n ⟨t,ht⟩ s (!(zeroBranch w n x d a s)) x = true ∧
    suffix w n x d a (next w s (!(zeroBranch w n x d a s)))=true
  cases e : zeroBranch w n x d a s
  · simp only [e,Bool.false_or,Bool.and_eq_true] at ok
    simpa only [Bool.not_false,←rev] using ok
  · have h : revAllow w n x d s false=true ∧ suffix w n x d a (next w s false)=true := Bool.and_eq_true_iff.mp e
    simpa only [Bool.not_true,←rev] using h
lemma traceSuffix {w n} (x : Fin (I n w)→Bool) (a : Q w) (h : suffix w n x n a a=true) :
    ∀ t≤n, suffix w n x (n-t) a (trace x a t) = true := by
  intro t;induction t with
  | zero => intro _;simpa [trace] using h
  | succ t ih =>
    intro ht
    exact (greedyStep x a (trace x a t) (by omega) (ih (by omega))).2
lemma traceCloses {w n} (x : Fin (I n w)→Bool) (a : Q w) (h : suffix w n x n a a=true) : trace x a n = a := by
  have ht := traceSuffix x a h n (le_refl n)
  simpa [suffix] using ht
lemma tableSteps {w n} (x : Fin (I n w)→Bool) (a : Q w) (h : suffix w n x n a a=true) {t : Nat} (ht : t<n) :
    allow w n ⟨t,ht⟩ (trace x a t) (label x a t) x = true :=
  (greedyStep x a (trace x a t) ht (traceSuffix x a h t (by omega))).1
lemma walkSuffix {w n} (x : Fin (I n w)→Bool) (q : Nat→Q w) (a : Nat→Bool) (closed : q n=q 0)
    (move : ∀ t<n,q (t+1)=next w (q t) (a t)) (ok : ∀ t (ht:t<n), allow w n ⟨t,ht⟩ (q t) (a t) x = true) :
    suffix w n x n (q 0) (q 0) = true := by
  have backInd : ∀d≤n,suffix w n x d (q 0) (q (n-d))=true := by
    intro d;induction d with
    | zero => intro _;simpa [suffix] using closed
    | succ d ih =>
      intro dd;let t := n-(d+1)
      have ht : t<n := by dsimp[t];omega
      have hn : n-d=t+1 := by dsimp[t];omega
      have he := ok t ht; have later:=ih (by omega)
      rw [hn,move t ht] at later
      have here : revAllow w n x d (q t) (a t)=true := by simpa [revAllow,show d<n by omega,t] using he
      change ((revAllow w n x d (q t) false && suffix w n x d (q 0) (next w (q t) false)) || (revAllow w n x d (q t) true && suffix w n x d (q 0) (next w (q t) true)))=true
      cases hy : a t <;> rw [hy] at here later <;> simp [here,later]
  simpa using backInd n (le_refl n)
end PEqualNP.Outside.L_clb_042_aux




namespace PEqualNP.Outside.L_clb_042_aux.Cyclic

lemma lowBit {w : Nat} (s : Q w) (a : Bool) {j : Nat} (hj : j < w) :
    (edgeCode w s a).testBit j = s.val.testBit j := by
  unfold edgeCode
  rw [Nat.add_comm, Nat.mul_comm, Nat.testBit_two_pow_mul_add _ s.isLt, ite_eq_left hj]

lemma highBit {w : Nat} (s : Q w) (a : Bool) :
    (edgeCode w s a).testBit w = a := by
  unfold edgeCode
  rw [Nat.add_comm, Nat.mul_comm, Nat.testBit_two_pow_mul_add _ s.isLt]
  cases a <;> simp

def readTime {n w : Nat} (_hn : 0 < n) (q : Nat → Q w) (a : Nat → Bool)
    (t j : Nat) := (edgeCode w (q (t % n)) (a (t % n))).testBit j

lemma cyclicStep {n w : Nat} (hn : 0 < n) (q : Nat → Q w) (a : Nat → Bool)
    (close : q n = q 0) (step : ∀ t < n, q (t+1) = next w (q t) (a t))
    (t j : Nat) (hj : j < w) :
    readTime hn q a t (j+1) = readTime hn q a (t+1) j := by
  have ht := Nat.mod_lt t hn
  have qstep : q ((t+1)%n) = next w (q (t%n)) (a (t%n)) := by
    rw [←Nat.mod_add_mod t n 1]
    by_cases h : t%n+1<n
    · rw [Nat.mod_eq_of_lt h,step _ ht]
    · have eq : t%n+1=n := by omega
      rw [eq,Nat.mod_self]
      exact close.symm.trans ((congrArg q eq.symm).trans (step _ ht))
  unfold readTime
  rw [lowBit _ _ hj, qstep]
  exact Nat.testBit_add_one .. 

lemma shiftWindow {n w : Nat} (hn : 0 < n) (q : Nat → Q w) (a : Nat → Bool)
    (close : q n = q 0) (step : ∀ t < n, q (t+1) = next w (q t) (a t))
    (t j : Nat) (hj : j ≤ w) :
    readTime hn q a t j = readTime hn q a (t+j) 0 := by
  induction j generalizing t with
  | zero => simp
  | succ j ih =>
    rw [cyclicStep hn q a close step t j (by omega), ih (t+1) (by omega)]
    congr 1; omega

lemma recoveredTime {n w : Nat} (hn : 0 < n) (q : Nat → Q w) (a : Nat → Bool)
    (close : q n = q 0) (step : ∀ t < n, q (t+1) = next w (q t) (a t))
    (p : Nat) :
    a ((p%n+n-w%n)%n) = readTime hn q a p 0 := by
  let t := p%n+n-w%n
  have shift := shiftWindow hn q a close step t w (by omega)
  change (edgeCode w _ _).testBit w = _ at shift
  rw [highBit] at shift
  have hmod : (t+w)%n=p%n := by
    calc
      (t+w)%n = (t+w%n)%n := by simp
      _ = (p%n+n)%n := by
        congr 1
        dsimp [t]
        have := Nat.mod_lt w hn
        omega
      _ = p%n := by simp
  change a (t%n) = _
  rw [shift]
  unfold readTime
  rw [hmod]

theorem validPicked {n w : Nat} (hn : 0 < n)
    {table : Fin n → (Fin (w+1) → Bool) → Bool}
    (q : Nat → Q w) (a : Nat → Bool) (close : q n = q 0)
    (step : ∀ t < n, q (t+1) = next w (q t) (a t))
    (ok : ∀ t (ht:t<n), table ⟨t,ht⟩ (fun j => (edgeCode w (q t) (a t)).testBit j.val) = true) :
    ∀ i : Fin n, table i (fun j =>
      a ((((i.val+j.val)%n)+n-w%n)%n)) = true := by
  intro i
  have good := ok i.val i.isLt
  convert good using 2
  funext j
  rw [recoveredTime hn q a close step (i.val+j.val),
    ←shiftWindow hn q a close step i.val j.val (by omega)]
  simp [readTime,Nat.mod_eq_of_lt i.isLt]

def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | w+1 => 2^w * (f w).toNat + pack f w

lemma packLt (f : Nat → Bool) (w : Nat) : pack f w < 2^w := by
  induction w with
  | zero => simp [pack]
  | succ w ih => cases hb : f w <;> simp [pack,hb,Nat.pow_succ] <;> omega

lemma packBit (f : Nat → Bool) {w j : Nat} (hj : j < w) : (pack f w).testBit j = f j := by
  induction w with
  | zero => omega
  | succ w ih =>
    rw [pack, Nat.testBit_two_pow_mul_add _ (packLt f w)]
    by_cases h : j < w
    · simp [h,ih h]
    · have : j=w := by omega
      subst j
      cases f w <;> simp

def stream {n : Nat} (hn : 0 < n) (word : Fin n → Bool) (t j : Nat) : Bool :=
  word ⟨(t+j)%n,Nat.mod_lt _ hn⟩

def state {n : Nat} (hn : 0 < n) (word : Fin n → Bool) (w t : Nat) : Q w :=
  ⟨pack (stream hn word t) w,packLt ..⟩

lemma edgeWindow {n w : Nat} (hn : 0 < n) (word : Fin n → Bool) (t j : Nat) (hj : j ≤ w) :
    (edgeCode w (state hn word w t) (stream hn word t w)).testBit j = stream hn word t j := by
  by_cases h : j<w
  · rw [lowBit _ _ h]
    exact packBit _ h
  · have : j=w := by omega
    subst j
    exact highBit ..

lemma stateStep {n w : Nat} (hn : 0 < n) (word : Fin n → Bool) (t : Nat) :
    state hn word w (t+1) = next w (state hn word w t) (stream hn word t w) := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases h : j < w
  · change (pack _ w).testBit j = (edgeCode .. / 2).testBit j
    rw [packBit _ h,Nat.testBit_div_two, edgeWindow hn word _ _ (by omega)]
    unfold stream
    congr 3; omega
  · have hbound : 2^w ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (state hn word w (t+1)).isLt hbound),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (next w (state hn word w t) (stream hn word t w)).isLt hbound)]

theorem wordWalk {n w : Nat} (hn : 0 < n)
    {table : Fin n → (Fin (w+1) → Bool) → Bool} (word : Fin n → Bool)
    (ok : ∀ i : Fin n, table i (fun j => word ⟨(i.val + j.val)%n,Nat.mod_lt _ hn⟩) = true) :
    ∃ (q : Nat → Q w) (a : Nat → Bool), q n = q 0 ∧
      (∀ t < n, q (t+1) = next w (q t) (a t)) ∧
      (∀ t (ht:t<n), table ⟨t,ht⟩ (fun j => (edgeCode w (q t) (a t)).testBit j.val) = true) := by
  refine ⟨state hn word w, fun t => stream hn word t w, ?_, fun t _ => stateStep hn word t, ?_⟩
  · have per : stream hn word n = stream hn word 0 := by funext j; simp [stream]
    apply Fin.ext
    exact congrArg (fun f => pack f w) per
  · intro t ht
    have eq : (fun j : Fin (w+1) => (edgeCode w (state hn word w t) (stream hn word t w)).testBit j.val)
        = fun j => word ⟨(t+j.val)%n,Nat.mod_lt _ hn⟩ := by
      funext j
      exact edgeWindow hn word t j.val (by omega)
    rw [eq]
    exact ok ⟨t,ht⟩

end PEqualNP.Outside.L_clb_042_aux.Cyclic

namespace PEqualNP.Outside.L_clb_042_aux
open PEqualNP.Outside.L_clb_042_aux.Builder
open Bank PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
private lemma anyReuse {I : Nat} {α : Type} {B : Bank I} (l : List α) (f : α → BitFn I)
    (zero : B.Has (fun _ => false)) (haveF : ∀ i ∈ l, B.Has (f i)) :
    B.Grow l.length (fun E => E.Has (fun x => l.any (fun i => f i x))) := by
  induction l with
  | nil => simpa using Grow.pure B zero
  | cons a l ih =>
    have pre := ih (fun i hi => haveF i (by simp [hi]))
    simpa using pre.bind (b:=1) (fun D e h => join (e (haveF a (by simp))) h)


def answer (n w : Nat) (x : Fin (I n w) → Bool) :=
  (List.finRange (2^w)).any (fun a => suffix w n x n a a)

lemma decideCircuit (n w : Nat) :
    ∃ C : Circuit, Monotone2 C ∧ ReadsBack (I n w) C ∧
      C.size ≤ 3*n*4^w+2^w+2 ∧ ∀ x, C.eval (List.ofFn x) = answer n w x := by
  apply Bank.finish
  obtain ⟨B,e,c,h⟩ := backward w n n (le_refl _)
  obtain ⟨D,f,g,k⟩ := anyReuse (B:=B) (List.finRange (2^w))
    (fun a x => suffix w n x n a a) (h.1 false) (fun a _=>h.2.1 a a)
  refine ⟨D,fun z => f (e z),?_,k⟩
  simp only [List.length_finRange] at g
  rw [show 3*n*4^w+2^w+2=3*n*(2^w)*(2^w)+2+2^w by rw [show 4^w=(2^w)*(2^w) by rw [←Nat.mul_pow]];ring]
  omega

lemma answer_iff {n w} (hn : 0<n) (table : Fin n → (Fin (w+1)→Bool)→Bool) :
    answer n w (tableBits hn table)=true ↔ ∃ word : Fin n→Bool,
      ∀ i : Fin n, table i (fun j => word ⟨(i.val+j.val)%n,Nat.mod_lt _ hn⟩)=true := by
  let x:=tableBits hn table
  constructor
  · intro yes
    obtain ⟨a,_,ok⟩ := List.any_eq_true.mp yes
    let q:=trace x a
    let b:=label x a
    refine ⟨fun p=>b ((p.val+n-w%n)%n),Cyclic.validPicked (w:=w) hn q b (traceCloses x a ok) (fun _ _=>rfl) ?_⟩
    intro t ht
    exact (allowBits hn table ⟨t,ht⟩ (q t) (b t)).symm.trans (tableSteps x a ok ht)
  · rintro ⟨word,ok⟩
    obtain ⟨q,b,closed,step,legal⟩:=Cyclic.wordWalk hn word ok
    apply List.any_eq_true.mpr
    refine ⟨q 0,List.mem_finRange _,walkSuffix x q b closed step ?_⟩
    intro t ht
    exact (allowBits hn table _ _ _).trans (legal t ht)

end PEqualNP.Outside.L_clb_042_aux
open PEqualNP.Outside.L_clb_042_aux in
theorem PEqualNP.Outside.L_clb_042 : ∀ (n w : ℕ) (hn : 0 < n),
  let I := n * 2 ^ (w + 1)
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧
    C.size ≤ 3 * n * 4 ^ w + 2 ^ w + 2 ∧
    ∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let inputs := List.ofFn (fun j : Fin I =>
        table ⟨(j.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
          (fun bit => j.val.testBit bit.val))
      C.eval inputs = true ↔
        ∃ word : Fin n → Bool, ∀ i : Fin n,
          table i (fun bit => word ⟨(i.val + bit.val) % n, Nat.mod_lt _ hn⟩) = true := by
  intro n w hn
  obtain ⟨C,m,b,c,h⟩ := decideCircuit n w
  refine ⟨C,m,b,c,?_⟩
  intro table
  change C.eval (List.ofFn (tableBits hn table))=true ↔ _
  rw [h]
  exact answer_iff hn table
