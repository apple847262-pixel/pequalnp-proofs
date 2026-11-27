import PEqualNP.Defs


namespace PEqualNP.Outside.L_clb_044_aux.Builder
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

abbrev BitFn (n : Nat) := (Fin n → Bool) → Bool

structure Bank (n : Nat) where
  gates : List Gate
  fan : FanInTwo ⟨gates,0⟩
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

def empty (n : Nat) : Bank n := ⟨[],by simp [FanInTwo],by simp [ReadsBack]⟩

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
    (ok : g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2)
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

lemma inv {B : Bank n} {f : BitFn n} (a : B.Has f) :
    B.Grow 1 (fun D => D.Has (fun x => !(f x))) := by
  obtain ⟨i,hi,he⟩ := a
  simpa [GateOp.eval,he] using B.gate ⟨.not,[i]⟩ (by simp) (by simpa using hi)

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

lemma collect {α : Type} (B : Bank n) (l : List α) (f : α → BitFn n) (cost : Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i ∈ l, D.Grow cost (fun E => E.Has (f i))) :
    B.Grow (l.length*cost) (fun D => ∀ i ∈ l, D.Has (f i)) := by
  induction l with
  | nil => simpa using (Grow.pure B (p:=fun D => ∀ i ∈ ([] : List α), D.Has (f i)) (by simp))
  | cons a l ih =>
    have t := ih (fun D e i hi => emit D e i (by simp [hi]))
    have out := t.bind (b:=cost) (q:=fun E => ∀ i ∈ a::l, E.Has (f i)) (by
      intro D e haveL
      obtain ⟨E,e',c',ha⟩ := emit D e a (by simp)
      refine ⟨E,e',c',?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | h
      · exact ha
      · exact e' (haveL i h))
    simpa [Nat.succ_mul] using out

lemma collectFin (B : Bank n) (m : Nat) (f : Fin m → BitFn n) (cost : Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i, D.Grow cost (fun E => E.Has (f i))) :
    B.Grow (m*cost) (fun D => ∀ i, D.Has (f i)) := by
  simpa using B.collect (List.finRange m) f cost (fun D e i _ => emit D e i)

lemma finish {f : BitFn n} {b : Nat} (h : (empty n).Grow b (fun B => B.Has f)) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack n C ∧ C.size ≤ b ∧
      ∀ bits, C.eval (List.ofFn bits) = f bits := by
  obtain ⟨B,_,budget,i,_,he⟩ := h
  exact ⟨⟨B.gates,i⟩, B.fan, B.back, by simpa [Circuit.size, empty] using budget, he⟩

end Bank
end PEqualNP.Outside.L_clb_044_aux.Builder


namespace PEqualNP.Outside.L_clb_044_aux
open PEqualNP.Outside.L_clb_044_aux.Builder

abbrev Guard (n : Nat) := Nat → BitFn n
abbrev State (d : Nat) := Fin (2^d)

def pattern {d : Nat} (s : State d) (bit : Bool) := s.val + (if bit then 2^d else 0)

lemma pattern_lt {d : Nat} (s : State d) (bit : Bool) : pattern s bit < 2^(d+1) := by
  have := s.isLt
  cases bit <;> simp [pattern,Nat.pow_succ] <;> omega

lemma pattern_mod {d : Nat} (s : State d) (bit : Bool) : pattern s bit % 2^d = s.val := by
  cases bit <;> simp [pattern,Nat.mod_eq_of_lt s.isLt]

lemma find_pattern {d w : Nat} (s : State d) (hm : w%2^d = s.val) :
    ∃ bit, pattern s bit = w%2^(d+1) := by
  rw [Nat.mod_pow_succ,hm]
  by_cases z : (w/2^d)%2=0
  · exact ⟨false,by simp [pattern,z]⟩
  · have o : (w/2^d)%2=1 := by omega
    exact ⟨true,by simp [pattern,o]⟩

def succState {d : Nat} (s : State d) (bit : Bool) : State d :=
  ⟨pattern s bit/2, by have := pattern_lt s bit; rw [Nat.pow_succ] at this; omega⟩

def active {n d : Nat} : List (Guard n) → State d → BitFn n
  | [],_ => fun _ => true
  | g::gs,s => fun x => (g (pattern s false) x && active gs (succState s false) x) ||
                          (g (pattern s true) x && active gs (succState s true) x)

def valid {n} (d : Nat) (gs : List (Guard n)) (w : Nat) (x : Fin n → Bool) : Prop :=
  ∀ i : Fin gs.length, gs[i.val] ((w/2^i.val)%2^(d+1)) x=true

lemma valid_cons {n d w : Nat} (g : Guard n) (gs : List (Guard n)) (x) :
    valid d (g::gs) w x ↔ g (w%2^(d+1)) x=true ∧ valid d gs (w/2) x := by
  have shift (i : Nat) : (w/2)/2^i = w/2^(i+1) := by
    rw [Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm 2]
  constructor
  · intro h
    refine ⟨by simpa using h ⟨0,by simp⟩,?_⟩
    intro j
    simpa [shift] using h ⟨j.val+1,by simp⟩
  · rintro ⟨a,b⟩ ⟨i,hi⟩
    cases i with
    | zero => simpa using a
    | succ i =>
      have h := b ⟨i,by simp at hi;omega⟩
      simpa [shift] using h

theorem active_iff {n d : Nat} (gs : List (Guard n)) (s : State d) (x) :
    active gs s x=true ↔ ∃ w : Fin (2^(gs.length+d)), w.val % 2^d=s.val ∧ valid d gs w.val x := by
  induction gs generalizing s with
  | nil =>
    constructor
    · intro _
      refine ⟨⟨s.val,by simp⟩,Nat.mod_eq_of_lt s.isLt,?_⟩
      intro i
      exact Fin.elim0 i
    · intro _; rfl
  | cons g gs ih =>
    have bridge : active (g::gs) s x=true ↔
        ∃ bit : Bool, g (pattern s bit) x=true ∧ active gs (succState s bit) x=true := by
      simp only [active,Bool.or_eq_true,Bool.and_eq_true]
      constructor
      · rintro (h|h)
        · exact ⟨false,h⟩
        · exact ⟨true,h⟩
      · rintro ⟨b,h⟩
        cases b
        · exact Or.inl h
        · exact Or.inr h
    rw [bridge]
    have bound : 2^((g::gs).length+d) = 2^(gs.length+d)*2 := by
      rw [List.length_cons,Nat.succ_add,Nat.pow_succ]
    constructor
    · rintro ⟨bit,hg,ht⟩
      obtain ⟨v,hv,good⟩ := (ih (succState s bit)).mp ht
      let p := pattern s bit
      let w := v.val*2+p%2
      change v.val % 2^d=p/2 at hv
      have div : w/2=v.val := by dsimp [w];omega
      have rem : w%2=p%2 := by dsimp [w];omega
      have full : w%2^(d+1) = p := by
        rw [Nat.pow_succ,Nat.mul_comm (2^d) 2,Nat.mod_mul,div,rem,hv]
        omega
      refine ⟨⟨w,by rw [bound];have := v.isLt;dsimp [w];omega⟩,?_,?_⟩
      · have q := congrArg (fun a => a%2^d) full
        simpa [Nat.pow_succ,p,pattern_mod] using q
      · apply (valid_cons g gs x).mpr
        exact ⟨by rwa [full],by rwa [div]⟩
    · rintro ⟨w,hs,hw⟩
      obtain ⟨bit,hb⟩ := find_pattern s hs
      obtain ⟨hg,ht⟩ := (valid_cons g gs x).mp hw
      refine ⟨bit,by rwa [hb],(ih _).mpr ⟨⟨w.val/2,by have := w.isLt;omega⟩,?_,ht⟩⟩
      change w.val/2%2^d = pattern s bit/2
      rw [hb,Nat.pow_succ,Nat.mod_mul_left_div_self]

end PEqualNP.Outside.L_clb_044_aux

namespace PEqualNP.Outside.L_clb_044_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_clb_044_aux.Builder
open PEqualNP.Outside.L_clb_044_aux.Builder.Bank

private abbrev Good (g : Gate) :=
  g.op ∈ ({GateOp.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private lemma keepOne {n} {B : Bank n} {f : BitFn n} (h : B.Has f) :
    B.Grow 1 (fun D => D.Has f) := ⟨B,fun x => x,by omega,h⟩

private lemma copyOne {n} (B : Bank n) (g : Gate) (good : Good g) (f : Nat → BitFn n)
    (hf : ∀ i, B.Has (f i)) :
    B.Grow 1 (fun D => D.Has (fun x => g.op.eval (g.inputs.map (fun i => f i x)))) := by
  obtain ⟨op,r⟩ := g
  obtain ⟨hop,hlen⟩ := good
  change op ∈ ({GateOp.and,.or,.not} : Set GateOp) at hop
  change r.length ≤ 2 at hlen
  change B.Grow 1 (fun D => D.Has (fun x => op.eval (r.map (fun i => f i x))))
  rcases r with _ | ⟨i, _ | ⟨j,_ | ⟨z,l⟩⟩⟩
  · rcases hop with h|h|h
    · rw [show op=.and from h]; exact B.const true
    · rw [show op=.or from h]; exact B.const false
    · rw [show op=.not from h]; exact B.const true
  · rcases hop with h|h|h
    · rw [show op=.and from h]; simpa [GateOp.eval] using keepOne (hf i)
    · rw [show op=.or from h]; simpa [GateOp.eval] using keepOne (hf i)
    · rw [show op=.not from h]; exact inv (hf i)
  · rcases hop with h|h|h
    · rw [show op=.and from h]; simpa [GateOp.eval] using meet (hf i) (hf j)
    · rw [show op=.or from h]; simpa [GateOp.eval] using join (hf i) (hf j)
    · rw [show op=.not from h]; exact inv (hf i)
  · simp at hlen

private def wire {n : Nat} (gs : List Gate) (i : Nat) (x : Fin n → Bool) : Bool :=
  ((⟨gs,0⟩ : Circuit).wires (List.ofFn x)).getD i false

private lemma copyLength (gs : List Gate) (x : List Bool) :
    ((⟨gs,0⟩ : Circuit).wires x).length = x.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp [Circuit.wires,List.foldl_append] at ih ⊢
    omega

private lemma wirePush {n : Nat} (gs : List Gate) (g : Gate) (j : Nat) (x : Fin n → Bool) :
    wire (gs++[g]) j x =
      if j<n+gs.length then wire gs j x else if j=n+gs.length then
        g.op.eval (g.inputs.map (fun i=>wire gs i x)) else false := by
  let ws := (⟨gs,0⟩ : Circuit).wires (List.ofFn x)
  let b := g.op.eval (g.inputs.map (fun i=>wire gs i x))
  have hl : ws.length=n+gs.length := by simp [ws,copyLength]
  have he : wire (gs++[g]) j x = (ws++[b]).getD j false := by
    simp [wire,ws,b,Circuit.wires,List.foldl_append]
  rw [he]
  split_ifs with a a
  · rw [List.getD_append _ _ _ _ (by omega)];rfl
  · rw [← hl] at a
    subst j
    simp [b]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

lemma copyGuard {n : Nat} (B : Bank n) (C : Circuit) (hf : FanInTwo C) (_hr : ReadsBack n C)
    (ins : ∀ j : Fin n, B.Has (fun x => x j)) (zero : B.Has (fun _ => false)) :
    B.Grow C.size (fun D => D.Has (fun x => C.eval (List.ofFn x))) := by
  have make (gs : List Gate) (good : ∀ g ∈ gs, Good g) :
      B.Grow gs.length (fun D => ∀ i, D.Has (wire gs i)) := by
    induction gs using List.reverseRecOn with
    | nil =>
      apply Grow.pure
      intro i
      by_cases hi : i<n
      · have eqn : @wire n [] i = (fun x => x ⟨i,hi⟩) := by
          funext x
          simp [wire,Circuit.wires,List.getD_eq_getElem?_getD,hi]
        rw [eqn]; exact ins ⟨i,hi⟩
      · have eqn : @wire n [] i = (fun _ => false) := by
          funext x
          simp [wire,Circuit.wires,List.getD_eq_getElem?_getD,hi]
        rw [eqn]; exact zero
    | append_singleton gs g ih =>
      obtain ⟨D,e,c,h⟩ := ih (fun z hz => good z (by simp [hz]))
      obtain ⟨E,f,d,t⟩ := copyOne D g (good g (by simp)) (wire gs) h
      refine ⟨E,fun a=>f (e a),by simp;omega,?_⟩
      intro j
      by_cases hl : j<n+gs.length
      · have eqn : @wire n (gs++[g]) j = wire gs j := by
          funext x; simp [wirePush,hl]
        rw [eqn]; exact f (h j)
      · by_cases hj : j=n+gs.length
        · have eqn : @wire n (gs++[g]) j = (fun x=>g.op.eval (g.inputs.map fun i=>wire gs i x)) := by
            funext x; simp [wirePush,hj]
          rw [eqn]; exact t
        · have eqn : @wire n (gs++[g]) j = (fun _ => false) := by
            funext x; simp [wirePush,hl,hj]
          rw [eqn]; exact f (e zero)
  obtain ⟨D,e,c,h⟩ := make C.gates hf
  exact ⟨D,e,c,h C.output⟩

end PEqualNP.Outside.L_clb_044_aux

namespace PEqualNP.Outside.L_clb_044_aux
open PEqualNP.Outside.L_clb_044_aux.Builder
open Bank

def Available {n : Nat} (d b : Nat) (B : Bank n) (g : Guard n) : Prop :=
  ∀ D : Bank n, B.Ext D → ∀ p<2^(d+1), D.Grow b (fun E => E.Has (g p))

lemma dpBuild {n : Nat} (B : Bank n) (d b : Nat) (gs : List (Guard n))
    (available : ∀ g ∈ gs, Available d b B g) (one : B.Has (fun _ => true)) :
    B.Grow (gs.length * (2^d*(2*b+3))) (fun E => ∀ s : State d,E.Has (active gs s)) := by
  induction gs with
  | nil =>
    simpa [active] using (Grow.pure B (p:=fun E => ∀ _ : State d,E.Has (fun _ => true)) (fun _=>one))
  | cons g gs ih =>
    obtain ⟨D,e,de,tail⟩ := ih (fun z hz => available z (by simp [hz]))
    have ag := available g (by simp)
    have emit (F : Bank n) (f : D.Ext F) (s : State d) :
        F.Grow (2*b+3) (fun E => E.Has (active (g::gs) s)) := by
      obtain ⟨G,j,fg,z⟩ := ag F (fun h=>f (e h)) _ (pattern_lt s false)
      obtain ⟨H,m,gh,o⟩ := ag G (fun h=>j (f (e h))) _ (pattern_lt s true)
      obtain ⟨K,k,hk,z'⟩ := meet (m z) (m (j (f (tail (succState s false)))))
      obtain ⟨L,l,kl,o'⟩ := meet (k o) (k (m (j (f (tail (succState s true))))))
      obtain ⟨M,a,lm,ans⟩ := join (l z') o'
      exact ⟨M,fun h=>a (l (k (m (j h)))),by omega,ans⟩
    obtain ⟨E,f,ef,yes⟩ := D.collectFin (2^d) (fun s => active (g::gs) s) (2*b+3) emit
    exact ⟨E,fun h => f (e h),by rw [List.length_cons,Nat.succ_mul];omega,yes⟩

private lemma orBits {n : Nat} {α : Type} {B : Bank n} (l : List α) (f : α → BitFn n)
    (zero : B.Has (fun _ => false)) (hf : ∀ i ∈ l,B.Has (f i)) :
    B.Grow l.length (fun D => D.Has (fun x=>l.any (fun i=>f i x))) := by
  induction l with
  | nil => simpa using Grow.pure B zero
  | cons a l ih =>
    have h := ih (fun i hi => hf i (by simp [hi]))
    simpa using h.bind (b:=1) (fun _ e v => join (e (hf a (by simp))) v)

lemma finishDP {n : Nat} (d b : Nat) (gs : List (Guard n))
    (ag : ∀ B : Bank n, (∀ i : Fin n,B.Has (fun x=>x i)) → B.Has (fun _=>false) →
      ∀ g ∈ gs, Available d b B g) :
    (Bank.empty n).Grow (2^d * (gs.length*(2*b+3)+1)+2)
      (fun D=>D.Has (fun x=>(List.finRange (2^d)).any (fun s=>active gs s x))) := by
  obtain ⟨B,e,eb,zero⟩ := Bank.const (Bank.empty n) false
  obtain ⟨D,f,bd,one⟩ := Bank.const B true
  obtain ⟨E,m,de,ans⟩ := dpBuild D d b gs (ag D (fun i=>f (e (Bank.input i))) (f zero)) one
  obtain ⟨F,j,ef,last⟩ := orBits (List.finRange (2^d)) (active gs) (m (f zero)) (fun s _=>ans s)
  refine ⟨F,fun h=>j (m (f (e h))),?_,last⟩
  simp only [List.length_finRange] at ef
  have eq : 2^d*(gs.length*(2*b+3)+1)=gs.length*(2^d*(2*b+3))+2^d := by ring
  rw [eq]
  omega

end PEqualNP.Outside.L_clb_044_aux


open PEqualNP.Outside.L_clb_044_aux PEqualNP.Outside.L_clb_044_aux.Builder in
theorem PEqualNP.Outside.L_clb_044 : ∀ (n t d b : Nat)
  (guard : Fin t → Nat → (Fin n → Bool) → Bool),
  (∀ (i : Fin t) (pattern : Nat), pattern < 2 ^ (d + 1) →
    ∃ G : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo G ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack n G ∧
      G.size ≤ b ∧
      ∀ x : Fin n → Bool, G.eval (List.ofFn x) = guard i pattern x) →
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
    C.size ≤ 2 ^ d * (t * (2 * b + 3) + 1) + 2 ∧
    ∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ word : Fin (2 ^ (t + d)), ∀ i : Fin t,
        guard i ((word.val / 2 ^ i.val) % 2 ^ (d + 1)) x = true) := by
  intro n t d b guard hypothesis
  let gs := List.ofFn guard
  have len : gs.length=t := List.length_ofFn
  have grown := finishDP d b gs (by
    intro B ins zero g hg D ext p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    obtain ⟨C,hf,hr,sz,correct⟩ := hypothesis i p hp
    apply (copyGuard D C hf hr (fun j=>ext (ins j)) (ext zero)).weaken sz
    intro E h
    simpa only [correct] using h)
  obtain ⟨C,hf,hr,sz,correct⟩ := Bank.finish grown
  refine ⟨C,hf,hr,by simpa only [len] using sz,?_⟩
  intro x
  rw [correct,List.any_eq_true]
  have matchGuard (w : Nat) : valid d gs w x ↔
      ∀ i : Fin t, guard i ((w/2^i.val)%2^(d+1)) x=true := by
    constructor
    · intro h i
      simpa [gs] using h ⟨i.val,by simp [gs]⟩
    · intro h i
      simpa [gs] using h ⟨i.val,by simpa only [←len] using i.isLt⟩
  constructor
  · rintro ⟨s,_,act⟩
    obtain ⟨w,_,hw⟩ := (active_iff gs s x).mp act
    exact ⟨⟨w.val,lt_of_lt_of_eq w.isLt (congrArg (fun l => 2^(l+d)) len)⟩,(matchGuard _).mp hw⟩
  · rintro ⟨w,hw⟩
    let s : State d := ⟨w.val % 2^d,Nat.mod_lt _ (by positivity)⟩
    exact ⟨s,List.mem_finRange _,(active_iff gs s x).mpr
      ⟨⟨w.val,lt_of_lt_of_eq w.isLt (congrArg (fun l => 2^(l+d)) len.symm)⟩,rfl,(matchGuard _).mpr hw⟩⟩
