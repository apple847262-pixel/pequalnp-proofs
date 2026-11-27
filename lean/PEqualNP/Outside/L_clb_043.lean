import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_043_aux.Builder
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

lemma xor2 {B : Bank n} {f g : BitFn n} (a : B.Has f) (b : B.Has g) :
    B.Grow 4 (fun D => D.Has (fun x => xor (f x) (g x))) := by
  apply (meet a b).bind (b := 3)
  intro C e hab
  apply (inv hab).bind (b := 2)
  intro D e' hn
  apply (join (e' (e a)) (e' (e b))).bind (b := 1)
  intro E e'' hor
  apply (meet hor (e'' hn)).weaken (le_refl _)
  intro F h
  have eq (x) : ((f x || g x) && !(f x && g x)) = xor (f x) (g x) := by
    cases f x <;> cases g x <;> decide
  simpa only [eq] using h

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
end PEqualNP.Outside.L_clb_043_aux.Builder

namespace PEqualNP.Outside.L_clb_043_aux.Route043
open PEqualNP.Outside.L_clb_043_aux.Builder
open Bank

abbrev Matrix (I S : Nat) := Fin S → Fin S → BitFn I
abbrev Known {I S} (B : Bank I) (A : Matrix I S) := ∀ u s, B.Has (A u s)

def move {I S} (A Z : Matrix I S) (u s : Fin S) (b : Bool) : BitFn I :=
  fun x => A u s x && (if b then !(Z u s x) else Z u s x)

def advance {I S} (src : Fin S → Bool → Fin S) (lab : Fin S → Bool → Bool)
    (A Z : Matrix I S) : Matrix I S :=
  fun u t x => move A Z u (src t false) (lab t false) x || move A Z u (src t true) (lab t true) x

def allPairs (S : Nat) : List (Fin S × Fin S) :=
  List.ofFn (fun i : Fin (S*S) => finProdFinEquiv.symm i)

private lemma pair_mem {S : Nat} (p : Fin S × Fin S) : p ∈ allPairs S := by
  exact List.mem_ofFn.mpr ⟨finProdFinEquiv p,finProdFinEquiv.symm_apply_apply p⟩

def emit {I S} (A Z : Matrix I S) : BitFn I :=
  fun x => (allPairs S).any (fun p => move A Z p.1 p.2 true x)

lemma emit_iff {I S} (A Z : Matrix I S) (x) :
    emit A Z x = true ↔ ∃ u s, move A Z u s true x = true := by
  constructor
  · intro h
    obtain ⟨⟨u,s⟩,_,hm⟩ := List.any_eq_true.mp h
    exact ⟨u,s,hm⟩
  · rintro ⟨u,s,h⟩
    exact List.any_eq_true.mpr ⟨(u,s),pair_mem _,h⟩

def acts {I S} (src : Fin S → Bool → Fin S) (lab : Fin S → Bool → Bool)
    (init : Matrix I S) (can0 : Nat → Matrix I S) : Nat → Matrix I S
  | 0 => init
  | t+1 => advance src lab (acts src lab init can0 t) (can0 t)

def flags {I S} (src : Fin S → Bool → Fin S) (lab : Fin S → Bool → Bool)
    (init : Matrix I S) (can0 : Nat → Matrix I S) (t : Nat) : BitFn I :=
  emit (acts src lab init can0 t) (can0 t)

private lemma collectPairs {I S c : Nat} (B : Bank I) (M : Matrix I S)
    (build : ∀ D : Bank I, B.Ext D → ∀ u s, D.Grow c (fun E => E.Has (M u s))) :
    B.Grow (S*S*c) (fun E => Known E M) := by
  have h := B.collect (allPairs S) (fun p => M p.1 p.2) c
    (fun D e p _ => build D e p.1 p.2)
  apply h.weaken (by simp [allPairs])
  exact fun E v u s => v (u,s) (pair_mem _)

private lemma anyReuse {I : Nat} {α : Type} {B : Bank I} (l : List α) (f : α → BitFn I)
    (zero : B.Has (fun _ => false)) (haveF : ∀ i ∈ l, B.Has (f i)) :
    B.Grow l.length (fun E => E.Has (fun x => l.any (fun i => f i x))) := by
  induction l with
  | nil => simpa using Grow.pure B zero
  | cons a l ih =>
    have pre := ih (fun i hi => haveF i (by simp [hi]))
    simpa using pre.bind (b:=1) (fun D e h => join (e (haveF a (by simp))) h)

lemma routeStep {I S} (B : Bank I) (src : Fin S → Bool → Fin S) (lab : Fin S → Bool → Bool)
    (A Z : Matrix I S) (ha : Known B A) (hz : Known B Z) (zer : B.Has (fun _ => false)) :
    B.Grow (5*(S*S)) (fun E => Known E (advance src lab A Z) ∧ E.Has (emit A Z)) := by
  let nz : Matrix I S := fun u s x => !(Z u s x)
  obtain ⟨D,e,de,hn⟩ := collectPairs (c:=1) B nz (fun _ ef u s => inv (ef (hz u s)))
  obtain ⟨F,f,df,h0⟩ := collectPairs (c:=1) D (fun u s => move A Z u s false)
    (fun _ ef u s => meet (ef (e (ha u s))) (ef (e (hz u s))))
  obtain ⟨G,g,fg,h1⟩ := collectPairs (c:=1) F (fun u s => move A Z u s true)
    (fun _ ef u s => meet (ef (f (e (ha u s)))) (ef (f (hn u s))))
  have hmove (u s) (b : Bool) : G.Has (move A Z u s b) := by
    cases b
    · exact g (h0 u s)
    · exact h1 u s
  obtain ⟨H,m,gh,hA⟩ := collectPairs (c:=1) G (advance src lab A Z) (fun _ ef u t =>
    join (ef (hmove u (src t false) (lab t false))) (ef (hmove u (src t true) (lab t true))))
  obtain ⟨J,j,hj,flag⟩ := anyReuse (B:=H) (allPairs S) (fun p => move A Z p.1 p.2 true)
    (m (g (f (e zer)))) (fun p _ => m (h1 p.1 p.2))
  simp only [allPairs,List.length_ofFn] at hj
  exact ⟨J,fun h=>j (m (g (f (e h)))),by omega,fun u s=>j (hA u s),flag⟩

lemma routeAll {I S} (B : Bank I) (src : Fin S → Bool → Fin S) (lab : Fin S → Bool → Bool)
    (init : Matrix I S) (can0 : Nat → Matrix I S) (n : Nat)
    (hz : ∀ t<n, Known B (can0 t)) (hi : Known B init) (zer : B.Has (fun _ => false)) :
    B.Grow (5*n*(S*S)) (fun E =>
      Known E (acts src lab init can0 n) ∧ ∀ t<n, E.Has (flags src lab init can0 t)) := by
  induction n with
  | zero =>
    simpa [acts] using (Grow.pure B (p:=fun E => Known E init ∧
      ∀ t<0, E.Has (flags src lab init can0 t)) ⟨hi,by simp⟩)
  | succ n ih =>
    obtain ⟨D,e,de,hA,hflags⟩ := ih (fun t ht => hz t (by omega))
    obtain ⟨E,f,df,hN,hb⟩ := routeStep D src lab _ (can0 n) hA
      (fun u s=>e (hz n (by omega) u s)) (e zer)
    refine ⟨E,fun h=>f (e h),?_,hN,?_⟩
    · rw [Nat.mul_succ,Nat.add_mul]
      omega
    · intro t ht
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with lt|rfl
      · exact f (hflags t lt)
      · exact hb

end PEqualNP.Outside.L_clb_043_aux.Route043

namespace PEqualNP.Outside.L_clb_043_aux.Pick043
open PEqualNP.Outside.L_clb_043_aux.Builder
open PEqualNP.Outside.L_clb_043_aux.Builder.Bank
variable {n S : Nat}
def before (d : Fin S → BitFn n) : Nat → BitFn n
  | 0 => fun _ => false
  | i+1 => fun x => before d i x || (if h : i < S then d ⟨i,h⟩ x else false)
def flag (d : Fin S → BitFn n) := before d S
def chosen (d : Fin S → BitFn n) (s : Fin S) : BitFn n :=
  fun x => d s x && !(before d s.val x)

lemma before_iff (d : Fin S → BitFn n) (i : Nat) (x) :
    before d i x = true ↔ ∃ s : Fin S, s.val < i ∧ d s x = true := by
  induction i with
  | zero => simp [before]
  | succ i ih =>
    simp only [before,Bool.or_eq_true,ih]
    constructor
    · rintro (⟨s,hs,e⟩|e)
      · exact ⟨s,by omega,e⟩
      · split at e
        · next h => exact ⟨⟨i,h⟩,by simp,e⟩
        · contradiction
    · rintro ⟨s,hs,e⟩
      by_cases h : s.val < i
      · exact Or.inl ⟨s,h,e⟩
      · have eq : s.val=i := by omega
        subst i
        simpa [s.isLt] using Or.inr e

lemma flag_iff (d : Fin S → BitFn n) (x) : flag d x = true ↔ ∃ s, d s x = true := by
  rw [flag,before_iff]
  exact ⟨fun ⟨s,_,h⟩ => ⟨s,h⟩,fun ⟨s,h⟩ => ⟨s,s.isLt,h⟩⟩

lemma chosen_iff (d : Fin S → BitFn n) (s : Fin S) (x) :
    chosen d s x = true ↔ d s x = true ∧ ∀ j : Fin S, j.val < s.val → d j x = false := by
  simp only [chosen,Bool.and_eq_true,Bool.not_eq_true']
  constructor
  · rintro ⟨hs,hb⟩
    refine ⟨hs,?_⟩
    intro j hj
    cases e : d j x with
    | false => rfl
    | true =>
      have := (before_iff d s.val x).mpr ⟨j,hj,e⟩
      rw [hb] at this
      contradiction
  · rintro ⟨hs,h⟩
    refine ⟨hs,?_⟩
    cases e : before d s.val x with
    | false => rfl
    | true =>
      obtain ⟨j,hj,yes⟩ := (before_iff d s.val x).mp e
      rw [h j hj] at yes
      contradiction

lemma flag_unique (d : Fin S → BitFn n) (x) (h : flag d x = true) :
    ∃! s, chosen d s x = true := by
  classical
  obtain ⟨i,hi⟩ := (flag_iff d x).mp h
  let P := fun j : Nat => ∃ s : Fin S, s.val=j ∧ d s x = true
  have exist : ∃ j, P j := ⟨i.val,i,rfl,hi⟩
  obtain ⟨s,hs,yes⟩ := Nat.find_spec exist
  have chosenS : chosen d s x = true := by
    refine (chosen_iff d s x).mpr ⟨yes,?_⟩
    intro j hj
    cases f : d j x with
    | false => rfl
    | true =>
      have bad := Nat.find_min' exist (show P j.val from ⟨j,rfl,f⟩)
      omega
  refine ⟨s,chosenS,?_⟩
  intro a ha
  have h1 := (chosen_iff d s x).mp chosenS
  have h2 := (chosen_iff d a x).mp ha
  apply Fin.ext
  rcases lt_trichotomy a.val s.val with lt|eq|gt
  · have no := h1.2 a lt; rw [h2.1] at no; contradiction
  · exact eq
  · have no := h2.2 s gt; rw [yes] at no; contradiction

lemma build (B : Bank n) (d : Fin S → BitFn n) (hd : ∀ s, B.Has (d s))
    (hz : B.Has (fun _ => false)) :
    B.Grow (3*S) (fun E => E.Has (flag d) ∧ ∀ s, E.Has (chosen d s)) := by
  have make (i : Nat) (hi : i≤S) :
      B.Grow (3*i) (fun D => D.Has (before d i) ∧ ∀ s : Fin S, s.val < i → D.Has (chosen d s)) := by
    induction i with
    | zero =>
      simpa using Grow.pure B (p:=fun D => D.Has (before d 0) ∧ ∀ s : Fin S, s.val < 0 → D.Has (chosen d s))
        ⟨hz,by simp⟩
    | succ i ih =>
      let a : Fin S := ⟨i,by omega⟩
      rw [Nat.mul_succ]
      apply (ih (by omega)).bind (b:=3)
      intro D e old
      apply (inv old.1).bind (b:=2)
      intro E f no
      apply (meet (f (e (hd a))) no).bind (b:=1)
      intro F g hit
      obtain ⟨G,z,sz,flagged⟩ := join (g (f old.1)) (g (f (e (hd a))))
      refine ⟨G,z,sz,?_,?_⟩
      · have hlt : i < S := by omega
        simpa only [before,dif_pos hlt,a] using flagged
      · intro s hs
        by_cases lt : s.val < i
        · exact z (g (f (old.2 s lt)))
        · have eq : s=a := Fin.ext (by change s.val=i; omega)
          subst s
          exact z hit
  exact (make S (le_refl _)).weaken (le_refl _) (fun E h => ⟨h.1,fun s => h.2 s s.isLt⟩)
end PEqualNP.Outside.L_clb_043_aux.Pick043




namespace PEqualNP.Outside.L_clb_043_aux
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
def incoming (w : Nat) (d : Q w) (side : Bool) := 2*d.val+side.toNat
def invSrc (w : Nat) (d : Q w) (side : Bool) : Q w := ⟨incoming w d side % 2^w,Nat.mod_lt _ (by positivity)⟩
def invLab (w : Nat) (d : Q w) (side : Bool) := decide (2^w ≤ incoming w d side)
lemma distinctIncoming {w} (d : Q w) (side : Bool) :
    edgeCode w (invSrc w d side) (invLab w d side) = incoming w d side := by
  have h := d.isLt
  have lt : incoming w d side < 2^w+2^w := by cases side <;>simp [incoming] <;>omega
  change incoming w d side % 2^w + (decide (2^w ≤ incoming w d side)).toNat * 2^w = _
  by_cases f : incoming w d side < 2^w
  · simp [not_le.mpr f,Nat.mod_eq_of_lt f]
  · have g : 2^w ≤ incoming w d side := by omega
    rw [Nat.mod_eq_sub_mod g,Nat.mod_eq_of_lt (show incoming w d side -2^w<2^w by omega)]
    simp [g]
lemma nextInv {w} (d : Q w) (side : Bool) : next w (invSrc w d side) (invLab w d side) = d := by
  apply Fin.ext;change edgeCode .. / 2 = _; rw [distinctIncoming]; cases side <;> simp [incoming] <;>omega
lemma codeInj {w} {s t : Q w} {a b : Bool} (e : edgeCode w s a=edgeCode w t b) : s=t ∧ a=b := by
  have hs:=s.isLt;have ht:=t.isLt
  cases a <;> cases b <;> simp [edgeCode] at e ⊢ <;> first | exact Fin.ext e | omega | exact Fin.ext (by omega)
lemma incomingIff {w} (s : Q w) (b : Bool) (d : Q w) :
    next w s b=d ↔ ∃ side, s=invSrc w d side ∧ b=invLab w d side := by
  constructor
  · intro e
    have eq : edgeCode w s b / 2 = d.val := congrArg Fin.val e
    let side := decide (edgeCode w s b % 2=1)
    have ec : edgeCode w s b = incoming w d side := by
      unfold incoming side;by_cases hx : edgeCode w s b % 2=1 <;>simp [hx] <;>omega
    exact ⟨side,codeInj (ec.trans (distinctIncoming d side).symm)⟩
  · rintro ⟨s,rfl,rfl⟩;exact nextInv ..
end PEqualNP.Outside.L_clb_043_aux




namespace PEqualNP.Outside.L_clb_043_aux

open PEqualNP.Outside.L_clb_043_aux.Builder
open PEqualNP.Outside.L_clb_043_aux.Builder.Bank

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
    revAllow w n x d s b = allow w n ⟨n-(d+1),by omega⟩ s b x := dif_pos hd

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

end PEqualNP.Outside.L_clb_043_aux

namespace PEqualNP.Outside.L_clb_043_aux
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
end PEqualNP.Outside.L_clb_043_aux



namespace PEqualNP.Outside.L_clb_043_aux
open PEqualNP.Outside.L_clb_043_aux.Builder
abbrev diagF (w n : Nat) (a : Q w) : BitFn (I n w) := fun x => suffix w n x n a a
abbrev flagF (w n : Nat) := Pick043.flag (diagF w n)
def initA (w n : Nat) : Route043.Matrix (I n w) (2^w) :=
  fun u s x => if u=s then Pick043.chosen (diagF w n) u x else false
abbrev zeros (w n t : Nat) : Route043.Matrix (I n w) (2^w) :=
  fun u s x => zeroBranch w n x (n-(t+1)) u s
abbrev active (w n : Nat) := Route043.acts (invSrc w) (invLab w) (initA w n) (zeros w n)
abbrev flagBit (w n : Nat) := Route043.flags (invSrc w) (invLab w) (initA w n) (zeros w n)
private lemma moveIff {m S} (A Z : Route043.Matrix m S) (x : Fin m→Bool) (u s : Fin S) (b : Bool) :
    Route043.move A Z u s b x = true ↔ A u s x=true ∧ b=!(Z u s x) := by
  unfold Route043.move
  cases b <;> cases A u s x <;> cases Z u s x <;> decide
lemma tracks {w n} (x : Fin (I n w)→Bool) {a : Q w}
    (unique : ∀ u : Q w, Pick043.chosen (diagF w n) u x=true ↔ u=a) (t : Nat) :
    ∀ u s, active w n t u s x=true ↔ u=a ∧ s=trace x a t := by
  induction t with
  | zero =>
    intro u s
    change (if u=s then Pick043.chosen (diagF w n) u x else false)=true ↔ u=a ∧ s=a
    by_cases eq : u=s
    · subst s;simp [unique]
    · simp only [if_neg eq,Bool.false_eq_true,false_iff]
      exact fun h=>eq (h.1.trans h.2.symm)
  | succ t ih =>
    intro u s
    change (Route043.move (active w n t) (zeros w n t) u (invSrc w s false) (invLab w s false) x ||
      Route043.move (active w n t) (zeros w n t) u (invSrc w s true) (invLab w s true) x)=true ↔ _
    rw [Bool.or_eq_true,moveIff,moveIff,ih,ih]
    let p := trace x a t
    let L := label x a t
    have one (d : Bool) : ((u=a ∧ invSrc w s d=p) ∧ invLab w s d=!(zeros w n t u (invSrc w s d) x)) ↔
        u=a ∧ p=invSrc w s d ∧ L=invLab w s d := by
      constructor
      · rintro ⟨⟨hu,hp⟩,hl⟩; subst u
        refine ⟨rfl,hp.symm,?_⟩
        change (!(zeros w n t a p x)) = invLab w s d
        rw [←hp]; exact hl.symm
      · rintro ⟨hu,hp,hl⟩; subst u;refine ⟨⟨rfl,hp.symm⟩,?_⟩
        rw [←hp]; exact hl.symm
    rw [one false,one true]
    change _ ↔ u=a ∧ s=next w p L
    constructor
    · rintro (⟨h,p0,l0⟩|⟨h,p1,l1⟩)
      · exact ⟨h,((incomingIff p L s).2 ⟨false,p0,l0⟩).symm⟩
      · exact ⟨h,((incomingIff p L s).2 ⟨true,p1,l1⟩).symm⟩
    · rintro ⟨h,hs⟩
      obtain ⟨b,pb,lb⟩ := (incomingIff p L s).1 hs.symm
      cases b
      · exact .inl ⟨h,pb,lb⟩
      · exact .inr ⟨h,pb,lb⟩
lemma emits {w n} (x : Fin (I n w)→Bool) {a : Q w}
    (unique : ∀ u : Q w, Pick043.chosen (diagF w n) u x=true ↔ u=a) (t : Nat) :
    flagBit w n t x = label x a t := by
  apply Bool.eq_iff_iff.mpr
  rw [flagBit,Route043.flags,Route043.emit_iff]
  constructor
  · rintro ⟨u,s,h⟩
    obtain ⟨activeU,which⟩ := (moveIff ..).1 h
    obtain ⟨rfl,rfl⟩ := (tracks x unique t _ _).1 activeU
    exact which.symm
  · intro h
    exact ⟨a,trace x a t,(moveIff ..).2 ⟨(tracks x unique t _ _).2 ⟨rfl,rfl⟩,h.symm⟩⟩
end PEqualNP.Outside.L_clb_043_aux




namespace PEqualNP.Outside.L_clb_043_aux.Cyclic

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

end PEqualNP.Outside.L_clb_043_aux.Cyclic

namespace PEqualNP.Outside.L_clb_043_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_clb_043_aux.Builder
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
lemma finishMulti {m n : Nat} {p : Bank m} {f : (Fin m → Bool) → Bool}
    {bits : Fin n → (Fin m → Bool) → Bool} (flag : p.Has f) (hs : ∀ i,p.Has (bits i)) :
    ∃ (C : Circuit) (out : Fin n → Fin (m+C.size)), FanInTwo C ∧ ReadsBack m C ∧
      C.output < m+C.size ∧ C.size=p.gates.length ∧ (∀ x,C.eval (List.ofFn x) = f x) ∧
      ∀ i x,(C.wires (List.ofFn x)).getD (out i).val false = bits i x := by
  classical
  obtain ⟨v,hv,h⟩ := flag
  choose ids hi ok using hs
  exact ⟨⟨p.gates,v⟩,fun i => ⟨ids i,hi i⟩,p.fan,p.back,hv,rfl,h,ok⟩
end PEqualNP.Outside.L_clb_043_aux


namespace PEqualNP.Outside.L_clb_043_aux
open PEqualNP.Outside.L_clb_043_aux.Builder
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
def bitOut (w n : Nat) (p : Fin n) := flagBit w n ((p.val+n-w%n)%n)
def WordOK {n w} (hn : 0<n) (table : Fin n → (Fin (w+1)→Bool)→Bool) (f : Fin n→Bool) :=
  ∀ i, table i (fun j => f ⟨(i.val+j.val)%n,Nat.mod_lt _ hn⟩) = true
lemma soundFlag {w n} (hn : 0<n) (table : Fin n → (Fin (w+1)→Bool)→Bool) :
    let x:=tableBits hn table
    (flagF w n x=true ↔ ∃ word,WordOK hn table word) ∧
      (flagF w n x=true → WordOK hn table (fun p => bitOut w n p x)) := by
  let x:=tableBits hn table
  have ens (h : flagF w n x=true) : WordOK hn table (fun p => bitOut w n p x) := by
    obtain ⟨a,yes,alone⟩ := Pick043.flag_unique (diagF w n) x h
    have un (v : Q w) : Pick043.chosen (diagF w n) v x = true ↔ v=a :=
      ⟨alone v,fun e=>e.symm ▸ yes⟩
    have ok := ((Pick043.chosen_iff (diagF w n) a x).1 yes).1
    let q := trace x a
    let b := label x a
    have legal := Cyclic.validPicked (w:=w) hn (table:=table) q b (traceCloses x a ok) (fun _ _=>rfl) (by
      intro t ht
      have he:=tableSteps x a ok ht
      rw [show allow w n ⟨t,ht⟩ (q t) (b t) x = _ from allowBits hn table _ (q t) (b t)] at he
      exact he)
    intro i
    have eq : (fun j : Fin (w+1) => bitOut w n ⟨(i.val+j.val)%n,Nat.mod_lt _ hn⟩ x) =
        (fun j => b ((((i.val+j.val)%n)+n-w%n)%n)) := by
      funext j;exact emits x un _
    rw [eq];exact legal i
  refine ⟨⟨fun y => ⟨_,ens y⟩,?_⟩,ens⟩
  rintro ⟨word,hword⟩
  obtain ⟨q,b,closed,step,legal⟩ := Cyclic.wordWalk hn word hword
  apply (Pick043.flag_iff ..).2; refine ⟨q 0,?_⟩
  apply walkSuffix x q b closed step
  intro t ht
  exact (allowBits hn table _ _ _).trans (legal t ht)
lemma buildAll {n w} (hn : 0<n) :
  ∃ C : Circuit, ∃ out : Fin n → Fin (I n w+C.size),
      FanInTwo C ∧ ReadsBack (I n w) C ∧ C.output < I n w+C.size ∧
      C.size ≤ 8*n*4^w+3*2^w+2 ∧
      (∀ x,C.eval (List.ofFn x)=flagF w n x) ∧
      ∀ p x,(C.wires (List.ofFn x)).getD (out p).val false = bitOut w n p x := by
  obtain ⟨B,_,b,hb⟩ := backward w n n (le_refl _)
  obtain ⟨D,eb,d,hflag,picked⟩ := Pick043.build B (diagF w n) (fun a=>hb.2.1 a a) (hb.1 false)
  have start : Route043.Known D (initA w n) := by
    intro u s;change D.Has (fun x => if u=s then Pick043.chosen (diagF w n) u x else false);by_cases h:u=s
    · simpa only [initA,if_pos h] using picked u
    · simpa only [initA,if_neg h] using eb (hb.1 false)
  obtain ⟨E,ed,e,_,flags⟩ := Route043.routeAll D (invSrc w) (invLab w) _ (zeros w n) n
    (fun t ht a s=>eb (hb.2.2 (n-(t+1)) (by omega) a s)) start (eb (hb.1 false))
  obtain ⟨C,out,fan,rb,bound,cs,cf,co⟩ :=
    finishMulti (ed hflag) (bits:=bitOut w n) (fun p=> flags _ (Nat.mod_lt _ hn))
  refine ⟨C,out,fan,rb,bound,?_,cf,co⟩
  have bb : B.gates.length ≤ 3*n*(2^w)*(2^w)+2 := by simpa [Bank.empty] using b
  have pw : 4^w = (2^w)*(2^w) := by rw [←Nat.mul_pow]
  rw [cs,pw]
  calc
    E.gates.length ≤ (3*n*(2^w)*(2^w)+2)+3*2^w+5*n*(2^w*2^w) := by omega
    _ = _ := by ring
end PEqualNP.Outside.L_clb_043_aux


open PEqualNP.Outside.L_clb_043_aux in
theorem PEqualNP.Outside.L_clb_043 : ∀ (n w : ℕ) (hn : 0 < n),
  let I := n * 2 ^ (w + 1)
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (outBit : Fin n → Fin (I + C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧
    C.output < I + C.size ∧
    C.size ≤ 8 * n * 4 ^ w + 3 * 2 ^ w + 2 ∧
    ∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let inputs := List.ofFn (fun j : Fin I =>
        table ⟨(j.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
          (fun bit => j.val.testBit bit.val))
      let valid := fun word : Fin n → Bool =>
        ∀ i : Fin n,
          table i (fun bit => word ⟨(i.val + bit.val) % n, Nat.mod_lt _ hn⟩) = true
      let picked := fun pos : Fin n => (C.wires inputs).getD (outBit pos).val false
      (C.eval inputs = true ↔ ∃ word, valid word) ∧
      (C.eval inputs = true → valid picked) := by
  intro n w hn
  obtain ⟨C,out,fan,rb,bnd,sz,fl,outs⟩ := buildAll (w:=w) hn
  refine ⟨C,out,fan,rb,bnd,sz,?_⟩
  intro table
  let x := tableBits hn table
  change (C.eval (List.ofFn x)=true ↔ ∃word,WordOK hn table word) ∧
    (C.eval (List.ofFn x)=true → WordOK hn table (fun p => (C.wires (List.ofFn x)).getD (out p).val false))
  rw [fl]
  have eq : (fun p => (C.wires (List.ofFn x)).getD (out p).val false) = (fun p => bitOut w n p x) := funext (fun p => outs p x)
  rw [eq]; exact soundFlag hn table
