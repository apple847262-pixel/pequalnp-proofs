import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25483_aux
abbrev Sig := Int → Bool
def chi (a b c : Bool) := xor a (!b && c)
def linear (x : Sig) (i : Int) := xor (xor (x i) (x (i-2))) (x (i+2))
def sweep (x : Sig) (i : Int) := chi (linear x i) (linear x (i+1)) (linear x (i+2))
def stage (x z v a : Sig) (d : Int) (i : Int) :=
  xor (xor (sweep x i) (xor (z (i-d)) (v (i-d)))) (a i)
def body (z v a b : Sig) :=
  sweep (stage (stage z z v a 1) z v b 4)
def pivot (z v a b c : Sig) (i : Int) := xor (xor (body z v a b i) (v (i-7))) (c i)
lemma pivotLaw (z v a b c : Sig) (i : Int) :
    stage (stage (stage z z v a 1) z v b 4) z v c 7 i = false ↔ z (i-7) = pivot z v a b c i := by
  change xor (xor (body z v a b i) (xor (z (i-7)) (v (i-7)))) (c i) = false ↔ _
  unfold pivot
  cases body z v a b i <;> cases z (i-7) <;> cases v (i-7) <;> cases c i <;> decide
def Agrees (x y : Sig) (lo hi : Int) : Prop := ∀ j, lo ≤ j → j ≤ hi → x j = y j
lemma sweepEq {x y : Sig} {i : Int} (h : Agrees x y (i-2) (i+4)) : sweep x i = sweep y i := by
  have lh (z : Int) (hl : i ≤ z) (hr : z ≤ i+2) : linear x z = linear y z := by
    unfold linear
    rw [h z (by omega) (by omega),h (z-2) (by omega) (by omega),h (z+2) (by omega) (by omega)]
  unfold sweep
  rw [lh i (by omega) (by omega),lh (i+1) (by omega) (by omega),lh (i+2) (by omega) (by omega)]
lemma pivotLocal (z z' v a b c : Sig) (i : Int) (h : Agrees z z' (i-6) (i+12)) :
    pivot z v a b c i = pivot z' v a b c i := by
  have one (j : Int) (hl : i-4 ≤ j) (hr : j ≤ i+8) :
      stage z z v a 1 j = stage z' z' v a 1 j := by
    unfold stage
    rw [sweepEq (x:=z) (y:=z') (i:=j) (fun l jl lj => h l (by omega) (by omega)),h (j-1) (by omega) (by omega)]
  have two (j : Int) (hl : i-2 ≤ j) (hr : j ≤ i+4) :
      stage (stage z z v a 1) z v b 4 j = stage (stage z' z' v a 1) z' v b 4 j := by
    change xor (xor (sweep (stage z z v a 1) j) _) _ = xor (xor (sweep (stage z' z' v a 1) j) _) _
    rw [sweepEq (x:=stage z z v a 1) (y:=stage z' z' v a 1) (i:=j) (fun l jl lj => one l (by omega) (by omega)),h (j-4) (by omega) (by omega)]
  unfold pivot body
  rw [sweepEq (x:=stage (stage z z v a 1) z v b 4) (y:=stage (stage z' z' v a 1) z' v b 4) (i:=i) (fun l hl hr => two l hl hr)]
def rot (k s w : Nat) := ((w <<< (s%k)) ||| (w >>> (k-s%k))) % 2^k
def flipAt (f : Nat → Bool) (i : Nat) := (f i).toNat <<< i
lemma flipBit (f : Nat → Bool) (i j : Nat) :
    (flipAt f i).testBit j = (if j=i then f i else false) := by
  unfold flipAt; rw [Nat.testBit_shiftLeft,Nat.testBit_bool_toNat]
  rcases lt_trichotomy j i with hl|he|hg
  · simp [Nat.not_le.mpr hl,Nat.ne_of_lt hl]
  · simp [he]
  · simp [Nat.le_of_lt hg,show j-i≠0 by omega,Nat.ne_of_gt hg]
lemma packBit (f : Nat → Bool) (l : List Nat) (acc j : Nat) :
  (l.foldl (fun z i => z ||| flipAt f i) acc).testBit j =
    (acc.testBit j || (decide (j∈l) && f j)) := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons,ih,Nat.testBit_or,flipBit]
    by_cases h : j=x
    · subst x; cases e : f j <;> simp [e,Bool.or_assoc]
    · simp [h]
def rawStep (k w : Nat) := (List.range k).foldl (fun z i =>
    z ||| flipAt (fun j => chi (w.testBit j) (w.testBit ((j+1)%k)) (w.testBit ((j+2)%k))) i) 0
lemma stepBit {k j} (h : j<k) (w : Nat) :
    (rawStep k w).testBit j = chi (w.testBit j) (w.testBit ((j+1)%k)) (w.testBit ((j+2)%k)) := by
  simp [rawStep,packBit,h]
lemma rotBit {k j s w : Nat} (h : j<k) (hs : s<k) (hw : w<2^k) :
    (rot k s w).testBit j = w.testBit (if j<s then k-s+j else j-s) := by
  simp only [rot,Nat.mod_eq_of_lt hs,Nat.testBit_mod_two_pow,h,decide_true,Bool.true_and,
    Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_shiftRight]
  by_cases hj : j<s
  · simp [hj,Nat.not_le.mpr hj]
  · have big : w.testBit (k-s+j) = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hj,Nat.le_of_not_gt hj,big]
end PEqualNP.Outside.L_meta_25483_aux

namespace PEqualNP.Outside.L_meta_25483_aux
def idx (k : Nat) (j : Int) := (j % (k : Int)).toNat
def bits (k w : Nat) (j : Int) := w.testBit (idx k j)
lemma idxlt {k : Nat} (kp : 0 < k) (j : Int) : idx k j < k := by
  have h := Int.emod_lt_of_pos j (show (0:Int)<k by omega)
  unfold idx;omega
lemma idxSub {k s : Nat} (hs : s<k) (j : Int) :
    idx k (j-(s:Int)) = if idx k j<s then k-s+idx k j else idx k j-s := by
  have hp : (0:Int)<k := by omega
  have a := Int.emod_nonneg j (ne_of_gt hp)
  have b := Int.emod_lt_of_pos j hp
  unfold idx; rw [← Int.emod_sub_emod j (k:Int) (s:Int)]; split
  · next h =>
    rw [←Int.add_emod_left,Int.emod_eq_of_lt (by omega) (by omega)];omega
  · next h => rw [Int.emod_eq_of_lt (by omega) (by omega)];omega
lemma bitsRot {k s w : Nat} (hs : s<k) (hw : w<2^k) (j : Int) :
    bits k (rot k s w) j = bits k w (j-(s:Int)) := by
  unfold bits;rw [rotBit (idxlt (by omega) _) hs hw,idxSub hs]
lemma idxAdd {k : Nat} (kp : 0<k) (j : Int) (s : Nat) :
    (idx k j+s)%k = idx k (j+(s:Int)) := by
  have a := Int.emod_nonneg j (show (k:Int)≠0 by omega)
  unfold idx
  rw [←Int.emod_add_emod j (k:Int) (s:Int)]
  have eq : (j%(k:Int)+(s:Int)).toNat = (j%(k:Int)).toNat + s := by omega
  rw [@Int.toNat_emod (j%(k:Int)+(s:Int)) (k:Int) (by omega) (by omega),eq]
  rfl
lemma bitsStep {k : Nat} (kp : 0<k) (w : Nat) (j : Int) :
    bits k (rawStep k w) j = chi (bits k w j) (bits k w (j+1)) (bits k w (j+2)) := by
  unfold bits; rw [stepBit (idxlt kp _), idxAdd kp j 1,idxAdd kp j 2]; rfl
lemma bitsXor (k a b : Nat) (j : Int) : bits k (a ^^^ b) j = xor (bits k a j) (bits k b j) := Nat.testBit_xor ..
lemma stepBound (k w : Nat) : rawStep k w < 2^k := by
  have e : rawStep k w % 2^k = rawStep k w := by
    apply Nat.eq_of_testBit_eq; intro i
    by_cases h : i<k
    · simp [Nat.testBit_mod_two_pow,h]
    · simp [Nat.testBit_mod_two_pow,rawStep,packBit,h]
  rw [←e];exact Nat.mod_lt _ (by positivity)
def rawLin (k x : Nat) := x ^^^ rot k 2 x ^^^ rot k (k-2) x
lemma linEq {k x : Nat} (hk : 20≤k) (hx : x<2^k) (j : Int) :
   bits k (rawLin k x) j = linear (bits k x) j := by
  simp only [rawLin,bitsXor,bitsRot (show 2<k by omega) hx,bitsRot (show k-2<k by omega) hx,linear]
  have e : j - ((k-2:Nat):Int) = (j+2) - (k:Int) := by omega
  simp [bits,idx,e]
def rInit (k w v : Nat) := rot k 3 w ^^^ v
lemma injected {k w v d : Nat} (hk : 20≤k) (hw : w<2^k) (hd : d+3<k) (j : Int) :
    bits k (rot k (d+3) w) j = xor (bits k (rInit k w v) (j-d)) (bits k v (j-d)) := by
  simp only [rInit,bitsXor,bitsRot hd hw,bitsRot (show 3<k by omega) hw]
  rw [show j-((d+3:Nat):Int)=(j-d)-3 by omega]
  cases bits k w (j-d-3) <;> cases bits k v (j-d) <;> rfl
def roundN (k w j d x : Nat) := rawStep k (rawLin k x) ^^^ rot k (d+3) w ^^^ (3^(k+j)%2^k)
lemma roundB (k w j d x : Nat) : roundN k w j d x < 2^k :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepBound ..) (Nat.mod_lt _ (by positivity))) (Nat.mod_lt _ (by positivity))
lemma roundEq {k w v r d x : Nat} (hk : 20≤k) (hw : w<2^k) (hd : d+3<k) (hx : x<2^k) :
    bits k (roundN k w r d x) = stage (bits k x) (bits k (rInit k w v)) (bits k v) (bits k (3^(k+r)%2^k)) d := by
  funext i; simp only [roundN,stage,bitsXor,bitsStep (show 0<k by omega),linEq hk hx,injected (v:=v) hk hw hd,sweep]
def rawCol (k w v : Nat) :=
    (List.range 3).foldl (fun x i => rawStep k (rawLin k x) ^^^ rot k (3*(i+1)+1) w ^^^ (3^(k+(3+(i+1)))%2^k)) (rInit k w v)
def ctr (k r : Nat) := bits k (3^(k+r)%2^k)
lemma colPivot {k w v : Nat} (hk : 20≤k) (hw : w<2^k) (hv : v<2^k) (i : Int) :
    bits k (rawCol k w v) i = false ↔ bits k (rInit k w v) (i-7) =
      pivot (bits k (rInit k w v)) (bits k v) (ctr k 4) (ctr k 5) (ctr k 6) i := by
  let z := rInit k w v
  let r1 := roundN k w 4 1 z
  let r2 := roundN k w 5 4 r1
  change bits k (roundN k w 6 7 r2) i = false ↔ _
  have az : z<2^k := Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) hv
  have h1 := roundEq (v:=v) (r:=4) (d:=1) hk hw (by omega) az
  have h2 := roundEq (v:=v) (r:=5) (d:=4) hk hw (by omega) (roundB k w 4 1 z)
  have h3 := roundEq (v:=v) (r:=6) (d:=7) hk hw (by omega) (roundB k w 5 4 r1)
  change bits k (roundN k w 4 1 z) = _ at h1
  change bits k (roundN k w 5 4 r1) = _ at h2
  change bits k (roundN k w 6 7 r2) = _ at h3
  rw [h3]; change stage (bits k (roundN k w 5 4 r1)) _ _ _ _ i = false ↔ _
  rw [h2];change stage (stage (bits k (roundN k w 4 1 z)) _ _ _ _) _ _ _ _ i = false ↔ _
  rw [h1];exact pivotLaw ..
lemma colRank {k w v t : Nat} (hk : 20≤k) (hw : w<2^k) (hv : v<2^k) (ht : t<k) :
    (rawCol k w v).testBit (k-1-t) = false ↔
    (rInit k w v).testBit ((2*k-8-t)%k) =
      pivot (bits k (rInit k w v)) (bits k v) (ctr k 4) (ctr k 5) (ctr k 6) (k-1-(t:Int)) := by
  have eq : idx k ((k:Int)-1-(t:Int)) = k-1-t := by
    unfold idx;rw [Int.emod_eq_of_lt (by omega) (by omega)];omega
  have eq2 : idx k ((k:Int)-1-(t:Int)-7) = (2*k-8-t)%k := by
    unfold idx
    rw [←Int.add_emod_left,Int.toNat_emod (by omega) (by omega)]
    congr 1 <;> omega
  simpa only [bits,eq,eq2] using colPivot hk hw hv ((k:Int)-1-(t:Int))
end PEqualNP.Outside.L_meta_25483_aux

namespace PEqualNP.Outside.L_meta_25483_aux
namespace Builder
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
end Builder
end PEqualNP.Outside.L_meta_25483_aux

namespace PEqualNP.Outside.L_meta_25483_aux.Builder.Bank

variable {n : Nat}

lemma xorConst {B : Bank n} {f : BitFn n} (a : B.Has f) (b : Bool) :
    B.Grow 1 (fun D => D.Has (fun x => xor (f x) b)) := by
  cases b with
  | false =>
    have h := Grow.pure B (p:=fun D => D.Has f) a
    simpa using h.weaken (b:=1) (q:=fun D => D.Has f) (by decide) (fun _ t => t)
  | true => simpa using inv a

private def foldOp (all : Bool) (a b : Bool) : Bool := if all then a && b else a || b

private lemma emitFoldOp {B : Bank n} (all : Bool) {f g : BitFn n}
    (a : B.Has f) (b : B.Has g) :
    B.Grow 1 (fun D => D.Has (fun x => foldOp all (f x) (g x))) := by
  cases all with
  | true => exact meet a b
  | false => exact join a b

private lemma foldSlots {α : Type} (all : Bool) (B : Bank n) (l : List α)
    (f : α → BitFn n) (cost : Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i ∈ l, D.Grow cost (fun E => E.Has (f i))) :
    B.Grow (1+l.length*(cost+1)) (fun D => D.Has (fun x =>
      if all then l.all (fun i => f i x) else l.any (fun i => f i x))) := by
  induction l with
  | nil =>
    simpa using B.const all
  | cons a l ih =>
    have t := ih (fun D e i hi => emit D e i (by simp [hi]))
    have out := t.bind (b:=cost+1)
      (q:=fun E => E.Has (fun x => if all then (a::l).all (fun i => f i x)
        else (a::l).any (fun i => f i x))) (by
      intro D e acc
      apply (emit D e a (by simp)).bind (b:=1)
      intro E e' ha
      have computed := emitFoldOp all ha (e' acc)
      cases all <;> simpa [foldOp] using computed)
    simpa [Nat.succ_mul,Nat.add_assoc] using out

lemma anySlots {α : Type} (B : Bank n) (l : List α) (f : α → BitFn n) (cost : Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i ∈ l, D.Grow cost (fun E => E.Has (f i))) :
    B.Grow (1+l.length*(cost+1))
      (fun D => D.Has (fun x => l.any (fun i => f i x))) :=
  foldSlots false B l f cost emit

lemma allSlots {α : Type} (B : Bank n) (l : List α) (f : α → BitFn n) (cost : Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i ∈ l, D.Grow cost (fun E => E.Has (f i))) :
    B.Grow (1+l.length*(cost+1))
      (fun D => D.Has (fun x => l.all (fun i => f i x))) :=
  foldSlots true B l f cost emit

lemma allBits {α : Type} {B : Bank n} (l : List α) (f : α → BitFn n)
    (h : ∀ i ∈ l, B.Has (f i)) :
    B.Grow (1+l.length) (fun D => D.Has (fun x => l.all (fun i => f i x))) := by
  simpa using allSlots B l f 0 (fun D e i hi => Grow.pure D (e (h i hi)))

lemma anyBits {α : Type} {B : Bank n} (l : List α) (f : α → BitFn n)
    (h : ∀ i ∈ l, B.Has (f i)) :
    B.Grow (1+l.length) (fun D => D.Has (fun x => l.any (fun i => f i x))) := by
  simpa using anySlots B l f 0 (fun D e i hi => Grow.pure D (e (h i hi)))

end PEqualNP.Outside.L_meta_25483_aux.Builder.Bank

namespace PEqualNP.Outside.L_meta_25483_aux
namespace Eval
open Builder Builder.Bank
variable {n k : Nat}

abbrev Word (n : Nat) := (Fin n → Bool) → Nat
def HasWord (k : Nat) (B : Bank n) (W : Word n) : Prop :=
  ∀ j : Int, B.Has (fun x => bits k (W x) j)

lemma idxNat {i : Nat} (h : i<k) : idx k (i : Int) = i := by
  unfold idx
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  rfl

lemma wordLift {B D : Bank n} {W : Word n} (ext : B.Ext D) (h : HasWord k B W) :
    HasWord k D W := fun j => ext (h j)

lemma fromFin {B : Bank n} {W : Word n} (hk : 0<k)
    (h : ∀ i : Fin k, B.Has (fun x => (W x).testBit i.val)) : HasWord k B W :=
  fun j => h ⟨idx k j,idxlt hk j⟩

lemma wordBuild {B : Bank n} {W : Word n} (hk : 0<k) (c : Nat)
    (h : ∀ D : Bank n, B.Ext D → ∀ j:Int, D.Grow c (fun E => E.Has (fun x => bits k (W x) j))) :
    B.Grow (k*c) (fun D => HasWord k D W) := by
  apply (B.collectFin k (fun i x => (W x).testBit i.val) c ?_).weaken (le_refl _)
  · intro D hD; exact fromFin hk hD
  · intro D e i; simpa only [bits,idxNat i.isLt] using h D e i.val

lemma rotated {B : Bank n} {W : Word n} {s : Nat} (h : HasWord k B W) (hs : s<k)
    (hw : ∀x,W x<2^k) : HasWord k B (fun x => rot k s (W x)) := by
  intro j; simpa only [bitsRot hs (hw _)] using h (j-s)

lemma xorWords {B : Bank n} {W V : Word n} (hk : 0<k) (h : HasWord k B W) (v : HasWord k B V) :
    B.Grow (k*4) (fun D => HasWord k D (fun x => W x ^^^ V x)) := by
  apply wordBuild hk
  intro D e j
  simpa only [bitsXor] using xor2 (e (h j)) (e (v j))

lemma chiBit {B : Bank n} {a b c : BitFn n} (ha:B.Has a) (hb:B.Has b) (hc:B.Has c) :
    B.Grow 6 (fun D => D.Has (fun x => chi (a x) (b x) (c x))) := by
  apply (inv hb).bind (b:=5)
  intro D e hnot
  apply (meet hnot (e hc)).bind (b:=4)
  intro E f hh
  exact xor2 (f (e ha)) hh

lemma nonlinear {B : Bank n} {W : Word n} (hk:0<k) (h:HasWord k B W) :
    B.Grow (k*6) (fun D => HasWord k D (fun x => rawStep k (W x))) := by
  apply wordBuild hk
  intro D e j
  simpa only [bitsStep hk] using chiBit (e (h j)) (e (h (j+1))) (e (h (j+2)))

lemma xorConst {B : Bank n} {W : Word n} (hk:0<k) (h:HasWord k B W) (C:Nat) :
    B.Grow (k*1) (fun D => HasWord k D (fun x => W x ^^^ C)) := by
  apply wordBuild hk
  intro D e j
  simpa only [bitsXor] using Bank.xorConst (e (h j)) (bits k C j)

def round (k dist shift C w state : Nat) :=
  rawStep k (state ^^^ rot k dist state ^^^ rot k (k-dist) state) ^^^ rot k shift w ^^^ C

lemma oneRound {B : Bank n} {W V : Word n} {dist shift : Nat} (hk:0<k)
    (h1:dist<k) (h2:k-dist<k) (hs:shift<k) (C:Nat)
    (hW:HasWord k B W) (hV:HasWord k B V) (bw:∀ x,W x<2^k) (bv:∀ x,V x<2^k) :
    B.Grow (k*19) (fun E => HasWord k E (fun x => round k dist shift C (W x) (V x))) := by
  have a:=rotated hV h1 bv
  have b:=rotated hV h2 bv
  have key:=rotated hW hs bw
  obtain ⟨D,e,de,t⟩:=xorWords hk hV a
  obtain ⟨E,f,ef,u⟩:=xorWords hk t (wordLift e b)
  obtain ⟨F,g,fg,v⟩:=nonlinear hk u
  obtain ⟨G,j,gj,p⟩:=xorWords hk v (wordLift g (wordLift f (wordLift e key)))
  obtain ⟨H,m,mh,q⟩:=xorConst hk p C
  exact ⟨H,fun h=>m (j (g (f (e h)))),by omega,q⟩

lemma roundBound {k dist shift C w state : Nat} (hC:C<2^k) : round k dist shift C w state<2^k :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepBound ..) (Nat.mod_lt _ (by positivity))) hC

def recover (k z v : Nat) := rot k (k-3) (z ^^^ v)
lemma recovery {B:Bank n} {Z V:Word n} (hk:20≤k) (hz:HasWord k B Z) (hv:HasWord k B V)
    (bz:∀x,Z x<2^k) (bv:∀x,V x<2^k) :
    B.Grow (k*4) (fun D=> HasWord k D (fun x => recover k (Z x) (V x))) := by
  apply (xorWords (by omega) hz hv).weaken (le_refl _)
  intro D h;exact rotated h (by omega) (fun x=>Nat.xor_lt_two_pow (bz x) (bv x))

end Eval
end PEqualNP.Outside.L_meta_25483_aux

namespace PEqualNP.Outside.L_meta_25483_aux
namespace Eval
open Builder Builder.Bank
variable {n k : Nat}

def rounds (k dist initial a b c ca cb cc w v : Nat) :=
  let init := rot k initial w ^^^ v
  let r1 := round k dist a (3^(k+ca)%2^k) w init
  let r2 := round k dist b (3^(k+cb)%2^k) w r1
  round k dist c (3^(k+cc)%2^k) w r2

lemma roundsBound (k dist initial a b c ca cb cc w v : Nat) :
    rounds k dist initial a b c ca cb cc w v < 2^k :=
  roundBound (Nat.mod_lt _ (by positivity))

lemma three {B:Bank n} {W V:Word n} {dist initial a b c : Nat} (hk:20≤k)
    (hd:0<dist) (hd':dist<k) (hi:initial<k) (ha:a<k) (hb:b<k) (hc:c<k) (ca cb cc:Nat)
    (w:HasWord k B W) (v:HasWord k B V) (bw:∀x,W x<2^k) (bv:∀x,V x<2^k) :
    B.Grow (k*61) (fun D => HasWord k D (fun x=>rounds k dist initial a b c ca cb cc (W x) (V x))) := by
  have hp:0<k:=by omega
  have hh:k-dist<k:=by omega
  obtain ⟨D,e,de,h0⟩:=xorWords hp (rotated w hi bw) v
  obtain ⟨E,f,ef,h1⟩:=oneRound hp hd' hh ha (3^(k+ca)%2^k) (wordLift e w) h0 bw
    (fun x=>Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) (bv x))
  obtain ⟨F,g,fg,h2⟩:=oneRound hp hd' hh hb (3^(k+cb)%2^k) (wordLift f (wordLift e w)) h1 bw
    (fun _=>roundBound (Nat.mod_lt _ (by positivity)))
  obtain ⟨G,j,gj,h3⟩:=oneRound hp hd' hh hc (3^(k+cc)%2^k) (wordLift g (wordLift f (wordLift e w))) h2 bw
    (fun _=>roundBound (Nat.mod_lt _ (by positivity)))
  exact ⟨G,fun h=>j (g (f (e h))),by omega,h3⟩

def row (k w v:Nat) := rounds k 1 1 0 2 4 1 2 3 w v
def col (k w v:Nat) := rounds k 2 3 4 7 10 4 5 6 w v

lemma colEq (k w v:Nat) : col k w v = rawCol k w v := rfl

lemma rowWord {B:Bank n} {W V:Word n} (hk:20≤k)
    (w:HasWord k B W) (v:HasWord k B V) (bw:∀x,W x<2^k) (bv:∀x,V x<2^k) :
    B.Grow (k*61) (fun D=>HasWord k D (fun x=>row k (W x) (V x))) := by
  exact three hk (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) 1 2 3 w v bw bv

lemma colWord {B:Bank n} {W V:Word n} (hk:20≤k)
    (w:HasWord k B W) (v:HasWord k B V) (bw:∀x,W x<2^k) (bv:∀x,V x<2^k) :
    B.Grow (k*61) (fun D=>HasWord k D (fun x=>col k (W x) (V x))) := by
  exact three hk (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) 4 5 6 w v bw bv

def highIndices (k low:Nat) := (List.range k).filter (low ≤ ·)
lemma highEq {k low v:Nat} (bv:v<2^k) :
    (!(highIndices k low).any (fun i=>v.testBit i)) = decide (v<2^low) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true',List.any_eq_false,decide_eq_true_eq]
  constructor
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    by_cases small:i<k
    · simpa using h i (by simp [highIndices,small,hi])
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le bv (Nat.pow_le_pow_right (by decide) (by omega)))
  · intro h i hi
    have hlo:low ≤ i:=by simpa [highIndices] using (List.mem_filter.mp hi).2
    simp [Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hlo))]

lemma testHigh {B:Bank n} {W:Word n} (low:Nat) (h:HasWord k B W) (bw:∀x,W x<2^k) :
    B.Grow (k+2) (fun D=>D.Has (fun x=>decide (W x<2^low))) := by
  have emit (i:Nat) (hi:i∈highIndices k low) : B.Has (fun x=>(W x).testBit i) := by
    have ilt:i<k:=List.mem_range.mp (List.mem_filter.mp hi).1
    simpa only [bits,idxNat ilt] using h i
  obtain ⟨D,e,de,hD⟩:=anyBits (highIndices k low) (fun i x=>(W x).testBit i) emit
  obtain ⟨E,f,ef,v⟩:=inv hD
  have ln:(highIndices k low).length≤k:=by simpa [highIndices] using
    (List.length_filter_le (fun i:Nat=>decide (low ≤ i)) (List.range k))
  refine ⟨E,fun h=>f (e h),by omega,?_⟩
  simpa only [highEq (bw _)] using v

lemma rowTest {B:Bank n} {W V:Word n} (hk:20≤k) (low:Nat)
    (w:HasWord k B W) (v:HasWord k B V) (bw:∀x,W x<2^k) (bv:∀x,V x<2^k) :
    B.Grow (62*k+2) (fun D=>D.Has (fun x=>decide (row k (W x) (V x)<2^low))) := by
  obtain ⟨D,e,de,t⟩:=rowWord hk w v bw bv
  obtain ⟨E,f,ef,u⟩:=testHigh low t (fun x=>roundsBound ..)
  exact ⟨E,fun h=>f (e h),by omega,u⟩

lemma colTest {B:Bank n} {W V:Word n} (hk:20≤k) (low:Nat)
    (w:HasWord k B W) (v:HasWord k B V) (bw:∀x,W x<2^k) (bv:∀x,V x<2^k) :
    B.Grow (62*k+2) (fun D=>D.Has (fun x=>decide (rawCol k (W x) (V x)<2^low))) := by
  obtain ⟨D,e,de,t⟩:=colWord hk w v bw bv
  obtain ⟨E,f,ef,u⟩:=testHigh low t (fun x=>roundsBound ..)
  exact ⟨E,fun h=>f (e h),by omega,u⟩
end Eval
end PEqualNP.Outside.L_meta_25483_aux

namespace PEqualNP.Outside.L_meta_25483_aux
namespace Eval
open Builder Builder.Bank
variable {k n : Nat}

lemma rowFromZ {B:Bank n} {Z U V:Word n} (hk:20≤k) (low:Nat)
    (hz:HasWord k B Z) (hu:HasWord k B U) (hv:HasWord k B V)
    (bz:∀x,Z x<2^k) (bu:∀x,U x<2^k) (bv:∀x,V x<2^k) :
    B.Grow (66*k+2) (fun D=>D.Has (fun x=>decide (row k (recover k (Z x) (V x)) (U x)<2^low))) := by
  obtain ⟨D,e,de,w⟩:=recovery hk hz hv bz bv
  obtain ⟨E,f,ef,q⟩:=rowTest hk low w (wordLift e hu) (fun _=>Nat.mod_lt _ (by positivity)) bu
  exact ⟨E,fun t=>f (e t),by omega,q⟩

lemma verifyBoth {B:Bank n} {Z U V:Word n} (hk:20≤k) (low:Nat)
    (hz:HasWord k B Z) (hu:HasWord k B U) (hv:HasWord k B V)
    (bz:∀x,Z x<2^k) (bu:∀x,U x<2^k) (bv:∀x,V x<2^k) :
    B.Grow (128*k+5) (fun D=>D.Has (fun x=>
      let w := recover k (Z x) (V x)
      decide (row k w (U x)<2^low) && decide (rawCol k w (V x)<2^low))) := by
  obtain ⟨D,e,de,w⟩:=recovery hk hz hv bz bv
  obtain ⟨E,f,ef,r⟩:=rowTest hk low w (wordLift e hu) (fun _=>Nat.mod_lt _ (by positivity)) bu
  obtain ⟨F,g,fg,c⟩:=colTest hk low (wordLift f w) (wordLift f (wordLift e hv))
    (fun _=>Nat.mod_lt _ (by positivity)) bv
  obtain ⟨G,j,jg,t⟩:=meet (g r) c
  exact ⟨G,fun a=>j (g (f (e a))),by omega,t⟩

lemma rowOfficial (k w u : Nat) :
    row k w u = (List.range 3).foldl (fun state i =>
      rawStep k (state ^^^ rot k 1 state ^^^ rot k (k-1) state) ^^^
      rot k (2*i) w ^^^ (3^(k+(i+1))%2^k)) (rot k 1 w ^^^ u) := rfl

end Eval
end PEqualNP.Outside.L_meta_25483_aux

namespace PEqualNP.Outside.L_meta_25483_aux
namespace Sweep
def run (rhs : Nat → (Nat → Bool) → Bool) (seed : Nat → Bool) : Nat → Nat → Bool
  | 0 => seed
  | n+1 => fun i => if i = n then rhs n (run rhs seed n) else run rhs seed n i

def rankPos (k t : Nat) := (2*k-8-t)%k

lemma rank_involutive {k t : Nat} (hk : 20 ≤ k) (ht : t < k) :
    rankPos k (rankPos k t) = t := by
  unfold rankPos
  by_cases h : t ≤ k-8
  · have he : 2*k-8-t = (k-8-t)+k := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (show k-8-t < k by omega)]
    have ht2 : 2*k-8-(k-8-t) = t+k := by omega
    rw [ht2, Nat.add_mod_right, Nat.mod_eq_of_lt ht]
  · have he : 2*k-8-t < k := by omega
    rw [Nat.mod_eq_of_lt he]
    have ht2 : 2*k-8-(2*k-8-t) = t := by omega
    rw [ht2, Nat.mod_eq_of_lt ht]

lemma earlier {k free t d : Nat} (hk : 20 ≤ k) (hf : free ≤ k-19)
    (ht : t < free) (hd : 1 ≤ d) (hd' : d ≤ 19) :
    (t+k-d)%k < t ∨ free ≤ (t+k-d)%k := by
  by_cases hl : d ≤ t
  · have eqn : t+k-d = (t-d)+k := by omega
    rw [eqn, Nat.add_mod_right, Nat.mod_eq_of_lt (show t-d < k by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (show t+k-d < k by omega)]
    omega

lemma recover {k free : Nat} (hk : 20 ≤ k) (hf : free ≤ k-19)
    (rhs : Nat → (Nat → Bool) → Bool) (seed z : Nat → Bool)
    (hseed : ∀ i < k, free ≤ i → seed i = z i)
    (hloc : ∀ t < free, ∀ a b : Nat → Bool,
      (∀ d, 1 ≤ d → d ≤ 19 → a ((t+k-d)%k) = b ((t+k-d)%k)) → rhs t a = rhs t b)
    (hsol : ∀ t < free, rhs t z = z t) (t : Nat) (ht : t ≤ free) :
    ∀ i < k, i < t ∨ free ≤ i → run rhs seed t i = z i := by
  induction t with
  | zero =>
    intro i hi h
    exact hseed i hi (by omega)
  | succ t ih =>
    intro i hi h
    rcases eq_or_ne i t with rfl | hne
    · simp only [run,if_true,eq_self_iff_true]
      rw [← hsol _ (by omega)]
      apply hloc _ (by omega)
      intro d hd hd'
      exact ih (by omega) _ (Nat.mod_lt _ (by omega)) (earlier hk hf (by omega) hd hd')
    · simp only [run,if_neg hne]
      exact ih (by omega) i hi (by omega)

def seedBits (k free : Nat) (z : Nat → Bool) : Fin (2^(k-free)) :=
  let l := List.ofFn (fun j : Fin (k-free) => z (free+j.val))
  let v := BitVec.ofBoolListLE l
  ⟨v.toNat, by simpa [v,l] using v.isLt⟩

lemma readSeed (k free : Nat) (z : Nat → Bool) {i : Nat} (hi : i < k) (h : free ≤ i) :
    (seedBits k free z).val.testBit (i-free) = z i := by
  simp only [seedBits, BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simp; omega)]
  simp [Nat.add_sub_of_le h]

theorem slotExists {k low : Nat} (hk : 20 ≤ k) (hl : low ≤ k)
    (rhs : Nat → (Nat → Bool) → Bool) (z : Nat → Bool)
    (hloc : ∀ t < k-max 19 low, ∀ a b : Nat → Bool,
      (∀ d, 1 ≤ d → d ≤ 19 → a ((t+k-d)%k) = b ((t+k-d)%k)) → rhs t a = rhs t b)
    (hsol : ∀ t < k-max 19 low, rhs t z = z t) :
    ∃ w : Fin (2^max 19 low), ∀ i < k,
      run rhs (fun j => w.val.testBit (j-(k-max 19 low))) (k-max 19 low) i = z i := by
  let f := k-max 19 low
  let w := seedBits k f z
  refine ⟨⟨w.val,?_⟩,?_⟩
  · have eqn : k-f = max 19 low := by dsimp [f]; omega
    rw [←eqn]
    exact w.isLt
  · intro i hi
    apply recover hk (show f ≤ k-19 by dsimp [f]; omega) rhs _ z _ hloc hsol f (by omega) i hi (by omega)
    intro j hj h
    exact readSeed k f z hj h
end Sweep
end PEqualNP.Outside.L_meta_25483_aux

namespace PEqualNP.Outside.L_meta_25483_aux
lemma lowIff {k r low : Nat} (bounds : r<2^k) (l : low ≤ k) :
    r<2^low ↔ ∀ t<k-low, r.testBit (k-1-t)=false := by
  constructor
  · intro h t ht
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
  · intro h
    have e : r % 2^low = r := by
      apply Nat.eq_of_testBit_eq;intro i
      rw [Nat.testBit_mod_two_pow]
      by_cases hi : i<low
      · simp [hi]
      · have f : r.testBit i=false := by
          by_cases hk : i<k
          · have hx := h (k-1-i) (by omega)
            rwa [show k-1-(k-1-i)=i by omega] at hx
          · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le bounds (Nat.pow_le_pow_right (by decide) (by omega)))
        simp [f]
    rw [←e]; exact Nat.mod_lt _ (by positivity)
lemma rawColBound (k w v : Nat) : rawCol k w v < 2^k :=
  roundB k w 6 7 (roundN k w 5 4 (roundN k w 4 1 (rInit k w v)))
lemma colAllPivot {k w v low : Nat} (hk : 20≤k) (hw : w<2^k) (hv : v<2^k) (hl : low≤k) :
  rawCol k w v < 2^low ↔ ∀ t<k-low, (rInit k w v).testBit ((2*k-8-t)%k) =
    pivot (bits k (rInit k w v)) (bits k v) (ctr k 4) (ctr k 5) (ctr k 6) (k-1-(t:Int)) := by
  rw [lowIff (rawColBound k w v) hl]
  exact forall_congr' fun t => forall_congr' fun ht => colRank hk hw hv (by omega)
end PEqualNP.Outside.L_meta_25483_aux

namespace PEqualNP.Outside.L_meta_25483_aux
namespace Sweep
lemma shiftRank {k t d : Nat} (hk : 20 ≤ k) (ht : t < k) (hd : d ≤ 19) :
    rankPos k ((t+k-d)%k) = (2*k-8-t+d)%k := by
  unfold rankPos
  by_cases h : d ≤ t
  · rw [show t+k-d=(t-d)+k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (show t-d<k by omega)]
    congr 1 <;> omega
  · rw [Nat.mod_eq_of_lt (show t+k-d < k by omega)]
    have eqn : 2*k-8-t+d = (2*k-8-(t+k-d))+k := by omega
    rw [eqn, Nat.add_mod_right]

lemma rankBand {k t : Nat} (hk : 20 ≤ k) (ht : t < k) {j : Int}
    (ha : (k:Int)-1-t-6 ≤ j) (hb : j ≤ (k:Int)-1-t+12) :
    ∃ d : Nat, 1 ≤ d ∧ d ≤ 19 ∧ rankPos k (idx k j) = (t+k-d)%k := by
  let d := (j-((k:Int)-8-t)).toNat
  have h1 : 1 ≤ d := by dsimp [d]; omega
  have h2 : d ≤ 19 := by dsimp [d]; omega
  refine ⟨d,h1,h2,?_⟩
  have J : idx k j = (2*k-8-t+d)%k := by
    unfold idx
    rw [←Int.add_emod_left,Int.toNat_emod (by omega) (by omega)]
    congr 1 <;> dsimp [d] <;> omega
  rw [J, ←shiftRank hk ht h2,rank_involutive hk (Nat.mod_lt _ (by omega))]
def localRhs (k v t : Nat) (a : Nat → Bool) :=
  pivot (fun j => a (rankPos k (idx k j))) (bits k v) (ctr k 4) (ctr k 5) (ctr k 6)
    ((k:Int)-1-(t:Int))
lemma localAgree {k t : Nat} (hk : 20 ≤ k) (ht : t < k) (v : Nat) (a b : Nat → Bool)
    (agr : ∀ d, 1 ≤ d → d ≤ 19 → a ((t+k-d)%k) = b ((t+k-d)%k)) :
    localRhs k v t a = localRhs k v t b := by
  apply pivotLocal
  intro j hj hh2
  obtain ⟨d,hd,hh,eqn⟩ := rankBand hk ht hj hh2
  simp only [eqn]
  exact agr d hd hh
def wordOf (k : Nat) (a : Nat → Bool) : Fin (2^k) :=
  seedBits k 0 a
lemma wordBit {k j : Nat} (a : Nat → Bool) (hj : j < k) :
    (wordOf k a).val.testBit j = a j := by simpa [wordOf] using readSeed k 0 a hj (Nat.zero_le _)
def guessZ (k low v w : Nat) := wordOf k (fun j =>
  run (localRhs k v) (fun b => w.testBit (b-(k-max 19 low))) (k-max 19 low) (rankPos k j))
theorem recoverZ {k low w v : Nat} (hk : 20 ≤ k) (hl : low ≤ k)
   (hw : w < 2^k) (hv : v < 2^k) (hcol : rawCol k w v < 2^low)
   (hz : rInit k w v < 2^k) :
   ∃ seed : Fin (2^max 19 low), (guessZ k low v seed.val).val = rInit k w v := by
  let zrank := fun t => (rInit k w v).testBit (rankPos k t)
  obtain ⟨seed,fit⟩ := slotExists hk hl (localRhs k v) zrank
    (fun t ht => localAgree hk (by omega) v) (by
      intro t ht
      have eqn := (colAllPivot hk hw hv hl).1 hcol t (by omega)
      have hfun : (fun j => zrank (rankPos k (idx k j))) = bits k (rInit k w v) := by
        funext j
        unfold zrank bits
        rw [rank_involutive hk (idxlt (by omega) _)]
      unfold localRhs
      rw [hfun]
      exact eqn.symm)
  refine ⟨seed,Nat.eq_of_testBit_eq fun j => ?_⟩
  by_cases h : j<k
  · unfold guessZ
    rw [wordBit _ h,fit (rankPos k j) (show rankPos k j < k from Nat.mod_lt _ (by omega))]
    unfold zrank
    rw [rank_involutive hk h]
  · have e : 2^k ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (guessZ k low v seed.val).isLt e),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hz e)]
end Sweep
end PEqualNP.Outside.L_meta_25483_aux

namespace PEqualNP.Outside.L_meta_25483_aux
open Builder
open Builder.Bank
abbrev MultiSig (n : Nat) := (Fin n → Bool) → Sig
def HasBand {n} (B : Bank n) (f : MultiSig n) (s : Int) (m : Nat) : Prop :=
  ∀ j : Int, s≤j → j<s+(m:Int) → B.Has (fun x => f x j)
lemma bandGrow {n m cost : Nat} {s : Int} (B : Bank n) (f : MultiSig n)
    (step : ∀ D : Bank n, B.Ext D → ∀ j : Int, s≤j → j<s+(m:Int) →
      D.Grow cost (fun E => E.Has (fun x => f x j))) :
    B.Grow (m*cost) (fun E => HasBand E f s m) := by
  have h := B.collectFin m (fun t x => f x (s+(t.val:Int))) cost
    (fun D e t => step D e _ (by omega) (by have := t.isLt; omega))
  apply h.weaken (by rfl)
  intro D v j a b
  let t : Fin m := ⟨(j-s).toNat,by omega⟩
  have eq : s+(t.val:Int)=j := by dsimp [t];omega
  simpa only [eq] using v t
lemma linearCost {n} {D : Bank n} (f : MultiSig n) (j : Int)
    (h : ∀ l : Int, j-2 ≤ l → l ≤ j+2 → D.Has (fun x => f x l)) :
    D.Grow 8 (fun E => E.Has (fun x => linear (f x) j)) := by
  apply (xor2 (h j (by omega) (by omega)) (h (j-2) (by omega) (by omega))).bind (b:=4)
  intro E e a; exact xor2 a (e (h (j+2) (by omega) (by omega)))
lemma chiCost {n} {D : Bank n} {u v w : BitFn n} (a : D.Has u) (b : D.Has v) (c : D.Has w) :
    D.Grow 6 (fun E => E.Has (fun x => chi (u x) (v x) (w x))) := by
  apply (inv b).bind (b:=5);intro E e nb
  apply (meet nb (e c)).bind (b:=4);intro F e' g;exact xor2 (e' (e a)) g
lemma sweepBand {n} (D : Bank n) (f : MultiSig n) (s : Int) (m : Nat)
    (old : HasBand D f (s-2) (m+6)) :
    D.Grow ((m+2)*8 + m*6) (fun E => HasBand E (fun x => sweep (f x)) s m) := by
  have l := bandGrow (s:=s) (m:=m+2) (cost:=8) D (fun x => linear (f x)) (by
    intro E e j hl hr;apply linearCost
    intro t a b;apply e; apply old t <;> omega)
  apply l.bind
  intro E _ h
  apply bandGrow
  intro F e j hl hr
  exact chiCost (e (h j (by omega) (by omega))) (e (h (j+1) (by omega) (by omega))) (e (h (j+2) (by omega) (by omega)))
lemma staticXor {n} {D : Bank n} {f : BitFn n} (h : D.Has f) (a : Bool) :
    D.Grow 1 (fun E => E.Has (fun x => xor (f x) a)) := by
  cases a with
  | true => simpa using inv h
  | false =>
    refine ⟨D,fun hf=>hf,by omega,?_⟩
    simpa using h
lemma stageBand {n} (D : Bank n) (f z v : MultiSig n) (a : Sig) (d s : Int) (m : Nat)
    (old : HasBand D f (s-2) (m+6))
    (q : ∀ j, s≤j → j<s+(m:Int) → D.Has (fun x => z x (j-d)))
    (vavail : ∀ j, D.Has (fun x => v x j)) :
    D.Grow (((m+2)*8 + m*6) + m*9) (fun E => HasBand E (fun x => stage (f x) (z x) (v x) a d) s m) := by
  apply (sweepBand D f s m old).bind
  intro E e h; apply bandGrow
  intro F e' j hl hr
  apply (xor2 (e' (e (q j hl hr))) (e' (e (vavail (j-d))))).bind (b:=5)
  intro H eh key
  apply (xor2 (eh (e' (h j hl hr))) key).bind (b:=1); intro J _ ff
  exact staticXor ff (a j)
lemma pivotCost {n} (D : Bank n) (z v : MultiSig n) (a b c : Sig) (i : Int)
    (wires : HasBand D z (i-6) 19)
    (vavail : ∀ j, D.Has (fun x => v x j)) :
    D.Grow 527 (fun E => E.Has (fun x => pivot (z x) (v x) a b c i)) := by
  let f1 : MultiSig n := fun x => stage (z x) (z x) (v x) a 1
  let f2 : MultiSig n := fun x => stage (f1 x) (z x) (v x) b 4
  have o1 : HasBand D z ((i-4)-2) (13+6) := by intro j hl hr;exact wires j (by omega) (by omega)
  apply (stageBand D z z v a 1 (i-4) 13 o1 (by intro j l r;apply wires <;>omega) vavail).bind (b:=212)
  intro E e h1
  have o2 : HasBand E f1 ((i-2)-2) (7+6) := by intro j hl hr;exact h1 j (by omega) (by omega)
  apply (stageBand E f1 z v b 4 (i-2) 7 o2 (by intro j l r;apply e;apply wires <;>omega) (fun j=>e (vavail j))).bind (b:=35)
  intro F e' h2
  have o3 : HasBand F f2 (i-2) (1+6) := by intro j hl hr;exact h2 j (by omega) (by omega)
  apply (sweepBand F f2 i 1 o3).bind (b:=5)
  intro H eh h3
  apply (xor2 (h3 i (by omega) (by omega)) (eh (e' (e (vavail (i-7)))))).bind (b:=1)
  intro J _ hv;exact staticXor hv (c i)
end PEqualNP.Outside.L_meta_25483_aux

namespace PEqualNP.Outside.L_meta_25483_aux
namespace Sweep
open Builder Builder.Bank
def pivotRhs (k v : Nat) (t : Nat) (a : Nat → Bool) :=
  pivot (fun j => a (rankPos k (idx k j))) (bits k v) (ctr k 4) (ctr k 5) (ctr k 6)
    ((k:Int)-1-(t:Int))
lemma sweepCost {n} (B : Bank n) (k free : Nat) (V : (Fin n → Bool) → Nat) (seed : Nat → Bool)
    (hav : ∀ j, B.Has (fun x => bits k (V x) j)) :
    B.Grow (2+527*free) (fun D => ∀ j, D.Has (fun x => run (pivotRhs k (V x)) seed free j)) := by
  induction free with
  | zero =>
    apply (Bank.const B false).bind (b:=1)
    intro D _ h0
    obtain ⟨E,e,sz,h1⟩ := Bank.const D true
    refine ⟨E,e,sz,?_⟩
    intro j
    change E.Has (fun _ => seed j)
    rcases h : seed j with _ | _
    · simpa only [h] using e h0
    · simpa only [h] using h1
  | succ t ih =>
    rw [Nat.mul_succ,←Nat.add_assoc]
    apply ih.bind
    intro D e ha
    let z : MultiSig n := fun x j => run (pivotRhs k (V x)) seed t (rankPos k (idx k j))
    have bnd : HasBand D z (((k:Int)-1-(t:Int))-6) 19 := fun j _ _ => ha _
    have pc := pivotCost D z (fun x => bits k (V x)) (ctr k 4) (ctr k 5) (ctr k 6)
      ((k:Int)-1-(t:Int)) bnd (fun j=>e (hav j))
    obtain ⟨E,ef,sz,hp⟩ := pc
    refine ⟨E,ef,sz,?_⟩
    intro j
    by_cases h : j=t
    · subst j; simp only [run,ite_true,eq_self_iff_true]; unfold pivotRhs; exact hp
    · simpa only [run,if_neg h] using ef (ha j)
end Sweep
end PEqualNP.Outside.L_meta_25483_aux

namespace PEqualNP.Outside.L_meta_25483_aux
namespace Eval
open Builder Builder.Bank
variable {k n : Nat}

def slotOK (k low seed u v : Nat) :=
  let z := (Sweep.guessZ k low v seed).val
  let w := recover k z v
  decide (row k w u < 2^low) && decide (rawCol k w v < 2^low)

lemma compiledSlot {U V : Word n} (B : Bank n) (hk : 20 ≤ k) (low seed : Nat)
    (hu : HasWord k B U) (hv : HasWord k B V)
    (bu : ∀x,U x<2^k) (bv : ∀x,V x<2^k) :
    B.Grow (527*(k-max 19 low)+128*k+7) (fun D=>D.Has (fun x=>slotOK k low seed (U x) (V x))) := by
  let free := k-max 19 low
  let mask := fun t : Nat => seed.testBit (t-free)
  obtain ⟨D,e,de,hw⟩:=Sweep.sweepCost B k free V mask hv
  let Z : Word n := fun x => (Sweep.guessZ k low (V x) seed).val
  have hz : HasWord k D Z := by
    intro j
    have he (x : Fin n → Bool) : bits k (Z x) j =
        Sweep.run (Sweep.pivotRhs k (V x)) mask free (Sweep.rankPos k (idx k j)) := by
      unfold bits Z Sweep.guessZ
      rw [Sweep.wordBit _ (idxlt (by omega) _)]
      rfl
    simpa only [he] using hw (Sweep.rankPos k (idx k j))
  have bz (x) : Z x < 2^k := (Sweep.guessZ k low (V x) seed).isLt
  obtain ⟨E,f,ef,t⟩:=verifyBoth hk low hz (wordLift e hu) (wordLift e hv) bz bu bv
  exact ⟨E,fun a=>f (e a),by dsimp [free] at de; omega,t⟩

end Eval
end PEqualNP.Outside.L_meta_25483_aux

namespace PEqualNP.Outside.L_meta_25483_aux

abbrev recoverKey (k z v : Nat) := rot k (k-3) (z ^^^ v)

lemma recoverKeyLt (k z v : Nat) : recoverKey k z v < 2^k :=
  Nat.mod_lt _ (by positivity)

private lemma wordEqBits {k a b : Nat} (ha : a<2^k) (hb : b<2^k)
    (h : ∀ j : Int, bits k a j = bits k b j) : a=b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i<k
  · have e : idx k (i : Int) = i := by
      unfold idx
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      rfl
    simpa only [bits,e] using h (i : Int)
  · have hp : 2^k ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hp),Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hp)]

lemma rotUndo {k s w : Nat} (hs : 0<s) (hsk : s<k) (hw : w<2^k) :
    rot k (k-s) (rot k s w) = w := by
  apply wordEqBits (k:=k) (a:=rot k (k-s) (rot k s w)) (Nat.mod_lt _ (by positivity)) hw
  intro j
  have hb : rot k s w < 2^k := Nat.mod_lt _ (by positivity)
  rw [bitsRot (show k-s<k by omega) hb,bitsRot hsk hw]
  have q : j - ((k-s:Nat):Int) - (s:Int) = j - (k:Int) := by omega
  simp [bits,idx,q]

lemma recoverInit {k w v : Nat} (hk : 20≤k) (hw : w<2^k) :
    recoverKey k (rInit k w v) v = w := by
  simp only [recoverKey,rInit,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]
  exact rotUndo (by decide) (by omega) hw

lemma initRecover {k z v : Nat} (hk : 20≤k) (hz : z<2^k) (hv : v<2^k) :
    rInit k (recoverKey k z v) v = z := by
  have hi := rotUndo (k:=k) (s:=k-3) (w:=z ^^^ v) (by omega) (by omega) (Nat.xor_lt_two_pow hz hv)
  rw [show k-(k-3)=3 by omega] at hi
  simp only [rInit,recoverKey,hi,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]

end PEqualNP.Outside.L_meta_25483_aux

namespace PEqualNP.Outside.L_meta_25483_aux
def testKey (k low u v w : Nat) : Bool :=
  decide (Eval.row k w u < 2^low) && decide (rawCol k w v < 2^low)
def slotCheck (k low u v seed : Nat) := testKey k low u v (recoverKey k (Sweep.guessZ k low v seed).val v)
theorem candidatesCorrect {k low : Nat} (hk : 20 ≤ k) (hl : low ≤ k) (u v : Nat) (hv : v < 2^k) :
    (List.finRange (2^max 19 low)).any (fun s => slotCheck k low u v s.val) =
    (List.range (2^k)).any (testKey k low u v) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,List.mem_finRange,true_and,List.mem_range]
  constructor
  · rintro ⟨s,hs⟩
    exact ⟨_,recoverKeyLt k (Sweep.guessZ k low v s.val).val v,hs⟩
  · rintro ⟨w,hw,ok⟩
    have both := Bool.and_eq_true_iff.mp ok
    have hz : rInit k w v < 2^k := by
      apply Nat.xor_lt_two_pow
      · exact Nat.mod_lt _ (by positivity)
      · exact hv
    obtain ⟨s,hs⟩ := Sweep.recoverZ hk hl hw hv (of_decide_eq_true both.2) hz
    refine ⟨s,?_⟩
    unfold slotCheck
    rw [hs,recoverInit hk hw]
    exact ok
end PEqualNP.Outside.L_meta_25483_aux

namespace PEqualNP.Outside.L_meta_25483_aux
namespace Name
open Builder Builder.Bank PEqualNP.MetaComplexity

theorem nameIndexSucc {n : ℕ} (x : Fin (n + 1) → Bool) :
    tableIndex x = tableIndex (fun i : Fin n => x i.castSucc)
      + (if x (Fin.last n) = true then 2 ^ n else 0) := by
  unfold tableIndex
  rw [Fin.sum_univ_castSucc]
  rfl

theorem nameIndexLt : ∀ {n : ℕ} (x : Fin n → Bool), tableIndex x < 2 ^ n := by
  intro n
  induction n with
  | zero => intro x; simp [tableIndex]
  | succ n ih =>
    intro x
    rw [nameIndexSucc, pow_succ]
    have := ih (fun i : Fin n => x i.castSucc)
    split <;> omega

theorem nameIndexBit : ∀ {n : ℕ} (x : Fin n → Bool) (i : Fin n),
    Nat.testBit (tableIndex x) i = x i := by
  intro n
  induction n with
  | zero => intro x i; exact i.elim0
  | succ n ih =>
    intro x i
    have hlt := nameIndexLt (fun i : Fin n => x i.castSucc)
    rw [nameIndexSucc]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.val_last]
      by_cases h : x (Fin.last n) = true
      · simp only [h, ↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        rfl
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        rw [Nat.add_zero, Nat.testBit_lt_two_pow hlt]
    · have hj : (j.castSucc : ℕ) = (j : ℕ) := rfl
      rw [hj]
      by_cases h : x (Fin.last n) = true
      · simp only [h, ↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_gt j.isLt]
        exact ih _ j
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        rw [Nat.add_zero]
        exact ih _ j

def name {k n : Nat} (atWire : Fin k → Fin n) (x : Fin n → Bool) : Nat :=
  (Fin.ofNat (2^k) (tableIndex fun i : Fin k => x (atWire i))).val

lemma nameLt {k n : Nat} (atWire : Fin k → Fin n) (x : Fin n → Bool) :
    name atWire x < 2^k := (Fin.ofNat (2^k) (tableIndex fun i : Fin k => x (atWire i))).isLt

lemma nameBit {k n : Nat} (atWire : Fin k → Fin n) (x : Fin n → Bool) (i : Fin k) :
    (name atWire x).testBit i.val = x (atWire i) := by
  change ((tableIndex fun i : Fin k => x (atWire i)) % 2^k).testBit i.val = _
  rw [Nat.mod_eq_of_lt (nameIndexLt _), nameIndexBit]

lemma nameSig {k n : Nat} (hk : 0<k) (atWire : Fin k → Fin n) (j : Int) :
    (Bank.empty n).Has (fun x => bits k (name atWire x) j) := by
  let i : Fin k := ⟨idx k j,idxlt hk j⟩
  have e (x : Fin n → Bool) : bits k (name atWire x) j = x (atWire i) := nameBit atWire x i
  simpa only [e] using Bank.input (atWire i)

abbrev row (k : Nat) := name (fun i : Fin k => Fin.castAdd k i)
abbrev col (k : Nat) := name (fun i : Fin k => Fin.natAdd k i)

end Name
end PEqualNP.Outside.L_meta_25483_aux

open PEqualNP.Outside.L_meta_25483_aux
open PEqualNP.Outside.L_meta_25483_aux.Builder
theorem PEqualNP.Outside.L_meta_25483 : ∀ k : Nat, 20 ≤ k →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let constant := fun (j : Nat) => 3 ^ (k + j) % 2 ^ k
  let first := fun (rowKey rowName : Nat) =>
    (List.range 3).foldl (fun state i =>
      step (state ^^^ rot 1 state ^^^ rot (k - 1) state) ^^^
        rot (2 * i) rowKey ^^^ constant (i + 1)) (rot 1 rowKey ^^^ rowName)
  let second := fun (colKey colName : Nat) =>
    (List.range 3).foldl (fun state i =>
      step (state ^^^ rot 2 state ^^^ rot (k - 2) state) ^^^
        rot (3 * (i + 1) + 1) colKey ^^^ constant (3 + (i + 1))) (rot 3 colKey ^^^ colName)
  let low := k - (k + 1) / 2
  let graph : Fin (2 ^ k) → Fin (2 ^ k) → Bool := fun row col =>
    (List.range (2 ^ k)).any (fun w =>
      decide (first w row.val < 2 ^ low) && decide (second w col.val < 2 ^ low))
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + k) C ∧
    C.size ≤ 2 ^ max 19 low * (500 * k) ∧
    ∀ bits : Fin (k + k) → Bool,
      C.eval (List.ofFn bits) = PEqualNP.Represents.adjFun (k := k) (l := k) graph bits := by
  intro k hk
  let low := k-(k+1)/2
  let slots := List.finRange (2^max 19 low)
  let cost := 527*(k-max 19 low)+128*k+7
  let fn := fun (s : Fin (2^max 19 low)) (x : Fin (k+k) → Bool) =>
    Eval.slotOK k low s.val (Name.row k x) (Name.col k x)
  have composed := Bank.anySlots (Bank.empty (k+k)) slots fn cost (by
    intro D ext s hs
    apply Eval.compiledSlot D hk
    · intro j
      exact ext (Name.nameSig (by omega : 0 < k) (fun i : Fin k => Fin.castAdd k i) j)
    · intro j
      exact ext (Name.nameSig (by omega : 0 < k) (fun i : Fin k => Fin.natAdd k i) j)
    · exact Name.nameLt _
    · exact Name.nameLt _)
  obtain ⟨C,fan,back,size,ok⟩ := Bank.finish composed
  refine ⟨C,fan,back,?_,?_⟩
  · change C.size ≤ 2^max 19 low*(500*k)
    have cb : cost+2 ≤ 500*k := by dsimp [cost,low]; omega
    have hlen : slots.length = 2^max 19 low := by simp [slots]
    rw [hlen] at size
    have pos : 0 < 2^max 19 low := by positivity
    calc
      C.size ≤ 1+2^max 19 low*(cost+1) := size
      _ ≤ 2^max 19 low*((cost+1)+1) := by simp only [Nat.mul_add,Nat.mul_one];omega
      _ ≤ _ := Nat.mul_le_mul_left _ cb
  · intro x
    rw [ok]
    exact candidatesCorrect hk (by dsimp [low];omega) (Name.row k x) (Name.col k x) (Name.nameLt _ x)
