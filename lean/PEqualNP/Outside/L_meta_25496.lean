import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_25496_aux
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
end PEqualNP.Outside.L_meta_25496_aux

namespace PEqualNP.Outside.L_meta_25496_aux
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
end PEqualNP.Outside.L_meta_25496_aux

namespace PEqualNP.Outside.L_meta_25496_aux

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

end PEqualNP.Outside.L_meta_25496_aux

namespace PEqualNP.Outside.L_meta_25496_aux
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
end PEqualNP.Outside.L_meta_25496_aux

namespace PEqualNP.Outside.L_meta_25496_aux.Builder
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
end PEqualNP.Outside.L_meta_25496_aux.Builder

namespace PEqualNP.Outside.L_meta_25496_aux.Builder.Bank

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

end PEqualNP.Outside.L_meta_25496_aux.Builder.Bank

namespace PEqualNP.Outside.L_meta_25496_aux
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
end PEqualNP.Outside.L_meta_25496_aux

namespace PEqualNP.Outside.L_meta_25496_aux
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
end PEqualNP.Outside.L_meta_25496_aux

namespace PEqualNP.Outside.L_meta_25496_aux.Name
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

end PEqualNP.Outside.L_meta_25496_aux.Name

namespace PEqualNP.Outside.L_meta_25496_aux.Work96
open Builder
def initW (k w u : Nat) := rot k 1 w ^^^ u
def recW (k z u : Nat) := rot k (k-1) (z ^^^ u)
lemma recBound (k z u : Nat) : recW k z u < 2^k := Nat.mod_lt _ (by positivity)
lemma initBound {k} (w : Nat) {u} (hu : u<2^k) : initW k w u < 2^k := Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) hu
lemma recInit {k w u} (hk : 8 ≤ k) (hw : w<2^k) : recW k (initW k w u) u = w := by
  simp only [recW,initW,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]
  exact rotUndo (by decide) (by omega) hw
lemma initRec {k z u} (hk : 8 ≤ k) (hz : z<2^k) (hu : u<2^k) : initW k (recW k z u) u = z := by
  have hi := rotUndo (k:=k) (s:=k-1) (w:=z ^^^ u) (by omega) (by omega) (Nat.xor_lt_two_pow hz hu)
  rw [show k-(k-1)=1 by omega] at hi
  simp only [initW,recW,hi,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]
lemma recBudget {k n} {B : Bank n} {Z U : Eval.Word n} (hk : 8≤k)
    (hz : Eval.HasWord k B Z) (hu : Eval.HasWord k B U) (bz : ∀x, Z x<2^k) (bu : ∀x,U x<2^k) :
    B.Grow (4*k) (fun D => Eval.HasWord k D (fun x=>recW k (Z x) (U x))) := by
  obtain ⟨D,e,sz,hw⟩ := Eval.xorWords (by omega : 0<k) hz hu
  refine ⟨D,e,by omega,?_⟩
  exact Eval.rotated hw (show k-1<k by omega) (fun x=>Nat.xor_lt_two_pow (bz x) (bu x))
def packed (k : Nat) (f : Nat → Bool) := Sweep.seedBits k 0 f
lemma packBit96 {k j} (f) (h : j<k) : (packed k f).val.testBit j = f j := by
  simpa [packed] using Sweep.readSeed k 0 f h (Nat.zero_le _)
lemma eqOfLowBits {k a b : Nat} (ha : a<2^k) (hb : b<2^k)
    (eq : ∀ i<k, a.testBit i = b.testBit i) : a=b := by
  apply Nat.eq_of_testBit_eq;intro i
  by_cases h : i<k
  · exact eq i h
  · have p : 2^k ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha p),Nat.testBit_lt_two_pow (lt_of_lt_of_le hb p)]
end PEqualNP.Outside.L_meta_25496_aux.Work96

namespace PEqualNP.Outside.L_meta_25496_aux.Row96
open Builder Builder.Bank
def init (k w u : Nat) := rot k 1 w ^^^ u
def lin (k x : Nat) := x ^^^ rot k 1 x ^^^ rot k (k-1) x
def first (k w u : Nat) :=
  rawStep k (lin k (init k w u)) ^^^ rot k 0 w ^^^ (3^(k+1)%2^k)

def pivot (x u a : Sig) (i : Int) : Bool :=
  let v := xor (x (i+1)) (x (i+2))
  xor (xor (xor (x i) (!(xor (x i) v) && xor v (x (i+3)))) (u (i+1))) (a i)

lemma ext {x y : Sig} (u a : Sig) (i : Int) (h : Agrees x y i (i+3)) :
    pivot x u a i = pivot y u a i := by
  unfold pivot
  rw [h i (by omega) (by omega),h (i+1) (by omega) (by omega),
      h (i+2) (by omega) (by omega),h (i+3) (by omega) (by omega)]

lemma linBit {k x : Nat} (hk : 8≤k) (hx : x<2^k) (j : Int) :
    bits k (lin k x) j = xor (xor (bits k x j) (bits k x (j-1))) (bits k x (j+1)) := by
  simp only [lin,bitsXor,bitsRot (show 1<k by omega) hx,bitsRot (show k-1<k by omega) hx]
  have e : j-((k-1:Nat):Int)=(j+1)-(k:Int) := by omega
  simp [bits,idx,e]

lemma initBound {k w u : Nat} (hu : u<2^k) : init k w u < 2^k :=
  Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) hu

lemma firstBound (k w u : Nat) : first k w u < 2^k :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepBound ..) (Nat.mod_lt _ (by positivity))) (Nat.mod_lt _ (by positivity))

lemma algebra (m x y z t u a : Bool) :
    xor (xor (chi (xor (xor x m) y) (xor (xor y x) z) (xor (xor z y) t)) (xor y u)) a = false ↔
    m = xor (xor (xor x (!(xor x (xor y z)) && xor (xor y z) t)) u) a := by
  cases m <;> cases x <;> cases y <;> cases z <;> cases t <;> cases u <;> cases a <;> decide

lemma law {k w u : Nat} (hk : 8≤k) (hw : w<2^k) (hu : u<2^k) (i : Int) :
    bits k (first k w u) i = false ↔ bits k (init k w u) (i-1) =
      pivot (bits k (init k w u)) (bits k u) (ctr k 1) i := by
  let x := init k w u
  have hx : x<2^k := initBound hu
  have key : bits k (rot k 0 w) i = xor (bits k x (i+1)) (bits k u (i+1)) := by
    simp only [x,init,bitsXor,bitsRot (show 1<k by omega) hw,bitsRot (show 0<k by omega) hw]
    simp
  simp only [first,bitsXor]
  change xor (xor (bits k (rawStep k (lin k x)) i) (bits k (rot k 0 w) i)) (ctr k 1 i) = false ↔ _
  rw [bitsStep (show 0<k by omega),key,linBit hk hx,linBit hk hx,linBit hk hx]
  rw [show i+1-1=i by omega,show i+1+1=i+2 by omega,show i+2-1=i+1 by omega,show i+2+1=i+3 by omega]
  exact algebra ..

lemma emit {n : Nat} {B : Bank n} (x u : (Fin n → Bool) → Sig) (a : Sig) (i : Int)
    (h0 : B.Has (fun s => x s i)) (h1 : B.Has (fun s => x s (i+1)))
    (h2 : B.Has (fun s => x s (i+2))) (h3 : B.Has (fun s => x s (i+3)))
    (hu : B.Has (fun s => u s (i+1))) :
    B.Grow 23 (fun D => D.Has (fun s => pivot (x s) (u s) a i)) := by
  apply (xor2 h1 h2).bind (b:=19)
  intro E e hv
  apply (xor2 (e h0) hv).bind (b:=15)
  intro F f hb
  apply (xor2 (f hv) (f (e h3))).bind (b:=11)
  intro G g hc
  apply (inv (g hb)).bind (b:=10)
  intro H h hnb
  apply (meet hnb (h hc)).bind (b:=9)
  intro J j hand
  apply (xor2 (j (h (g (f (e h0))))) hand).bind (b:=5)
  intro K m hab
  apply (xor2 hab (m (j (h (g (f (e hu))))))).bind (b:=1)
  intro L l val
  exact xorConst val (a i)

end PEqualNP.Outside.L_meta_25496_aux.Row96

namespace PEqualNP.Outside.L_meta_25496_aux
namespace Sweep96
open Sweep (run seedBits readSeed)
def rank96 (k t : Nat) := (2*k-2-t)%k

lemma rank_involutive {k t : Nat} (hk : 8 ≤ k) (ht : t < k) :
    rank96 k (rank96 k t) = t := by
  unfold rank96
  by_cases h : t ≤ k-2
  · have he : 2*k-2-t = (k-2-t)+k := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (show k-2-t < k by omega)]
    have ht2 : 2*k-2-(k-2-t) = t+k := by omega
    rw [ht2, Nat.add_mod_right, Nat.mod_eq_of_lt ht]
  · have he : 2*k-2-t < k := by omega
    rw [Nat.mod_eq_of_lt he]
    have ht2 : 2*k-2-(2*k-2-t) = t := by omega
    rw [ht2, Nat.mod_eq_of_lt ht]

lemma earlier {k free t d : Nat} (hk : 8 ≤ k) (hf : free ≤ k-4)
    (ht : t < free) (hd : 1 ≤ d) (hd' : d ≤ 4) :
    (t+k-d)%k < t ∨ free ≤ (t+k-d)%k := by
  by_cases hl : d ≤ t
  · have eqn : t+k-d = (t-d)+k := by omega
    rw [eqn, Nat.add_mod_right, Nat.mod_eq_of_lt (show t-d < k by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (show t+k-d < k by omega)]
    omega

lemma recover {k free : Nat} (hk : 8 ≤ k) (hf : free ≤ k-4)
    (rhs : Nat → (Nat → Bool) → Bool) (seed z : Nat → Bool)
    (hseed : ∀ i < k, free ≤ i → seed i = z i)
    (hloc : ∀ t < free, ∀ a b : Nat → Bool,
      (∀ d, 1 ≤ d → d ≤ 4 → a ((t+k-d)%k) = b ((t+k-d)%k)) → rhs t a = rhs t b)
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

lemma shiftRank {k t d : Nat} (hk : 8 ≤ k) (ht : t < k) (hd : d ≤ 4) :
    rank96 k ((t+k-d)%k) = (2*k-2-t+d)%k := by
  unfold rank96
  by_cases h : d ≤ t
  · rw [show t+k-d=(t-d)+k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (show t-d<k by omega)]
    congr 1 <;> omega
  · rw [Nat.mod_eq_of_lt (show t+k-d < k by omega)]
    have eqn : 2*k-2-t+d = (2*k-2-(t+k-d))+k := by omega
    rw [eqn, Nat.add_mod_right]

lemma rankBand {k t : Nat} (hk : 8 ≤ k) (ht : t < k) {j : Int}
    (ha : (k:Int)-1-t ≤ j) (hb : j ≤ (k:Int)+2-t) :
    ∃ d : Nat, 1 ≤ d ∧ d ≤ 4 ∧ rank96 k (idx k j) = (t+k-d)%k := by
  let d := (j-((k:Int)-2-t)).toNat
  have h1 : 1 ≤ d := by dsimp [d]; omega
  have h2 : d ≤ 4 := by dsimp [d]; omega
  refine ⟨d,h1,h2,?_⟩
  have J : idx k j = (2*k-2-t+d)%k := by
    unfold idx
    rw [←Int.add_emod_left,Int.toNat_emod (by omega) (by omega)]
    congr 1 <;> dsimp [d] <;> omega
  rw [J, ←shiftRank hk ht h2,rank_involutive hk (Nat.mod_lt _ (by omega))]

lemma smallerUnchanged (rhs : Nat → (Nat → Bool) → Bool) (seed : Nat → Bool)
    {a b i : Nat} (hab : a ≤ b) (hi : i<a) : run rhs seed b i = run rhs seed a i := by
  induction b with
  | zero => have := Nat.eq_zero_of_le_zero hab; subst a; rfl
  | succ b ih =>
    by_cases eqn : a=b+1
    · rw [eqn]
    · have hin : i ≠ b := by omega
      simp only [run, if_neg hin]
      exact ih (by omega)
lemma biggerUnchanged (rhs : Nat → (Nat → Bool) → Bool) (seed : Nat → Bool)
    {a i : Nat} (h : a ≤ i) : run rhs seed a i = seed i := by
  induction a with
  | zero => rfl
  | succ a ih =>
    have hn : i ≠ a := by omega
    simp only [run,if_neg hn]
    exact ih (by omega)
lemma runSolves {k free : Nat} (hk : 8≤k) (hf : free ≤ k-4)
    (rhs : Nat → (Nat → Bool) → Bool) (seed : Nat → Bool)
    (hloc : ∀ t < free, ∀ a b : Nat → Bool,
      (∀ d, 1 ≤ d → d ≤ 4 → a ((t+k-d)%k) = b ((t+k-d)%k)) → rhs t a = rhs t b)
    {t : Nat} (ht : t < free) : run rhs seed free t = rhs t (run rhs seed free) := by
  calc
    run rhs seed free t = run rhs seed (t+1) t := smallerUnchanged rhs seed ht (by omega)
    _ = rhs t (run rhs seed t) := by simp [run]
    _ = rhs t (run rhs seed free) := by
      apply hloc t ht
      intro d h1 h4
      rcases earlier hk hf ht h1 h4 with e|e
      · exact (smallerUnchanged rhs seed (by omega) e).symm
      · rw [biggerUnchanged rhs seed (by omega : t ≤ (t+k-d)%k),biggerUnchanged rhs seed e]
theorem slots {k free : Nat} (hk : 8 ≤ k) (hf : free ≤ k-4)
    (rhs : Nat → (Nat → Bool) → Bool) (z : Nat → Bool)
    (hloc : ∀ t < free, ∀ a b : Nat → Bool,
      (∀ d, 1 ≤ d → d ≤ 4 → a ((t+k-d)%k) = b ((t+k-d)%k)) → rhs t a = rhs t b)
    (hsol : ∀ t < free, rhs t z = z t) :
    ∃ w : Fin (2^(k-free)), ∀ i < k, run rhs (fun j => w.val.testBit (j-free)) free i = z i := by
  refine ⟨seedBits k free z,?_⟩
  intro i hi
  apply recover hk hf rhs _ z _ hloc hsol free (by omega) i hi (by omega)
  intro j hj h
  exact readSeed k free z hj h
end Sweep96
end PEqualNP.Outside.L_meta_25496_aux

namespace PEqualNP.Outside.L_meta_25496_aux.Work96
open Sweep96
def rhs (k u t : Nat) (a : Nat → Bool) :=
  Row96.pivot (fun j => a (rank96 k (idx k j))) (bits k u) (ctr k 1) ((k:Int)-1-t)
def state (k h u seed : Nat) := Sweep.run (rhs k u) (fun j => seed.testBit (j-h)) h
def guess (k h u seed : Nat) := packed k (fun j => state k h u seed (rank96 k j))
def key (k h u seed : Nat) := recW k (guess k h u seed).val u
def ranked (k w : Nat) (t : Nat) := w.testBit (rank96 k t)
lemma sigRank {k} (hk : 8≤k) (w : Nat) :
    (fun j => ranked k w (rank96 k (idx k j))) = bits k w := by
  funext j;unfold ranked bits;rw [rank_involutive hk (idxlt (by omega) _)]
lemma loc {k t} (hk : 8≤k) (ht : t<k) (u : Nat) (a b : Nat→Bool)
    (h : ∀ d, 1≤d → d≤4 → a ((t+k-d)%k) = b ((t+k-d)%k)) : rhs k u t a = rhs k u t b := by
  apply Row96.ext
  intro j lo hi
  obtain ⟨d,d1,d4,e⟩ := rankBand hk ht lo (by omega)
  change a (rank96 k (idx k j)) = b (rank96 k (idx k j))
  rw [e]; exact h d d1 d4
lemma rowCriterion {k h w u : Nat} (hk : 8≤k) (hh : h≤k) (hw : w<2^k) (hu : u<2^k) :
  Row96.first k w u < 2^(k-h) ↔ ∀t<h, rhs k u t (ranked k (initW k w u)) = ranked k (initW k w u) t := by
  rw [lowIff (Row96.firstBound ..) (by omega),show k-(k-h)=h by omega]
  apply forall_congr';intro t;apply forall_congr';intro ht
  have e0 : idx k ((k:Int)-1-t)=k-1-t := by unfold idx; rw [Int.emod_eq_of_lt (by omega) (by omega)];omega
  have e1 : idx k ((k:Int)-1-t-1)=rank96 k t := by
    unfold idx rank96;rw [←Int.add_emod_left,Int.toNat_emod (by omega) (by omega)]
    congr 1 <;> omega
  unfold rhs;rw [sigRank hk]
  have eqn := Row96.law hk hw hu ((k:Int)-1-t)
  apply Iff.trans _ eq_comm
  simpa only [bits,e0,e1,ranked,initW,Row96.init] using eqn
lemma rankGuess {k h u seed t} (hk : 8≤k) (ht : t<k) :
    ranked k (guess k h u seed).val t = state k h u seed t := by
  unfold ranked guess; rw [packBit96 (k:=k) (j:=rank96 k t) _ (show rank96 k t<k from Nat.mod_lt _ (by omega)),rank_involutive hk ht]
lemma keyOk {k h u : Nat} (hk : 8≤k) (hf : h≤k-4) (hu : u<2^k) (seed : Nat) :
    Row96.first k (key k h u seed) u < 2^(k-h) := by
  apply (rowCriterion hk (by omega) (recBound ..) hu).2
  intro t ht
  rw [initRec hk (guess k h u seed).isLt hu,rankGuess hk (by omega)]
  have localE := fun s (hs:s<h) => loc hk (show s<k by omega) u
  have sol := runSolves hk hf (rhs k u) (fun j => seed.testBit (j-h)) localE ht
  refine Eq.trans ?_ sol.symm
  apply loc hk (by omega)
  intro d d1 d4
  exact rankGuess hk (Nat.mod_lt _ (by omega))
lemma contains {k h u w : Nat} (hk : 8≤k) (hf : h≤k-4) (hw : w<2^k) (hu : u<2^k)
    (row : Row96.first k w u < 2^(k-h)) :
    ∃ seed : Fin (2^(k-h)), key k h u seed.val = w := by
  have hsol := (rowCriterion hk (by omega) hw hu).1 row
  obtain ⟨seed,fit⟩ := slots hk hf (rhs k u) (ranked k (initW k w u))
    (fun t ht => loc hk (by omega) u) hsol
  refine ⟨seed,?_⟩
  have good : (guess k h u seed.val).val = initW k w u := by
    apply eqOfLowBits (k:=k) (guess k h u seed.val).isLt (initBound w hu)
    intro i hi
    unfold guess
    rw [packBit96 (k:=k) _ hi]
    unfold state
    rw [fit (rank96 k i) (show rank96 k i<k from Nat.mod_lt _ (by omega))]
    unfold ranked;rw [rank_involutive hk hi]
  unfold key;rw [good,recInit hk hw]
end PEqualNP.Outside.L_meta_25496_aux.Work96

namespace PEqualNP.Outside.L_meta_25496_aux.Eval
open Builder Builder.Bank

def second96 (k w v : Nat) := round k 2 4 (3^(k+2) % 2^k) w (rInit k w v)

private lemma colAll96 {k h y : Nat} (hh : h≤k) (hy : y<2^k) :
    (List.range h).all (fun t => !(y.testBit (k-1-t))) = decide (y<2^(k-h)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true,List.mem_range,Bool.not_eq_true',decide_eq_true_eq]
  rw [lowIff hy (by omega : k-h≤k),show k-(k-h)=h by omega]

lemma column96 {n k h : Nat} {B : Bank n} {W V : Word n} (hk : 8≤k) (hh : h≤k)
    (w : HasWord k B W) (v : HasWord k B V) (bw : ∀ x,W x<2^k) (bv : ∀ x,V x<2^k) :
    B.Grow (12*k+12*h+1) (fun D => D.Has
      (fun x => decide (second96 k (W x) (V x) < 2^(k-h)))) := by
  let Z : Word n := fun x => rInit k (W x) (V x)
  let L : Word n := fun x => rawLin k (Z x)
  let Y : Word n := fun x => second96 k (W x) (V x)
  let cst := 3^(k+2)%2^k
  have pos : 0<k := by omega
  have bz : ∀ x,Z x < 2^k := fun x => Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) (bv x)
  have by' : ∀ x,Y x < 2^k := fun _ => roundBound (Nat.mod_lt _ (by positivity))
  have key := rotated (s:=4) w (by omega) bw
  obtain ⟨D,e,de,hz⟩ := xorWords pos (rotated (s:=3) w (by omega) bw) v
  change HasWord k D Z at hz
  obtain ⟨E,f,ef,ha⟩ := xorWords pos hz (rotated (s:=2) hz (by omega) bz)
  obtain ⟨F,g,fg,hL⟩ := xorWords pos ha (wordLift f (rotated (s:=k-2) hz (by omega) bz))
  change HasWord k F L at hL
  have emit (A : Bank n) (u : F.Ext A) (t : Nat) (ht : t ∈ List.range h) :
      A.Grow 11 (fun Q => Q.Has (fun x => !((Y x).testBit (k-1-t)))) := by
    let j : Int := ((k-1-t : Nat) : Int)
    have he : idx k j = k-1-t := idxNat (by omega)
    have eqbit (x) : (!((Y x).testBit (k-1-t))) =
        xor (xor (chi (bits k (L x) j) (bits k (L x) (j+1)) (bits k (L x) (j+2)))
          (bits k (rot k 4 (W x)) j)) (!(bits k cst j)) := by
      change (!((rawStep k (L x) ^^^ rot k 4 (W x) ^^^ cst).testBit (k-1-t))) = _
      rw [←he]
      change (!(bits k (rawStep k (L x) ^^^ rot k 4 (W x) ^^^ cst) j)) = _
      simp only [bitsXor,bitsStep pos]
      generalize xor (chi _ _ _) (bits k (rot k 4 (W x)) j) = b
      cases b <;> cases bits k cst j <;> rfl
    have eqfun := funext eqbit
    rw [eqfun]
    apply (chiBit (u (hL j)) (u (hL (j+1))) (u (hL (j+2)))).bind (b:=5)
    intro A' ea hchi
    apply (xor2 hchi (ea (u (g (f (e (key j))))))).bind (b:=1)
    intro A'' _ hb
    exact Bank.xorConst hb _
  obtain ⟨H,i,hi,ans⟩ := allSlots F (List.range h) (fun t x => !((Y x).testBit (k-1-t))) 11 emit
  simp only [List.length_range] at hi
  refine ⟨H,fun hs=>i (g (f (e hs))),by omega,?_⟩
  simpa only [colAll96 hh (by' _)] using ans

end PEqualNP.Outside.L_meta_25496_aux.Eval

namespace PEqualNP.Outside.L_meta_25496_aux.Work96
open Sweep96 Builder
lemma stateCost {n k : Nat} (B : Bank n) (U : Eval.Word n) (hu : Eval.HasWord k B U) (h seed : Nat) :
    B.Grow (2+23*h) (fun D => ∀ j, D.Has (fun x => state k h (U x) seed j)) := by
  let f (j : Nat) := seed.testBit (j-h)
  have aux (t : Nat) : B.Grow (2+23*t) (fun D => ∀j, D.Has (fun x => Sweep.run (rhs k (U x)) f t j)) := by
    induction t with
    | zero =>
      apply (Bank.const B false).bind (b:=1)
      intro D _ h0
      obtain ⟨E,e,sz,h1⟩ := Bank.const D true
      refine ⟨E,e,sz,?_⟩; intro j; change E.Has (fun _ => f j)
      cases q : f j
      · exact e h0
      · exact h1
    | succ t ih =>
      rw [Nat.mul_succ,←Nat.add_assoc]
      apply ih.bind
      intro D e prev
      let z := fun (x : Fin n → Bool) (j : Int) => Sweep.run (rhs k (U x)) f t (rank96 k (idx k j))
      let pos := (k:Int)-1-t
      obtain ⟨E,ef,sz,hp⟩ := Row96.emit (B:=D) z (fun x => bits k (U x)) (ctr k 1) pos
        (prev _) (prev _) (prev _) (prev _) (e (hu _))
      refine ⟨E,ef,sz,?_⟩;intro j;by_cases eq : j=t
      · subst j;simp only [Sweep.run,ite_true,eq_self_iff_true];unfold rhs;exact hp
      · simpa only [Sweep.run,if_neg eq] using ef (prev j)
  exact aux h
def slot (k h seed u v : Nat) : Bool := decide (Eval.second96 k (key k h u seed) v < 2^(k-h))
lemma compileSlot {n k h : Nat} {U V : Eval.Word n} (B : Bank n) (hk : 8≤k) (hh : h≤k)
    (hu : Eval.HasWord k B U) (hv : Eval.HasWord k B V)
    (bu : ∀x,U x<2^k) (bv : ∀x,V x<2^k) (seed : Nat) :
    B.Grow (35*h+16*k+3) (fun D => D.Has (fun x=>slot k h seed (U x) (V x))) := by
  obtain ⟨D,e,sd,wires⟩ := stateCost B U hu h seed
  let Z : Eval.Word n := fun x => (guess k h (U x) seed).val
  have hz : Eval.HasWord k D Z := by
    intro j
    have eqn (x : Fin n→Bool) : bits k (Z x) j = state k h (U x) seed (rank96 k (idx k j)) := by
      unfold Z bits guess;rw [packBit96 _ (idxlt (by omega) j)]
    simpa only [eqn] using wires (rank96 k (idx k j))
  obtain ⟨E,ee,se,keyw⟩ := recBudget hk hz (Eval.wordLift e hu) (fun x => (guess k h (U x) seed).isLt) bu
  obtain ⟨F,ef,sf,ok⟩ := Eval.column96 hk hh keyw (Eval.wordLift ee (Eval.wordLift e hv)) (fun x=>recBound ..) bv
  exact ⟨F,fun a=>ef (ee (e a)),by omega,ok⟩
def test (k h u v w : Nat) := decide (Row96.first k w u < 2^(k-h)) && decide (Eval.second96 k w v < 2^(k-h))
lemma correct {k h u v : Nat} (hk : 8≤k) (hf : h≤k-4) (hu : u<2^k) :
    (List.finRange (2^(k-h))).any (fun s => slot k h s.val u v) = (List.range (2^k)).any (test k h u v) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,List.mem_finRange,true_and,List.mem_range]
  constructor
  · rintro ⟨s,ok⟩
    exact ⟨_,recBound k (guess k h u s.val).val u,Bool.and_eq_true_iff.mpr ⟨decide_eq_true (keyOk hk hf hu s.val),ok⟩⟩
  · rintro ⟨w,hw,ok⟩
    obtain ⟨row,col⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨s,hs⟩ := contains hk hf hw hu (of_decide_eq_true row)
    exact ⟨s,by unfold slot;rw [hs];exact col⟩
end PEqualNP.Outside.L_meta_25496_aux.Work96

open PEqualNP.Outside.L_meta_25496_aux PEqualNP.Outside.L_meta_25496_aux.Builder PEqualNP.Outside.L_meta_25496_aux.Work96 in
theorem PEqualNP.Outside.L_meta_25496 : ∀ k : Nat, 8 ≤ k →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let constant := fun (j : Nat) => 3 ^ (k + j) % 2 ^ k
  let first := fun (rowKey rowName : Nat) =>
    let x := rot 1 rowKey ^^^ rowName
    step (x ^^^ rot 1 x ^^^ rot (k - 1) x) ^^^ rot 0 rowKey ^^^ constant 1
  let second := fun (colKey colName : Nat) =>
    let z := rot 3 colKey ^^^ colName
    step (z ^^^ rot 2 z ^^^ rot (k - 2) z) ^^^ rot 4 colKey ^^^ constant 2
  let slots := 2 ^ (k - (k + 1) / 2)
  let graph : Fin (2 ^ k) → Fin (2 ^ k) → Bool := fun row col =>
    (List.range (2 ^ k)).any (fun w =>
      decide (first w row.val < slots) && decide (second w col.val < slots))
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + k) C ∧
    C.size ≤ slots * (36 * k) ∧
    ∀ bits : Fin (k + k) → Bool,
      C.eval (List.ofFn bits) = PEqualNP.Represents.adjFun (k := k) (l := k) graph bits := by
  intro k hk
  let h := (k+1)/2
  let l := List.finRange (2^(k-h))
  let cost := 35*h+16*k+3
  let f := fun (s : Fin (2^(k-h))) (x : Fin (k+k) → Bool) => slot k h s.val (Name.row k x) (Name.col k x)
  have out := Bank.anySlots (Bank.empty (k+k)) l f cost (by
    intro D e s hs
    apply compileSlot D hk (by dsimp [h];omega)
    · exact fun j => e (Name.nameSig (by omega : 0<k) (fun i : Fin k => Fin.castAdd k i) j)
    · exact fun j => e (Name.nameSig (by omega : 0<k) (fun i : Fin k => Fin.natAdd k i) j)
    · exact Name.nameLt _
    · exact Name.nameLt _)
  obtain ⟨C,fan,back,sz,val⟩ := Bank.finish out
  refine ⟨C,fan,back,?_,?_⟩
  · change C.size ≤ 2^(k-h)*(36*k)
    rw [show l.length=2^(k-h) by simp [l]] at sz
    have pos : 0<2^(k-h) := by positivity
    have small : cost+2 ≤ 36*k := by dsimp [cost,h];omega
    calc
      C.size ≤ 1+2^(k-h)*(cost+1) := sz
      _ ≤ 2^(k-h)*((cost+1)+1) := by simp only [Nat.mul_add,Nat.mul_one]; omega
      _ ≤ _ := Nat.mul_le_mul_left _ small
  · intro x;rw [val]
    exact correct hk (by dsimp [h];omega) (Name.nameLt _ x)
