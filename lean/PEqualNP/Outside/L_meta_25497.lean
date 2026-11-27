import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25497_aux
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
end PEqualNP.Outside.L_meta_25497_aux

namespace PEqualNP.Outside.L_meta_25497_aux
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
end PEqualNP.Outside.L_meta_25497_aux

namespace PEqualNP.Outside.L_meta_25497_aux
namespace S97
def run (rhs : Nat → (Nat → Bool) → Bool) (seed : Nat → Bool) : Nat → Nat → Bool
  | 0 => seed
  | n+1 => fun i => if i = n then rhs n (run rhs seed n) else run rhs seed n i

def rankPos (k t : Nat) := (2*k-3-t)%k

lemma rank_involutive {k t : Nat} (hk : 16 ≤ k) (ht : t < k) :
    rankPos k (rankPos k t) = t := by
  unfold rankPos
  by_cases h : t ≤ k-3
  · have he : 2*k-3-t = (k-3-t)+k := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (show k-3-t < k by omega)]
    have ht2 : 2*k-3-(k-3-t) = t+k := by omega
    rw [ht2, Nat.add_mod_right, Nat.mod_eq_of_lt ht]
  · have he : 2*k-3-t < k := by omega
    rw [Nat.mod_eq_of_lt he]
    have ht2 : 2*k-3-(2*k-3-t) = t := by omega
    rw [ht2, Nat.mod_eq_of_lt ht]

lemma earlier {k free t d : Nat} (hk : 16 ≤ k) (hf : free ≤ k-8)
    (ht : t < free) (hd : 1 ≤ d) (hd' : d ≤ 8) :
    (t+k-d)%k < t ∨ free ≤ (t+k-d)%k := by
  by_cases hl : d ≤ t
  · have eqn : t+k-d = (t-d)+k := by omega
    rw [eqn, Nat.add_mod_right, Nat.mod_eq_of_lt (show t-d < k by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (show t+k-d < k by omega)]
    omega

lemma recover {k free : Nat} (hk : 16 ≤ k) (hf : free ≤ k-8)
    (rhs : Nat → (Nat → Bool) → Bool) (seed z : Nat → Bool)
    (hseed : ∀ i < k, free ≤ i → seed i = z i)
    (hloc : ∀ t < free, ∀ a b : Nat → Bool,
      (∀ d, 1 ≤ d → d ≤ 8 → a ((t+k-d)%k) = b ((t+k-d)%k)) → rhs t a = rhs t b)
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

theorem slotExists {k low : Nat} (hk : 16 ≤ k) (hl : low ≤ k)
    (rhs : Nat → (Nat → Bool) → Bool) (z : Nat → Bool)
    (hloc : ∀ t < k-max 8 low, ∀ a b : Nat → Bool,
      (∀ d, 1 ≤ d → d ≤ 8 → a ((t+k-d)%k) = b ((t+k-d)%k)) → rhs t a = rhs t b)
    (hsol : ∀ t < k-max 8 low, rhs t z = z t) :
    ∃ w : Fin (2^max 8 low), ∀ i < k,
      run rhs (fun j => w.val.testBit (j-(k-max 8 low))) (k-max 8 low) i = z i := by
  let f := k-max 8 low
  let w := seedBits k f z
  refine ⟨⟨w.val,?_⟩,?_⟩
  · have eqn : k-f = max 8 low := by dsimp [f]; omega
    rw [←eqn]
    exact w.isLt
  · intro i hi
    apply recover hk (show f ≤ k-8 by dsimp [f]; omega) rhs _ z _ hloc hsol f (by omega) i hi (by omega)
    intro j hj h
    exact readSeed k f z hj h

lemma runPast {rhs : Nat → (Nat → Bool) → Bool} {seed : Nat → Bool}
    {a b j : Nat} (hab : a≤b) (hj : j<a ∨ b≤j) :
    run rhs seed b j = run rhs seed a j := by
  induction b generalizing a with
  | zero => rw [show a=0 by omega]
  | succ b ih =>
    by_cases eqn:a=b+1
    · subst a; rfl
    have hne:j≠b:=by omega
    simpa only [run,if_neg hne] using (ih (a:=a) (by omega) (by omega))

lemma solution {k free : Nat} (hk : 16 ≤ k) (hf : free ≤ k-8)
    (rhs : Nat → (Nat → Bool) → Bool) (seed : Nat → Bool)
    (loc : ∀ t < free, ∀ a b : Nat → Bool,
      (∀ d, 1 ≤ d → d ≤ 8 → a ((t+k-d)%k)=b ((t+k-d)%k)) → rhs t a=rhs t b)
    (t : Nat) (ht : t<free) :
    run rhs seed free t = rhs t (run rhs seed free) := by
  calc
    run rhs seed free t = run rhs seed (t+1) t := runPast (by omega) (Or.inl (Nat.lt_succ_self t))
    _ = rhs t (run rhs seed t) := by simp only [run,eq_self_iff_true,ite_true]
    _ = _ := by
      apply loc t ht
      intro d hd hd'
      exact (runPast (a:=t) (b:=free) (by omega) (earlier hk hf ht hd hd')).symm
lemma shiftRank {k t d : Nat} (hk : 16 ≤ k) (ht : t < k) (hd : d ≤ 8) :
    rankPos k ((t+k-d)%k) = (2*k-3-t+d)%k := by
  unfold rankPos
  by_cases h : d ≤ t
  · rw [show t+k-d=(t-d)+k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (show t-d<k by omega)]
    congr 1 <;> omega
  · rw [Nat.mod_eq_of_lt (show t+k-d < k by omega)]
    have eqn : 2*k-3-t+d = (2*k-3-(t+k-d))+k := by omega
    rw [eqn, Nat.add_mod_right]

lemma rankBand {k t : Nat} (hk : 16 ≤ k) (ht : t < k) {j : Int}
    (ha : (k:Int)-1-t-1 ≤ j) (hb : j ≤ (k:Int)-1-t+6) :
    ∃ d : Nat, 1 ≤ d ∧ d ≤ 8 ∧ rankPos k (idx k j) = (t+k-d)%k := by
  let d := (j-((k:Int)-3-t)).toNat
  have h1 : 1 ≤ d := by dsimp [d]; omega
  have h2 : d ≤ 8 := by dsimp [d]; omega
  refine ⟨d,h1,h2,?_⟩
  have J : idx k j = (2*k-3-t+d)%k := by
    unfold idx
    rw [←Int.add_emod_left,Int.toNat_emod (by omega) (by omega)]
    congr 1 <;> dsimp [d] <;> omega
  rw [J, ←shiftRank hk ht h2,rank_involutive hk (Nat.mod_lt _ (by omega))]
def wordOf (k : Nat) (a : Nat → Bool) : Fin (2^k) := seedBits k 0 a
lemma wordBit {k j : Nat} (a : Nat → Bool) (hj : j<k) :
    (wordOf k a).val.testBit j = a j := by simpa [wordOf] using readSeed k 0 a hj (Nat.zero_le _)
end S97
end PEqualNP.Outside.L_meta_25497_aux

namespace PEqualNP.Outside.L_meta_25497_aux
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
end PEqualNP.Outside.L_meta_25497_aux

namespace PEqualNP.Outside.L_meta_25497_aux.Builder.Bank

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

end PEqualNP.Outside.L_meta_25497_aux.Builder.Bank

namespace PEqualNP.Outside.L_meta_25497_aux
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
end PEqualNP.Outside.L_meta_25497_aux

namespace PEqualNP.Outside.L_meta_25497_aux
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
end PEqualNP.Outside.L_meta_25497_aux

namespace PEqualNP.Outside.L_meta_25497_aux

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

end PEqualNP.Outside.L_meta_25497_aux

namespace PEqualNP.Outside.L_meta_25497_aux
namespace Col97
open PEqualNP.Outside.L_meta_25497_aux
open Builder Builder.Bank Eval
variable {n k : Nat}

def recover1 (k x u : Nat) := rot k (k-1) (x ^^^ u)
def rowInit (k w u : Nat) := rot k 1 w ^^^ u

lemma recover1Lt (k x u : Nat) : recover1 k x u < 2^k := Nat.mod_lt _ (by positivity)

lemma recover1Init {w u : Nat} (hk : 16≤k) (hw : w<2^k) :
    recover1 k (rowInit k w u) u = w := by
  simp only [recover1,rowInit,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]
  exact rotUndo (by decide) (by omega) hw

lemma initRecover1 {z u : Nat} (hk : 16≤k) (hz : z<2^k) (hu : u<2^k) :
    rowInit k (recover1 k z u) u = z := by
  have hi := rotUndo (k:=k) (s:=k-1) (w:=z ^^^ u) (by omega) (by omega) (Nat.xor_lt_two_pow hz hu)
  rw [show k-(k-1)=1 by omega] at hi
  simp only [rowInit,recover1,hi,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]

def colInit (k w v : Nat) := rot k 3 w ^^^ v
def colMiddle (k w v : Nat) := round k 2 4 (3^(k+3)%2^k) w (colInit k w v)
def rawCol2 (k w v : Nat) := round k 2 7 (3^(k+4)%2^k) w (colMiddle k w v)

lemma recoverAt {B : Bank n} {X U : Word n} (hk : 16≤k)
    (hx : HasWord k B X) (hu : HasWord k B U) (bx : ∀ x, X x < 2^k) (bu : ∀ x, U x < 2^k) :
    B.Grow (4*k) (fun D => HasWord k D (fun x => recover1 k (X x) (U x))) := by
  obtain ⟨D,e,c,v⟩ := xorWords (by omega) hx hu
  exact ⟨D,e,by omega,rotated v (by omega) (fun x => Nat.xor_lt_two_pow (bx x) (bu x))⟩

lemma middleAt {B : Bank n} {W V : Word n} (hk : 16≤k)
    (hw : HasWord k B W) (hv : HasWord k B V) (bw : ∀ x, W x < 2^k) (bv : ∀x, V x < 2^k) :
    B.Grow (23*k) (fun D => HasWord k D (fun x => colMiddle k (W x) (V x))) := by
  obtain ⟨D,e,c,t⟩ := xorWords (by omega) (rotated hw (show 3<k by omega) bw) hv
  obtain ⟨E,f,d,q⟩ := oneRound (dist:=2) (shift:=4) (by omega) (by omega) (by omega) (by omega)
    (3^(k+3)%2^k) (wordLift e hw) t bw (fun x => Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) (bv x))
  exact ⟨E,fun h => f (e h),by omega,q⟩

lemma evalSlot {B : Bank n} {X U V : Word n} (hk : 16≤k) (low : Nat)
    (hx : HasWord k B X) (hu : HasWord k B U) (hv : HasWord k B V)
    (bx : ∀x, X x < 2^k) (bu : ∀x, U x < 2^k) (bv : ∀x, V x < 2^k) :
    B.Grow (47*k+2) (fun D => D.Has (fun x =>
      decide (rawCol2 k (recover1 k (X x) (U x)) (V x) < 2^low))) := by
  obtain ⟨D,e,c,w⟩ := recoverAt hk hx hu bx bu
  obtain ⟨E,f,d,t⟩ := middleAt hk w (wordLift e hv) (fun _ => recover1Lt ..) bv
  obtain ⟨F,g,fc,u⟩ := oneRound (dist:=2) (shift:=7) (by omega) (by omega) (by omega) (by omega)
    (3^(k+4)%2^k) (wordLift f w) t (fun _ => recover1Lt ..) (fun _ => roundBound (Nat.mod_lt _ (by positivity)))
  obtain ⟨H,j,jc,q⟩ := testHigh low u (fun _ => roundBound (Nat.mod_lt _ (by positivity)))
  exact ⟨H,fun a => j (g (f (e a))),by omega,q⟩

end Col97
end PEqualNP.Outside.L_meta_25497_aux

namespace PEqualNP.Outside.L_meta_25497_aux
namespace S97
open PEqualNP.Outside.L_meta_25497_aux.Col97
abbrev Pv := (Int → Bool) → (Int → Bool) → (Int → Bool) → (Int → Bool) → Int → Bool

def rhs (p : Pv) (k u t : Nat) (a : Nat → Bool) : Bool :=
  p (fun j=>a (rankPos k (idx k j))) (bits k u) (ctr k 1) (ctr k 2) ((k:Int)-1-(t:Int))

def Local (p : Pv) := ∀ (a b u c d : Int → Bool) (i:Int),
  (∀ j, i-1 ≤ j → j ≤ i+6 → a j=b j) → p a u c d i=p b u c d i

lemma localAgree {k t : Nat} {p : Pv} (hk:16≤k) (ht:t<k) (loc:Local p) (u:Nat) (a b : Nat → Bool)
    (agr:∀ d,1≤d → d≤8 → a ((t+k-d)%k)=b ((t+k-d)%k)) :
    rhs p k u t a = rhs p k u t b := by
  apply loc
  intro j h jh
  obtain ⟨d,h1,h2,eqn⟩:=rankBand hk ht h jh
  simp only [eqn];exact agr d h1 h2

def guess (p : Pv) (k low u seed : Nat) := wordOf k (fun j =>
  run (rhs p k u) (fun b=>seed.testBit (b-(k-low))) (k-low) (rankPos k j))

def Valid (p:Pv) (k low u z:Nat) : Prop :=
  ∀ t<k-low, z.testBit (rankPos k t) =
    p (bits k z) (bits k u) (ctr k 1) (ctr k 2) ((k:Int)-1-(t:Int))

lemma guessValid {p:Pv} (loc:Local p) {k low:Nat} (hk:16≤k) (hl:8≤low) (hle:low≤k)
    (u seed:Nat) : Valid p k low u (guess p k low u seed).val := by
  let f := k-low
  let s := fun b:Nat=>seed.testBit (b-f)
  let a := run (rhs p k u) s f
  have wit (j:Int) : bits k (guess p k low u seed).val j = a (rankPos k (idx k j)) := by
    unfold bits guess;rw [wordBit _ (idxlt (by omega) _)]
  intro t ht
  have tlt:t<k:=by omega
  have hr:rankPos k t<k:=Nat.mod_lt _ (by omega)
  have eqa := solution (k:=k) (free:=f) hk (by dsimp [f];omega) (rhs p k u) s
    (fun t ht a b => localAgree hk (by dsimp [f] at ht;omega) loc u a b) t ht
  unfold guess
  rw [wordBit _ hr,rank_involutive hk tlt]
  change a t = p (bits k (guess p k low u seed).val) _ _ _ _
  rw [show bits k (guess p k low u seed).val = (fun j=> a (rankPos k (idx k j))) from funext wit]
  exact eqa

lemma getGuess {p:Pv} (loc:Local p) {k low:Nat} (hk:16≤k) (hl:8≤low) (hle:low≤k)
    {u z:Nat} (hz:z<2^k) (hvalid:Valid p k low u z) :
    ∃ s:Fin (2^low), (guess p k low u s.val).val = z := by
  let zrank := fun t => z.testBit (rankPos k t)
  have ml : max 8 low=low:=max_eq_right hl
  have ex := slotExists hk hle (rhs p k u) zrank
    (fun t ht a b=>localAgree hk (by omega) loc u a b) (by
      rw [ml]; intro t ht
      have eqn:=hvalid t ht
      have hfun : (fun j => zrank (rankPos k (idx k j))) = bits k z := by
        funext j;unfold zrank bits;rw [rank_involutive hk (idxlt (by omega) _)]
      unfold rhs;rw [hfun]; exact eqn.symm)
  rw [ml] at ex
  obtain ⟨s,fit⟩:=ex
  refine ⟨s,Nat.eq_of_testBit_eq fun j=>?_⟩
  by_cases h:j<k
  · unfold guess;rw [wordBit _ h,fit (rankPos k j) (show rankPos k j < k from Nat.mod_lt _ (by omega))]
    unfold zrank;rw [rank_involutive hk h]
  · have bound : 2^k≤2^j:=Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (guess p k low u s.val).isLt bound),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hz bound)]

def rawRow (k w u:Nat) :=
  let mix := fun x => rawStep k (x ^^^ rot k 1 x ^^^ rot k (k-1) x)
  let x := rowInit k w u
  let x1 := mix x ^^^ rot k 0 w ^^^ (3^(k+1)%2^k)
  mix x1 ^^^ rot k 2 w ^^^ (3^(k+2)%2^k)

def test (k low u v w:Nat) :=
  decide (rawRow k w u < 2^low) && decide (rawCol2 k w v < 2^low)

def accept (p:Pv) (k low u v seed:Nat) :=
  decide (rawCol2 k (recover1 k (guess p k low u seed).val u) v < 2^low)

theorem candidateIff {p:Pv} (loc:Local p) {k low:Nat} (hk:16≤k) (hl:8≤low) (hle:low≤k)
    (u v:Nat) (hu:u<2^k)
    (eqv:∀ w, w<2^k → (rawRow k w u<2^low ↔ Valid p k low u (rowInit k w u))) :
    (List.finRange (2^low)).any (fun s=>accept p k low u v s.val) = (List.range (2^k)).any (test k low u v) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,List.mem_finRange,true_and,List.mem_range]
  constructor
  · rintro ⟨s,hs⟩
    let z := (guess p k low u s.val).val
    let w := recover1 k z u
    have hw : w<2^k:=recover1Lt ..
    have hi : rowInit k w u = z := initRecover1 hk (guess p k low u s.val).isLt hu
    have hr : rawRow k w u<2^low:=(eqv w hw).2 (hi ▸ guessValid loc hk hl hle u s.val)
    exact ⟨w,hw,Bool.and_eq_true_iff.mpr ⟨decide_eq_true hr,hs⟩⟩
  · rintro ⟨w,hw,ok⟩
    have parts := Bool.and_eq_true_iff.mp ok
    have bz : rowInit k w u<2^k:=Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) hu
    obtain ⟨s,hs⟩:=getGuess loc hk hl hle bz ((eqv w hw).1 (of_decide_eq_true parts.1))
    refine ⟨s,?_⟩
    unfold accept;rw [hs,recover1Init hk hw];exact parts.2
end S97
end PEqualNP.Outside.L_meta_25497_aux

namespace PEqualNP.Outside.L_meta_25497_aux
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
end PEqualNP.Outside.L_meta_25497_aux

namespace PEqualNP.Outside.L_meta_25497_aux
namespace S97
open Builder Builder.Bank Eval
open PEqualNP.Outside.L_meta_25497_aux.Col97

def HasEmitter (p : Pv) (n : Nat) := ∀ (B : Bank n) (x u : (Fin n → Bool) → Int → Bool)
  (a b : Int → Bool) (i : Int),
  (∀ j : Int, i-1 ≤ j → j ≤ i+6 → B.Has (fun z=>x z j)) →
  (∀ j : Int, B.Has (fun z=>u z j)) →
  B.Grow 154 (fun E=>E.Has (fun z=>p (x z) (u z) a b i))

lemma sweepGates {n} {p:Pv} (emit:HasEmitter p n) (B : Bank n) (k free : Nat)
    (U : Word n) (seed : Nat → Bool) (hav : HasWord k B U) :
    B.Grow (2+154*free) (fun D => ∀ j, D.Has (fun x => run (rhs p k (U x)) seed free j)) := by
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
    let z := fun (x: Fin n → Bool) (j:Int) => run (rhs p k (U x)) seed t (rankPos k (idx k j))
    have pc := emit D z (fun x => bits k (U x)) (ctr k 1) (ctr k 2)
      ((k:Int)-1-(t:Int)) (fun j _ _=>ha _) (fun j=>e (hav j))
    obtain ⟨E,ef,sz,hp⟩ := pc
    refine ⟨E,ef,sz,?_⟩
    intro j
    by_cases h : j=t
    · subst j; simp only [run,ite_true,eq_self_iff_true]; exact hp
    · simpa only [run,if_neg h] using ef (ha j)

lemma compiledSlot {n k : Nat} {p:Pv} (emit:HasEmitter p n) {U V : Word n} (B : Bank n)
    (hk : 16 ≤ k) (low seed : Nat) (hu : HasWord k B U) (hv : HasWord k B V)
    (bu : ∀x,U x<2^k) (bv : ∀x,V x<2^k) :
    B.Grow (154*(k-low)+47*k+4) (fun D=>D.Has (fun x=>accept p k low (U x) (V x) seed)) := by
  let f:=k-low
  let s:=fun t:Nat=>seed.testBit (t-f)
  obtain ⟨D,e,de,ha⟩:=sweepGates emit B k f U s hu
  let X : Word n:= fun x=>(guess p k low (U x) seed).val
  have hx:HasWord k D X:=by
    intro j
    have he (x:Fin n → Bool):bits k (X x) j = run (rhs p k (U x)) s f (rankPos k (idx k j)) := by
      unfold bits X guess; rw [wordBit _ (idxlt (by omega) _)]
    simpa only [he] using ha (rankPos k (idx k j))
  obtain ⟨E,g,eg,q⟩:=evalSlot hk low hx (wordLift e hu) (wordLift e hv) (fun x=>(guess p k low (U x) seed).isLt) bu bv
  exact ⟨E,fun a=>g (e a),by dsimp [f] at de;omega,q⟩

lemma whole {p : Pv} {k : Nat} (hk : 16 ≤ k) (emit:HasEmitter p (k+k)) (loc:Local p)
    (correct : ∀ (w u low : Nat), w<2^k → u<2^k → low≤k →
      (rawRow k w u < 2^low ↔ Valid p k low u (rowInit k w u))) :
    let low := k-(k+1)/2
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+k) C ∧
      C.size ≤ 2^low*(130*k) ∧ ∀ x:Fin (k+k) → Bool,
      C.eval (List.ofFn x) = (List.range (2^k)).any (test k low (Name.row k x) (Name.col k x)) := by
  intro low
  let slots := List.finRange (2^low)
  let cost := 154*(k-low)+47*k+4
  let fn := fun (s : Fin (2^low)) (x : Fin (k+k) → Bool) =>
    accept p k low (Name.row k x) (Name.col k x) s.val
  have composed := Bank.anySlots (Bank.empty (k+k)) slots fn cost (by
    intro D ext s hs
    apply compiledSlot emit D hk
    · intro j;exact ext (Name.nameSig (by omega : 0 < k) (fun i : Fin k => Fin.castAdd k i) j)
    · intro j;exact ext (Name.nameSig (by omega : 0 < k) (fun i : Fin k => Fin.natAdd k i) j)
    · exact Name.nameLt _
    · exact Name.nameLt _)
  obtain ⟨C,fan,back,size,ok⟩ := Bank.finish composed
  refine ⟨C,fan,back,?_,?_⟩
  · have cb : cost+2 ≤ 130*k := by dsimp [cost,low];omega
    have hlen : slots.length = 2^low := by simp [slots]
    rw [hlen] at size
    have pos : 0<2^low:=by positivity
    calc
      C.size ≤ 1+2^low*(cost+1):=size
      _ ≤ 2^low*((cost+1)+1) := by simp only [Nat.mul_add,Nat.mul_one];omega
      _ ≤ _ := Nat.mul_le_mul_left _ cb
  · intro x;rw [ok]
    exact candidateIff loc hk (by dsimp [low];omega) (by dsimp [low];omega) (Name.row k x) (Name.col k x)
      (Name.nameLt _ x) (fun w hw=>correct w _ _ hw (Name.nameLt _ x) (by dsimp [low];omega))
end S97
end PEqualNP.Outside.L_meta_25497_aux

namespace PEqualNP.Outside.L_meta_25497_aux
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
end PEqualNP.Outside.L_meta_25497_aux

namespace PEqualNP.Outside.L_meta_25497_aux
namespace P97

def lin (x : Sig) (i : Int) :=
  xor (xor (x i) (x (i-1))) (x (i+1))

def mix (x : Sig) (i : Int) :=
  chi (lin x i) (lin x (i+1)) (lin x (i+2))

def first (x u c1 : Sig) (j : Int) :=
  xor (xor (mix x j) (xor (x (j+1)) (u (j+1)))) (c1 j)

def output (x u c1 c2 : Sig) (i : Int) :=
  xor (xor (mix (first x u c1) i) (xor (x (i-1)) (u (i-1)))) (c2 i)

def masked (x : Sig) (i j : Int) := if j=i-2 then false else x j

def pivot (x u c1 c2 : Sig) (i : Int) := output (masked x i) u c1 c2 i

private theorem xorCancelR (a b c : Bool) :
    xor (xor a c) (xor b c) = xor a b := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem xorCancelL (a b c : Bool) :
    xor (xor c a) (xor c b) = xor a b := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem linOn {x y : Sig} {i : Int} (h : Agrees x y (i-1) (i+1)) :
    lin x i = lin y i := by
  unfold lin
  rw [h i (by omega) (by omega), h (i-1) (by omega) (by omega), h (i+1) (by omega) (by omega)]

private theorem mixOn {x y : Sig} {i : Int} (h : Agrees x y (i-1) (i+3)) :
    mix x i = mix y i := by
  have l (j : Int) (a : i ≤ j) (b : j ≤ i+2) : lin x j = lin y j :=
    linOn (fun t ht th => h t (by omega) (by omega))
  unfold mix
  rw [l i (by omega) (by omega), l (i+1) (by omega) (by omega), l (i+2) (by omega) (by omega)]

private theorem mixDiff {x y : Sig} {i : Int} (h : Agrees x y i (i+3)) :
    xor (mix x i) (mix y i) = xor (x (i-1)) (y (i-1)) := by
  have l (j : Int) (a : i < j) (b : j ≤ i+2) : lin x j = lin y j :=
    linOn (fun t ht th => h t (by omega) (by omega))
  unfold mix chi
  rw [l (i+1) (by omega) (by omega), l (i+2) (by omega) (by omega),xorCancelR]
  unfold lin
  rw [h i (by omega) (by omega),h (i+1) (by omega) (by omega),xorCancelR,xorCancelL]

private theorem firstOn {x y : Sig} (u c1 : Sig) {i : Int} (h : Agrees x y (i-1) (i+3)) :
    first x u c1 i = first y u c1 i := by
  unfold first
  rw [mixOn h,h (i+1) (by omega) (by omega)]

private theorem firstDiff {x y : Sig} (u c1 : Sig) {i : Int} (h : Agrees x y i (i+3)) :
    xor (first x u c1 i) (first y u c1 i) = xor (x (i-1)) (y (i-1)) := by
  unfold first
  rw [h (i+1) (by omega) (by omega),xorCancelR,xorCancelR,mixDiff h]

private theorem outputDiff {x y : Sig} (u c1 c2 : Sig) {i : Int} (h : Agrees x y (i-1) (i+6)) :
    xor (output x u c1 c2 i) (output y u c1 c2 i) = xor (x (i-2)) (y (i-2)) := by
  have hf : Agrees (first x u c1) (first y u c1) i (i+3) := by
    intro j a b
    apply firstOn
    intro t ht th
    exact h t (by omega) (by omega)
  have hj : Agrees x y (i-1) ((i-1)+3) := fun t ht th => h t ht (by omega)
  unfold output
  rw [h (i-1) (by omega) (by omega),xorCancelR,xorCancelR,mixDiff hf,firstDiff u c1 hj,
      show i-1-1 = i-2 by omega]

theorem pivotLaw (x u c1 c2 : Sig) (i : Int) :
    output x u c1 c2 i = false ↔ x (i-2) = pivot x u c1 c2 i := by
  have same : Agrees x (masked x i) (i-1) (i+6) := by
    intro j h _
    simp [masked,show j ≠ i-2 by omega]
  have hd := outputDiff u c1 c2 same
  change xor (output x u c1 c2 i) (pivot x u c1 c2 i) = xor (x (i-2)) (masked x i (i-2)) at hd
  have hm : masked x i (i-2) = false := by simp [masked]
  rw [hm,Bool.xor_false] at hd
  rw [←hd]
  cases output x u c1 c2 i <;> cases pivot x u c1 c2 i <;> decide

theorem pivotLocal {x y : Sig} (u c1 c2 : Sig) (i : Int)
    (h : ∀ j : Int, i-1 ≤ j → j ≤ i+6 → x j = y j) :
    pivot x u c1 c2 i = pivot y u c1 c2 i := by
  have same : Agrees (masked x i) (masked y i) (i-1) (i+6) := by
    intro j hj jh
    simp [masked,show j ≠ i-2 by omega,h j hj jh]
  have hd := outputDiff u c1 c2 same
  change xor (pivot x u c1 c2 i) (pivot y u c1 c2 i) = xor (masked x i (i-2)) (masked y i (i-2)) at hd
  simpa [masked] using hd

def rawMix (k x : Nat) := rawStep k (x ^^^ rot k 1 x ^^^ rot k (k-1) x)
def init (k w u : Nat) := rot k 1 w ^^^ u
def rawFirst (k w u : Nat) := rawMix k (init k w u) ^^^ rot k 0 w ^^^ (3^(k+1)%2^k)
def row (k w u : Nat) := rawMix k (rawFirst k w u) ^^^ rot k 2 w ^^^ (3^(k+2)%2^k)

lemma initBound {k w u : Nat} (hu : u<2^k) : init k w u < 2^k :=
  Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) hu

lemma rawFirstBound (k w u : Nat) : rawFirst k w u < 2^k :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepBound ..) (Nat.mod_lt _ (by positivity))) (Nat.mod_lt _ (by positivity))

lemma rowBound (k w u : Nat) : row k w u < 2^k :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepBound ..) (Nat.mod_lt _ (by positivity))) (Nat.mod_lt _ (by positivity))

private theorem bitsLin {k x : Nat} (hk : 16 ≤ k) (hx : x < 2^k) (j : Int) :
    bits k (x ^^^ rot k 1 x ^^^ rot k (k-1) x) j = lin (bits k x) j := by
  simp only [bitsXor,bitsRot (show 1<k by omega) hx,bitsRot (show k-1<k by omega) hx,lin]
  have e : j - ((k-1:Nat):Int) = (j+1) - (k:Int) := by omega
  simp [bits,idx,e]

lemma bitsMix {k x : Nat} (hk : 16 ≤ k) (hx : x < 2^k) (j : Int) :
    bits k (rawMix k x) j = mix (bits k x) j := by
  simp only [rawMix,bitsStep (show 0<k by omega),bitsLin hk hx,mix]

lemma keyAt {k w u : Nat} (hk : 16 ≤ k) (hw : w < 2^k) (j : Int) :
    bits k w j = xor (bits k (init k w u) (j+1)) (bits k u (j+1)) := by
  simp [init,bitsXor,bitsRot (show 1<k by omega) hw]

lemma bitsFirst {k w u : Nat} (hk : 16 ≤ k) (hw : w < 2^k) (hu : u < 2^k) :
    bits k (rawFirst k w u) = first (bits k (init k w u)) (bits k u) (ctr k 1) := by
  funext j
  simp only [rawFirst,bitsXor,bitsMix hk (initBound hu),bitsRot (show 0<k by omega) hw,
    Nat.cast_zero,sub_zero,first,ctr]
  rw [keyAt (u:=u) hk hw]

lemma bitsRow {k w u : Nat} (hk : 16 ≤ k) (hw : w < 2^k) (hu : u < 2^k) (i : Int) :
    bits k (row k w u) i = output (bits k (init k w u)) (bits k u) (ctr k 1) (ctr k 2) i := by
  simp only [row,bitsXor,bitsMix hk (rawFirstBound k w u),bitsFirst hk hw hu,
    bitsRot (show 2<k by omega) hw,output,ctr]
  rw [keyAt (u:=u) hk hw,show i-((2:Nat):Int)+1=i-1 by omega]

lemma rowPivot {k w u : Nat} (hk : 16 ≤ k) (hw : w < 2^k) (hu : u < 2^k) (i : Int) :
    bits k (row k w u) i = false ↔ bits k (init k w u) (i-2) =
      pivot (bits k (init k w u)) (bits k u) (ctr k 1) (ctr k 2) i := by
  rw [bitsRow hk hw hu,pivotLaw]

lemma rowRank {k w u t : Nat} (hk : 16 ≤ k) (hw : w < 2^k) (hu : u < 2^k) (ht : t < k) :
    (row k w u).testBit (k-1-t) = false ↔ (init k w u).testBit ((2*k-3-t)%k) =
      pivot (bits k (init k w u)) (bits k u) (ctr k 1) (ctr k 2) ((k:Int)-1-(t:Int)) := by
  have eq : idx k ((k:Int)-1-(t:Int)) = k-1-t := by
    unfold idx
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  have eq2 : idx k ((k:Int)-1-(t:Int)-2) = (2*k-3-t)%k := by
    unfold idx
    rw [←Int.add_emod_left,Int.toNat_emod (by omega) (by omega)]
    congr 1
    omega
  simpa only [bits,eq,eq2] using rowPivot hk hw hu ((k:Int)-1-(t:Int))

lemma rowAllPivot {k w u low : Nat} (hk : 16≤k) (hw : w<2^k) (hu : u<2^k) (hl : low≤k) :
    row k w u < 2^low ↔ ∀ t<k-low, (init k w u).testBit ((2*k-3-t)%k) =
      pivot (bits k (init k w u)) (bits k u) (ctr k 1) (ctr k 2) ((k:Int)-1-(t:Int)) := by
  rw [lowIff (rowBound k w u) hl]
  exact forall_congr' fun t => forall_congr' fun ht => rowRank hk hw hu (by omega)

end P97
end PEqualNP.Outside.L_meta_25497_aux

namespace PEqualNP.Outside.L_meta_25497_aux
open Builder Builder.Bank
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
lemma chiCost {n} {D : Bank n} {u v w : BitFn n} (a : D.Has u) (b : D.Has v) (c : D.Has w) :
    D.Grow 6 (fun E => E.Has (fun x => chi (u x) (v x) (w x))) := by
  apply (inv b).bind (b:=5);intro E e nb
  apply (meet nb (e c)).bind (b:=4);intro F e' g;exact xor2 (e' (e a)) g
lemma staticXor {n} {D : Bank n} {f : BitFn n} (h : D.Has f) (a : Bool) :
    D.Grow 1 (fun E => E.Has (fun x => xor (f x) a)) := by
  cases a with
  | true => simpa using inv h
  | false =>
    refine ⟨D,fun hf=>hf,by omega,?_⟩
    simpa using h
end PEqualNP.Outside.L_meta_25497_aux

namespace PEqualNP.Outside.L_meta_25497_aux
open Builder Builder.Bank

private lemma linOne97 {n} {D : Bank n} (x : MultiSig n) (j : Int)
    (a : D.Has (fun t => x t (j-1))) (b : D.Has (fun t => x t j))
    (c : D.Has (fun t => x t (j+1))) :
    D.Grow 8 (fun E => E.Has (fun t => P97.lin (x t) j)) := by
  apply (xor2 b a).bind (b:=4)
  intro E e h
  exact xor2 h (e c)

private lemma linPair97 {n} {D : Bank n} (x : MultiSig n) (j : Int)
    (h : ∀ l : Int, j-1 ≤ l → l ≤ j+2 → D.Has (fun t => x t l)) :
    D.Grow 12 (fun E => E.Has (fun t => P97.lin (x t) j) ∧
      E.Has (fun t => P97.lin (x t) (j+1))) := by
  apply (xor2 (h (j+1) (by omega) (by omega)) (h j (by omega) (by omega))).bind (b:=8)
  intro E e common
  apply (xor2 common (e (h (j-1) (by omega) (by omega)))).bind (b:=4)
  intro F ef left
  obtain ⟨H,fh,cost,right⟩ := xor2 (ef common) (ef (e (h (j+2) (by omega) (by omega))))
  refine ⟨H,fh,cost,?_,?_⟩
  · have eqv : (fun t => P97.lin (x t) j) =
        (fun t => xor (xor (x t (j+1)) (x t j)) (x t (j-1))) := by
      funext t
      exact (show ∀ a b c : Bool, xor (xor a b) c = xor (xor c a) b by decide) _ _ _
    rw [eqv]
    exact fh left
  · simpa only [P97.lin,show j+1-1=j by omega,show j+1+1=j+2 by omega] using right

private lemma linPairs97 {n} (D : Bank n) (x : MultiSig n) (s : Int) (p : Nat)
    (h : ∀ l : Int, s-1 ≤ l → l ≤ s+2*(p:Int) → D.Has (fun t => x t l)) :
    D.Grow (p*12) (fun E => HasBand E (fun t => P97.lin (x t)) s (2*p)) := by
  induction p with
  | zero =>
    apply Grow.pure
    intro j hj hj'
    omega
  | succ p ih =>
    let j : Int := s+2*(p:Int)
    have old := ih (fun l a b => h l a (by omega))
    rw [Nat.succ_mul]
    apply old.bind
    intro E de band
    obtain ⟨F,ef,cost,ha,hb⟩ := linPair97 (D:=E) x j
      (fun l a b => de (h l (by dsimp [j] at a;omega) (by dsimp [j] at b;omega)))
    refine ⟨F,ef,cost,?_⟩
    intro l hl hr
    by_cases a : l<j
    · exact ef (band l hl (by dsimp [j] at a; omega))
    · have pos : l=j ∨ l=j+1 := by dsimp [j] at a ⊢; omega
      rcases pos with rfl|rfl
      · exact ha
      · exact hb

private lemma mixKey97 {n} {D : Bank n} {a b c l r : BitFn n} (k : Bool)
    (ha : D.Has a) (hb : D.Has b) (hc : D.Has c) (hl : D.Has l) (hr : D.Has r) :
    D.Grow 15 (fun E => E.Has (fun t => xor (xor (chi (a t) (b t) (c t)) (xor (l t) (r t))) k)) := by
  apply (chiCost ha hb hc).bind (b:=9)
  intro E e hchi
  apply (xor2 (e hl) (e hr)).bind (b:=5)
  intro F ef key
  apply (xor2 (ef hchi) key).bind (b:=1)
  intro H _ hout
  exact staticXor hout k

theorem pivot2Cost {n} (D : Bank n) (x u : MultiSig n) (a b : Sig) (i : Int)
    (hx : ∀ j : Int, i-1 ≤ j → j ≤ i+6 → D.Has (fun t => x t j))
    (hu : ∀ j : Int, D.Has (fun t => u t j)) :
    D.Grow 154 (fun E => E.Has (fun t => P97.pivot (x t) (u t) a b i)) := by
  let z : MultiSig n := fun t => P97.masked (x t) i
  let f : MultiSig n := fun t => P97.first (z t) (u t) a
  have raw (j : Int) (lo : i-1 ≤ j) (hi : j ≤ i+6) : D.Has (fun t => z t j) := by
    simpa only [z,P97.masked,if_neg (by omega : j ≠ i-2)] using hx j lo hi
  have border : D.Grow 4 (fun E => E.Has (fun t => P97.lin (z t) (i-1))) := by
    have e : (fun t => P97.lin (z t) (i-1)) = (fun t => xor (z t (i-1)) (z t i)) := by
      funext t
      have hz : z t (i-1-1) = false := by simp [z,P97.masked,show i-1-1=i-2 by omega]
      simp [P97.lin,hz,show i-1+1=i by omega]
    rw [e]
    exact xor2 (raw (i-1) (by omega) (by omega)) (raw i (by omega) (by omega))
  apply border.bind (b:=150)
  intro E de h0
  apply (linPairs97 E z i 3 (fun j lo hi => de (raw j lo (by omega)))).bind (b:=114)
  intro F ef six
  have seven (j : Int) (lo : i-1 ≤ j) (hi : j ≤ i+5) : F.Has (fun t => P97.lin (z t) j) := by
    by_cases hz : j=i-1
    · rw [hz]; exact ef h0
    · exact six j (by omega) (by omega)
  have stage : F.Grow (5*15) (fun E => HasBand E f (i-1) 5) := by
    apply bandGrow
    intro H fh j lo hi
    apply mixKey97 (a j)
    · exact fh (seven j (by omega) (by omega))
    · exact fh (seven (j+1) (by omega) (by omega))
    · exact fh (seven (j+2) (by omega) (by omega))
    · exact fh (ef (de (raw (j+1) (by omega) (by omega))))
    · exact fh (ef (de (hu (j+1))))
  apply stage.bind (b:=39)
  intro H fh hb
  have outer : H.Grow (3*8) (fun E => HasBand E (fun t => P97.lin (f t)) i 3) := by
    apply bandGrow
    intro K hk j lo hi
    exact linOne97 f j (hk (hb (j-1) (by omega) (by omega)))
      (hk (hb j (by omega) (by omega))) (hk (hb (j+1) (by omega) (by omega)))
  apply outer.bind (b:=15)
  intro K hk ho
  apply mixKey97 (b i)
  · exact ho i (by omega) (by omega)
  · exact ho (i+1) (by omega) (by omega)
  · exact ho (i+2) (by omega) (by omega)
  · exact hk (fh (ef (de (raw (i-1) (by omega) (by omega)))))
  · exact hk (fh (ef (de (hu (i-1)))))

end PEqualNP.Outside.L_meta_25497_aux

open PEqualNP.Outside.L_meta_25497_aux in
theorem PEqualNP.Outside.L_meta_25497 : ∀ k : Nat, 16 ≤ k →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let constant := fun (j : Nat) => 3 ^ (k + j) % 2 ^ k
  let rowMix := fun (x : Nat) => step (x ^^^ rot 1 x ^^^ rot (k - 1) x)
  let colMix := fun (z : Nat) => step (z ^^^ rot 2 z ^^^ rot (k - 2) z)
  let first := fun (rowKey rowName : Nat) =>
    let x0 := rot 1 rowKey ^^^ rowName
    let x1 := rowMix x0 ^^^ rot 0 rowKey ^^^ constant 1
    rowMix x1 ^^^ rot 2 rowKey ^^^ constant 2
  let second := fun (colKey colName : Nat) =>
    let z0 := rot 3 colKey ^^^ colName
    let z1 := colMix z0 ^^^ rot 4 colKey ^^^ constant 3
    colMix z1 ^^^ rot 7 colKey ^^^ constant 4
  let slots := 2 ^ (k - (k + 1) / 2)
  let graph : Fin (2 ^ k) → Fin (2 ^ k) → Bool := fun row col =>
    (List.range (2 ^ k)).any (fun w =>
      decide (first w row.val < slots) && decide (second w col.val < slots))
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + k) C ∧
    C.size ≤ slots * (130 * k) ∧
    ∀ bits : Fin (k + k) → Bool,
      C.eval (List.ofFn bits) = PEqualNP.Represents.adjFun (k := k) (l := k) graph bits := by
  intro k hk
  exact S97.whole (p:=P97.pivot) hk (fun B x u a b i hx hu=>pivot2Cost B x u a b i hx hu)
    (fun a b u c e i he=>P97.pivotLocal u c e i he)
    (fun w u low hw hu hl=>P97.rowAllPivot hk hw hu hl)

