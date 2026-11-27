import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_25495_aux
abbrev Sig := Int → Bool
def chi (a b c : Bool) := xor a (!b && c)
def linear (x : Sig) (i : Int) := xor (xor (x i) (x (i-2))) (x (i+2))
def sweep (x : Sig) (i : Int) := chi (linear x i) (linear x (i+1)) (linear x (i+2))
def stage (x z v a : Sig) (d : Int) (i : Int) :=
  xor (xor (sweep x i) (xor (z (i-d)) (v (i-d)))) (a i)
def Agrees (x y : Sig) (lo hi : Int) : Prop := ∀ j, lo ≤ j → j ≤ hi → x j = y j
lemma sweepEq {x y : Sig} {i : Int} (h : Agrees x y (i-2) (i+4)) : sweep x i = sweep y i := by
  have lh (z : Int) (hl : i ≤ z) (hr : z ≤ i+2) : linear x z = linear y z := by
    unfold linear
    rw [h z (by omega) (by omega),h (z-2) (by omega) (by omega),h (z+2) (by omega) (by omega)]
  unfold sweep
  rw [lh i (by omega) (by omega),lh (i+1) (by omega) (by omega),lh (i+2) (by omega) (by omega)]
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
end PEqualNP.Outside.L_meta_25495_aux


namespace PEqualNP.Outside.L_meta_25495_aux
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
def ctr (k r : Nat) := bits k (3^(k+r)%2^k)
end PEqualNP.Outside.L_meta_25495_aux



namespace PEqualNP.Outside.L_meta_25495_aux
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
end PEqualNP.Outside.L_meta_25495_aux


namespace PEqualNP.Outside.L_meta_25495_aux

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

end PEqualNP.Outside.L_meta_25495_aux

namespace PEqualNP.Outside.L_meta_25495_aux
namespace Sweep
def seedBits (k free : Nat) (z : Nat → Bool) : Fin (2^(k-free)) :=
  let l := List.ofFn (fun j : Fin (k-free) => z (free+j.val))
  let v := BitVec.ofBoolListLE l
  ⟨v.toNat, by simpa [v,l] using v.isLt⟩

lemma readSeed (k free : Nat) (z : Nat → Bool) {i : Nat} (hi : i < k) (h : free ≤ i) :
    (seedBits k free z).val.testBit (i-free) = z i := by
  simp only [seedBits, BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simp; omega)]
  simp [Nat.add_sub_of_le h]

end Sweep
end PEqualNP.Outside.L_meta_25495_aux

namespace PEqualNP.Outside.L_meta_25495_aux

def colSignal95 (k r : Nat) (z v : Sig) : Nat → Sig
  | 0 => z
  | t+1 => stage (colSignal95 k r z v t) z v (ctr k (r+(t+1))) (3*(t+1)-2 : Nat)

def col95 (k r w v : Nat) : Nat → Nat
  | 0 => rInit k w v
  | t+1 => roundN k w (r+(t+1)) (3*(t+1)-2) (col95 k r w v t)

lemma col95_bound {k : Nat} (r w : Nat) {v : Nat} (hv : v<2^k) (t : Nat) :
    col95 k r w v t < 2^k := by
  cases t with
  | zero => exact Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) hv
  | succ t => exact roundB ..

lemma col95_bits {k r w v t : Nat} (hr : 3≤r) (hk : 7*r-1≤k) (ht : t≤r)
    (hw : w<2^k) (hv : v<2^k) :
    bits k (col95 k r w v t) = colSignal95 k r (bits k (rInit k w v)) (bits k v) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change bits k (roundN k w _ _ _) = stage _ _ _ _ _
    rw [roundEq (v:=v) (by omega) hw (by omega) (col95_bound r w hv t),ih (by omega)]
    rfl

lemma col95_fold (k r w v t : Nat) : (List.range t).foldl (fun x i =>
    rawStep k (rawLin k x) ^^^ rot k (3*(i+1)+1) w ^^^ (3^(k+(r+(i+1)))%2^k))
    (rInit k w v) = col95 k r w v t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,ih,col95,roundN]
    rw [show 3*(t+1)-2+3=3*(t+1)+1 by omega]

lemma col95_low {k r w v low : Nat} (hr : 3≤r) (hk : 7*r-1≤k)
    (hw : w<2^k) (hv : v<2^k) (hl : low≤k) :
    col95 k r w v r < 2^low ↔
    ∀ t<k-low, colSignal95 k r (bits k (rInit k w v)) (bits k v) r ((k:Int)-1-(t:Int))=false := by
  rw [lowIff (col95_bound r w hv r) hl,←col95_bits hr hk (Nat.le_refl r) hw hv]
  apply forall_congr';intro t
  apply forall_congr';intro ht
  have h : idx k ((k:Int)-1-t)=k-1-t := by
    unfold idx
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  simp only [bits,h]

end PEqualNP.Outside.L_meta_25495_aux

namespace PEqualNP.Outside.L_meta_25495_aux

private theorem roundsAgree95 {k r : Nat} {z z' v : Sig} {lo hi : Int}
    (agree : Agrees z z' lo hi) (t : Nat) (i : Int)
    (hlinear : lo ≤ i-2*(t:Int)) (hkey : lo ≤ i-(3*(t:Int)-2))
    (hright : i+4*(t:Int) ≤ hi) :
    colSignal95 k r z v t i = colSignal95 k r z' v t i := by
  induction t generalizing i with
  | zero => exact agree i (by omega) (by omega)
  | succ t ih =>
    have same : sweep (colSignal95 k r z v t) i = sweep (colSignal95 k r z' v t) i := by
      apply sweepEq
      intro j hj hj'
      exact ih j (by omega) (by omega) (by omega)
    have key : z (i-((3*(t+1)-2 : Nat):Int)) = z' (i-((3*(t+1)-2 : Nat):Int)) :=
      agree _ (by omega) (by omega)
    simp only [colSignal95,stage,same,key]

theorem pivotTransfer95 {k r : Nat} (hr : 3 ≤ r) {z z' v : Sig} (i : Int)
    (eq : Agrees z z' (i-((3*r-2 : Nat):Int)+1) (i+4*(r:Int)))
    (p : colSignal95 k r z v r i = false) (p' : colSignal95 k r z' v r i = false) :
    z (i-((3*r-2 : Nat):Int)) = z' (i-((3*r-2 : Nat):Int)) := by
  cases r with
  | zero => omega
  | succ t =>
    have same : sweep (colSignal95 k (t+1) z v t) i = sweep (colSignal95 k (t+1) z' v t) i := by
      apply sweepEq
      intro j hj hj'
      exact roundsAgree95 eq t j (by omega) (by omega) (by omega)
    simp only [colSignal95,stage,same] at p p'
    exact (show ∀ s x y d e : Bool,
      xor (xor s (xor x d)) e = false → xor (xor s (xor y d)) e = false → x = y by decide)
      _ _ _ _ _ p p'

end PEqualNP.Outside.L_meta_25495_aux

namespace PEqualNP.Outside.L_meta_25495_aux

def ranked95 (k w : Nat) (c : Int) (t : Nat) : Bool := bits k w (c-(t:Int))

lemma lookup95 {k : Nat} (hk : 0<k) (w : Nat) (c j : Int) :
    ranked95 k w c (idx k (c-j)) = bits k w j := by
  have pos : 0<(k:Int) := by omega
  have ec : ((idx k (c-j):Nat):Int) = (c-j)%(k:Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt pos))
  unfold ranked95 bits idx
  change w.testBit ((c-((idx k (c-j):Nat):Int))%(k:Int)).toNat = _
  rw [ec,Int.sub_emod c ((c-j)%(k:Int)),Int.emod_emod,←Int.sub_emod]
  rw [show c-(c-j)=j by omega]

lemma prior95 {k q t len : Nat} (hq : q+len≤k) (ht : t<q) {j : Int}
    (lo : (t:Int)-(len:Int) ≤ j) (hi : j < (t:Int)) :
    idx k j < t ∨ q ≤ idx k j := by
  by_cases hn : 0≤j
  · left
    unfold idx
    rw [Int.emod_eq_of_lt hn (by omega)]
    omega
  · right
    unfold idx
    rw [←Int.add_emod_left,Int.emod_eq_of_lt (by omega) (by omega)]
    omega

lemma rankedInject95 {k z z' : Nat} (hk : 0<k) (hz : z<2^k) (hz' : z'<2^k)
    (c : Int) (agree : ∀ t<k, ranked95 k z c t = ranked95 k z' c t) : z=z' := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<k
  · have e := agree (idx k (c-(j:Int))) (idxlt hk _)
    rw [lookup95 hk,lookup95 hk] at e
    have hj' : idx k (j:Int)=j := by
      unfold idx
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      rfl
    simpa only [bits,hj'] using e
  · have h : 2^k≤2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hz h),Nat.testBit_lt_two_pow (lt_of_lt_of_le hz' h)]

lemma rankInd95 {q k : Nat} (a b : Nat → Bool)
    (seed : ∀ j<k, q≤j → a j=b j)
    (step : ∀ t<q, (∀ j<k, j<t ∨ q≤j → a j=b j) → a t=b t) : ∀ j<k, a j=b j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases lo : j<q
    · apply step j lo
      rintro l hl (lt|high)
      · exact ih l lt hl
      · exact seed l hl high
    · exact seed j hj (by omega)

end PEqualNP.Outside.L_meta_25495_aux


namespace PEqualNP.Outside.L_meta_25495_aux

lemma passInject95 {k r v w w' : Nat} (hr : 3≤r) (hk : 7*r-1≤k) (hv : v<2^k)
    (hw : w<2^k) (hw' : w'<2^k)
    {h q : Nat} (hh : h≤k) (qh : q≤h) (qk : q+(7*r-2)≤k)
    (test : col95 k r w v r < 2^(k-h)) (test' : col95 k r w' v r < 2^(k-h))
    (seed : ∀ j<k, q≤j →
      ranked95 k (rInit k w v) ((k:Int)-1-((3*r-2:Nat):Int)) j =
      ranked95 k (rInit k w' v) ((k:Int)-1-((3*r-2:Nat):Int)) j) : w=w' := by
  let z := rInit k w v
  let z' := rInit k w' v
  let c := (k:Int)-1-((3*r-2:Nat):Int)
  have pos : 0<k := by omega
  have a := (col95_low hr hk hw hv (show k-h≤k by omega)).mp test
  have b := (col95_low hr hk hw' hv (show k-h≤k by omega)).mp test'
  have agr : ∀ j<k, ranked95 k z c j = ranked95 k z' c j := by
    apply rankInd95 _ _ seed
    intro t ht prev
    let i := (k:Int)-1-(t:Int)
    have hck : c-(t:Int) = i-((3*r-2:Nat):Int) := by dsimp [c,i]; omega
    unfold ranked95
    rw [hck]
    apply pivotTransfer95 (k:=k) (v:=bits k v) hr i _ (a t (by omega)) (b t (by omega))
    intro j lo hi
    rw [←lookup95 pos z c j,←lookup95 pos z' c j]
    apply prev _ (idxlt pos _)
    apply prior95 (len:=7*r-2) qk ht <;> dsimp [c,i] at * <;> omega
  have hz : z<2^k := Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) hv
  have hz' : z'<2^k := Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) hv
  have same := rankedInject95 pos hz hz' c agr
  have e := congrArg (fun t => recoverKey k t v) same
  change recoverKey k (rInit k w v) v = recoverKey k (rInit k w' v) v at e
  rwa [recoverInit (by omega) hw,recoverInit (by omega) hw'] at e

theorem count95 (k r v : Nat) (hr : 3≤r) (hk : 7*r-1≤k) (hv : v<2^k) :
    ((List.range (2^k)).filter (fun w => decide (col95 k r w v r < 2^(k-(k+1)/2)))).length
      ≤ 2^(max (k-(k+1)/2) (7*r-2)) := by
  classical
  let h := (k+1)/2
  let q := min h (k-(7*r-2))
  let c := (k:Int)-1-((3*r-2:Nat):Int)
  let words := (List.range (2^k)).filter (fun w => decide (col95 k r w v r < 2^(k-h)))
  let S := words.toFinset
  let code (w : S) := Sweep.seedBits k q (ranked95 k (rInit k w.val v) c)
  have mem (w : S) : w.val<2^k ∧ col95 k r w.val v r < 2^(k-h) := by
    have e : w.val ∈ words := List.mem_toFinset.mp w.property
    simpa [words] using e
  have hi : Function.Injective code := by
    intro w w' e
    apply Subtype.ext
    apply passInject95 hr hk hv (mem w).1 (mem w').1 (h:=h) (q:=q)
      (by dsimp [h];omega) (min_le_left ..) (by dsimp [h,q];omega) (mem w).2 (mem w').2
    intro j hj hq
    have he := congrArg (fun s : Fin (2^(k-q)) => s.val.testBit (j-q)) e
    dsimp only [code] at he
    simpa only [Sweep.readSeed k q _ hj hq] using he
  have ca := Fintype.card_le_of_injective code hi
  have hd : words.Nodup := List.nodup_range.filter _
  have eq : k-q=max (k-h) (7*r-2) := by dsimp [q,h];omega
  change words.length ≤ 2^max (k-h) (7*r-2)
  simpa only [Fintype.card_coe,S,List.toFinset_card_of_nodup hd,Fintype.card_fin,eq] using ca

end PEqualNP.Outside.L_meta_25495_aux

open PEqualNP.Outside.L_meta_25495_aux in
theorem PEqualNP.Outside.L_meta_25495 : ∀ (k r : Nat), 3 ≤ r → 7 * r - 1 ≤ k → ∀ v : Fin (2 ^ k),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let constant := fun (j : Nat) => 3 ^ (k + j) % 2 ^ k
  let second := fun (colKey colName : Nat) =>
    (List.range r).foldl (fun colState colIndex =>
      step (colState ^^^ rot 2 colState ^^^ rot (k - 2) colState) ^^^
        rot (3 * (colIndex + 1) + 1) colKey ^^^ constant (r + (colIndex + 1)))
      (rot 3 colKey ^^^ colName)
  let h := (k + 1) / 2
  ((List.range (2 ^ k)).filter (fun w => decide (second w v.val < 2 ^ (k - h)))).length
    ≤ 2 ^ (max (k - h) (7 * r - 2)) := by
  intro k r hr hk v
  dsimp only
  change ((List.range (2^k)).filter (fun w => decide ((List.range r).foldl (fun x i =>
    rawStep k (rawLin k x) ^^^ rot k (3*(i+1)+1) w ^^^ (3^(k+(r+(i+1)))%2^k))
    (rInit k w v.val) < 2^(k-(k+1)/2)))).length ≤ _
  simpa only [col95_fold] using count95 k r v.val hr hk v.isLt
