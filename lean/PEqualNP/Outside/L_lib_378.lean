import PEqualNP.Defs
namespace PEqualNP.Outside.L_lib_378_aux
abbrev Sig := Int → Bool
def chi (a b c : Bool) := xor a (!b && c)
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

def Agrees (x y : Sig) (lo hi : Int) : Prop := ∀ j, lo≤j → j≤hi → x j=y j

def lin (x : Sig) (i : Int) :=
  xor (xor (x i) (x (i-1))) (x (i+1))

def mix (x : Sig) (i : Int) :=
  chi (lin x i) (lin x (i+1)) (lin x (i+2))

def first (x u c1 : Sig) (j : Int) :=
  xor (xor (mix x j) (xor (x (j+1)) (u (j+1)))) (c1 j)

def output (x u c1 c2 : Sig) (i : Int) :=
  xor (xor (mix (first x u c1) i) (xor (x (i-1)) (u (i-1)))) (c2 i)

theorem xorCancelR (a b c : Bool) :
    xor (xor a c) (xor b c) = xor a b := by
  cases a <;> cases b <;> cases c <;> rfl

theorem xorCancelL (a b c : Bool) :
    xor (xor c a) (xor c b) = xor a b := by
  cases a <;> cases b <;> cases c <;> rfl

theorem linOn {x y : Sig} {i : Int} (h : Agrees x y (i-1) (i+1)) :
    lin x i = lin y i := by
  unfold lin
  rw [h i (by omega) (by omega), h (i-1) (by omega) (by omega), h (i+1) (by omega) (by omega)]

theorem mixOn {x y : Sig} {i : Int} (h : Agrees x y (i-1) (i+3)) :
    mix x i = mix y i := by
  have l (j : Int) (a : i ≤ j) (b : j ≤ i+2) : lin x j = lin y j :=
    linOn (fun t ht th => h t (by omega) (by omega))
  unfold mix
  rw [l i (by omega) (by omega), l (i+1) (by omega) (by omega), l (i+2) (by omega) (by omega)]

theorem mixDiff {x y : Sig} {i : Int} (h : Agrees x y i (i+3)) :
    xor (mix x i) (mix y i) = xor (x (i-1)) (y (i-1)) := by
  have l (j : Int) (a : i < j) (b : j ≤ i+2) : lin x j = lin y j :=
    linOn (fun t ht th => h t (by omega) (by omega))
  unfold mix chi
  rw [l (i+1) (by omega) (by omega), l (i+2) (by omega) (by omega),xorCancelR]
  unfold lin
  rw [h i (by omega) (by omega),h (i+1) (by omega) (by omega),xorCancelR,xorCancelL]

theorem firstOn {x y : Sig} (u c1 : Sig) {i : Int} (h : Agrees x y (i-1) (i+3)) :
    first x u c1 i = first y u c1 i := by
  unfold first
  rw [mixOn h,h (i+1) (by omega) (by omega)]

theorem firstDiff {x y : Sig} (u c1 : Sig) {i : Int} (h : Agrees x y i (i+3)) :
    xor (first x u c1 i) (first y u c1 i) = xor (x (i-1)) (y (i-1)) := by
  unfold first
  rw [h (i+1) (by omega) (by omega),xorCancelR,xorCancelR,mixDiff h]

theorem outputDiff {x y : Sig} (u c1 c2 : Sig) {i : Int} (h : Agrees x y (i-1) (i+6)) :
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


def initWord (k u w:Nat) := rot k 1 w ^^^ u
def rawLin1 (k x:Nat) := x ^^^ rot k 1 x ^^^ rot k (k-1) x
def roundWord (k w j cx x:Nat) := rawStep k (rawLin1 k x) ^^^ rot k (2*j) w ^^^ cx

lemma linBits {k x:Nat} (hk:2≤k) (hx:x<2^k) :
 bits k (rawLin1 k x) = lin (bits k x) := by
 funext j
 simp only [rawLin1,lin,bitsXor,bitsRot (show 1<k by omega) hx,bitsRot (show k-1<k by omega) hx]
 rw [show j-((k-1:Nat):Int)=(j+1)-(k:Int) by omega]
 simp [bits,idx]

lemma roundBound {k cx:Nat} (w j x:Nat) (hc:cx<2^k) : roundWord k w j cx x < 2^k :=
 Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepBound ..) (Nat.mod_lt _ (by positivity))) hc

def leftSpan (t : Nat) : Nat := max t (2*t-3)

def stages (x u : Sig) (cs : Nat → Sig) : Nat → Sig
  | 0 => x
  | t+1 => fun i =>
    let j := i+1-2*(t:Int)
    xor (xor (mix (stages x u cs t) i) (xor (x j) (u j))) (cs (t+1) i)

private theorem stageAgree {t : ℕ} {x y : Sig} (u : Sig) (cs : ℕ → Sig) (i : Int)
    (h : Agrees x y (i-(leftSpan t:Int)) (i+3*(t:Int))) :
    stages x u cs t i = stages y u cs t i := by
  induction t generalizing i with
  | zero => exact h i (by simp [leftSpan]) (by simp)
  | succ t ih =>
    have cover : (leftSpan t:Int)+1 ≤ (leftSpan (t+1):Int) := by
      dsimp [leftSpan]
      omega
    have lo : i-(leftSpan (t+1):Int) ≤ i+1-2*(t:Int) := by
      dsimp [leftSpan]
      omega
    have eqmix : mix (stages x u cs t) i = mix (stages y u cs t) i := by
      apply mixOn
      intro j h1 h2
      apply ih
      intro z hz zh
      exact h z (by omega) (by omega)
    simp only [stages,eqmix,h (i+1-2*(t:Int)) lo (by omega)]

theorem stageDiff {r : Nat} (hr : 1 ≤ r) (three : r ≠ 3) {x y : Sig}
    (u : Sig) (cs : Nat → Sig) (i : Int)
    (h : Agrees x y (i-(leftSpan r:Int)+1) (i+3*(r:Int))) :
    xor (stages x u cs r i) (stages y u cs r i) =
      xor (x (i-(leftSpan r:Int))) (y (i-(leftSpan r:Int))) := by
  by_cases r1 : r=1
  · subst r
    have hs (z : Sig) : stages z u cs 1 = first z u (cs 1) := by
      funext l; simp [stages,first]
    rw [hs,hs]
    have result := firstDiff u (cs 1) (i:=i) (x:=x) (y:=y)
    change xor (first x u (cs 1) i) (first y u (cs 1) i) = xor (x (i-1)) (y (i-1))
    apply result
    intro j jl jh
    exact h j (by norm_num [leftSpan]; omega) (by norm_num; omega)
  by_cases r2 : r=2
  · subst r
    have hs (z : Sig) : stages z u cs 2 = output z u (cs 1) (cs 2) := by
      have one : stages z u cs 1 = first z u (cs 1) := by funext j; simp [stages,first]
      funext l
      change xor (xor (mix (stages z u cs 1) l)
          (xor (z (l+1-2*(1:Int))) (u (l+1-2*(1:Int))))) (cs 2 l) = _
      rw [one,show l+1-2*(1:Int)=l-1 by omega]
      rfl
    rw [hs,hs]
    change xor (output x u (cs 1) (cs 2) i) (output y u (cs 1) (cs 2) i) =
      xor (x (i-2)) (y (i-2))
    apply outputDiff u (cs 1) (cs 2)
    intro j jl jh
    exact h j (by norm_num [leftSpan]; omega) (by norm_num; omega)
  cases r with
  | zero => omega
  | succ t =>
    have large : 3≤t := by omega
    have flank : (leftSpan (t+1) : Int) = 2*(t:Int)-1 := by dsimp [leftSpan]; omega
    have old : (leftSpan t : Int) = 2*(t:Int)-3 := by dsimp [leftSpan]; omega
    have mixEq : mix (stages x u cs t) i = mix (stages y u cs t) i := by
      apply mixOn
      intro j jl jh
      apply stageAgree
      intro z zl zh
      exact h z (by omega) (by omega)
    have pi : i+1-2*(t:Int) = i-(leftSpan (t+1):Int) := by omega
    simp only [stages,mixEq,pi,xorCancelR,xorCancelL]

def stateWord (k u w : Nat) (c : Nat → Fin (2^k)) (t : Nat) :=
  (List.range t).foldl (fun prev j => roundWord k w j (c (j+1)).val prev) (initWord k u w)

theorem stateSucc (k u w : Nat) (c : Nat → Fin (2^k)) (t : Nat) :
    stateWord k u w c (t+1) = roundWord k w t (c (t+1)).val (stateWord k u w c t) := by
  simp [stateWord,List.range_succ]

theorem stateBound (k u w : Nat) (c : Nat → Fin (2^k)) (hu:u<2^k) (t : Nat) :
    stateWord k u w c t < 2^k := by
  cases t with
  | zero => exact Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) hu
  | succ t => rw [stateSucc]; exact roundBound _ _ _ (c _).isLt

theorem injBits {k w : Nat} (u t : Nat) (hk : 1 < k) (hw:w<2^k) (j : Int) :
    bits k w (j - ((2*t:Nat):Int)) =
      xor (bits k (initWord k u w) (j+1-2*(t:Int))) (bits k u (j+1-2*(t:Int))) := by
  rw [initWord,bitsXor,bitsRot hk hw]
  rw [show j+1-2*(t:Int)-(1:Nat)=j-((2*t:Nat):Int) by omega]
  cases bits k w (j-((2*t:Nat):Int)) <;> cases bits k u (j+1-2*(t:Int)) <;> rfl

theorem stateBits {k w u : Nat} (c : Nat → Fin (2^k)) (hk:2≤k) (hw:w<2^k) (hu:u<2^k)
    (t : Nat) (ht:2*t<k) :
    bits k (stateWord k u w c t) =
      stages (bits k (initWord k u w)) (bits k u) (fun j => bits k (c j).val) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext j
    rw [stateSucc]
    simp only [roundWord,bitsXor,bitsStep (show 0<k by omega),
      linBits hk (stateBound k u w c hu t),bitsRot (show 2*t<k by omega) hw,
      ih (by omega),stages,mix]
    rw [injBits u t (by omega) hw]

theorem cyclicPivot {k i L : Nat} (positive : 0<k) (le : L ≤ k) :
    idx k ((i:Int)-(L:Int)) = (i+k-L)%k := by
  unfold idx
  rw [← Int.add_emod_right ((i:Int)-(L:Int)) (k:Int)]
  rw [show (i:Int)-(L:Int)+(k:Int) = ((i+k-L:Nat):Int) by omega]
  rw [Int.toNat_emod (by omega) (by omega)]
  simp

theorem cyclicWindow {k i L width x y : Nat} (positive : 0<k) (le : L ≤ k)
    (agree : ∀ j : Fin width, x.testBit (((i+k-L)%k+1+j.val)%k) =
      y.testBit (((i+k-L)%k+1+j.val)%k)) :
    Agrees (bits k x) (bits k y) ((i:Int)-(L:Int)+1) ((i:Int)-(L:Int)+(width:Int)) := by
  intro z h₁ h₂
  let d : Nat := (z-((i:Int)-(L:Int)+1)).toNat
  have cast : (d:Int) = z-((i:Int)-(L:Int)+1) := by dsimp [d]; omega
  have hd : d < width := by omega
  have pos := cyclicPivot (i:=i) positive le
  have atIndex : ((i+k-L)%k+1+d)%k = idx k z := by
    rw [Nat.add_assoc,←pos,idxAdd positive]
    congr 1
    omega
  simpa only [bits, ← atIndex] using agree ⟨d,hd⟩

end PEqualNP.Outside.L_lib_378_aux
open PEqualNP.Outside.L_lib_378_aux in
theorem PEqualNP.Outside.L_lib_378 :
∀ (k r : Nat) (u : Fin (2 ^ k)) (c : Nat → Fin (2 ^ k)),
  1 ≤ r → r ≠ 3 →
  let left := max r (2 * r - 3)
  let width := left + 3 * r
  width < k →
  let rot := fun (s w : Nat) =>
    ((w <<< (s % k)) ||| (w >>> (k - s % k))) % 2 ^ k
  let step := fun (x : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (x.testBit i)
        (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))).toNat <<< i)) 0
  let start := fun (w : Fin (2 ^ k)) => rot 1 w.val ^^^ u.val
  let state := fun (w : Fin (2 ^ k)) =>
    (List.range r).foldl (fun prev j =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * j) w.val ^^^ (c (j + 1)).val)
      (start w)
  ∀ (i : Fin k) (w v : Fin (2 ^ k)),
    let p := (i.val + k - left) % k
    (∀ j : Fin width,
      (start w).testBit ((p + 1 + j.val) % k) =
      (start v).testBit ((p + 1 + j.val) % k)) →
    xor ((state w).testBit i.val) ((state v).testBit i.val) =
      xor ((start w).testBit p) ((start v).testBit p) := by
  intro k r u c hr hn
  dsimp only
  intro window i w v agree
  change leftSpan r + 3*r < k at window
  have hk : 2≤k := by omega
  have wide : 2*r<k := by omega
  let L := leftSpan r
  have low : L ≤ k := by dsimp [L];omega
  have turn : idx k ((i.val:Int)-(L:Int))=(i.val+k-L)%k := cyclicPivot (by omega) low
  have atI : idx k (i.val:Int)=i.val := by
    unfold idx
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    rfl
  change xor ((stateWord k u.val w.val c r).testBit i.val)
      ((stateWord k u.val v.val c r).testBit i.val) =
    xor ((initWord k u.val w.val).testBit ((i.val+k-L)%k))
      ((initWord k u.val v.val).testBit ((i.val+k-L)%k))
  change ∀ j : Fin (L+3*r), (initWord k u.val w.val).testBit (((i.val+k-L)%k+1+j.val)%k) =
    (initWord k u.val v.val).testBit (((i.val+k-L)%k+1+j.val)%k) at agree
  have ha := cyclicWindow (i:=i.val) (by omega:0<k) low agree
  have windows : Agrees (bits k (initWord k u.val w.val)) (bits k (initWord k u.val v.val))
      ((i.val:Int)-(leftSpan r:Int)+1) ((i.val:Int)+3*(r:Int)) := by
    intro z a b
    exact ha z a (by dsimp [L]; omega)
  have diff := stageDiff hr hn (bits k u.val) (fun t => bits k (c t).val) i.val windows
  rw [←stateBits c hk w.isLt u.isLt r wide,←stateBits c hk v.isLt u.isLt r wide] at diff
  simpa only [bits,atI,show idx k ((i.val:Int)-(leftSpan r:Int))=(i.val+k-L)%k from turn] using diff
