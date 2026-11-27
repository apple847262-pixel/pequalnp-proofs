import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25507_aux.Wrap507.Row.Impl

namespace Sweep25484

def mix (x : Nat → Bool) (n : Nat) : Bool :=
  xor (xor (x n) (x (n+1))) (x (n+2))

def core (x : Nat → Bool) (n : Nat) : Bool :=
  xor (mix x n) (!(mix x (n+1)) && mix x (n+2))

theorem core_congr {x y : Nat → Bool} {n : Nat}
    (H : ∀ i, n ≤ i → i ≤ n+4 → x i = y i) : core x n = core y n := by
  unfold core mix
  rw [H n (by omega) (by omega), H (n+1) (by omega) (by omega),
    H (n+2) (by omega) (by omega), H (n+3) (by omega) (by omega),
    H (n+4) (by omega) (by omega)]

def row (r : Nat) (u : Nat → Bool) (c : Nat → Nat → Bool)
    (x : Nat → Bool) : Nat → Nat → Bool
  | 0, n => x (n+(r-3))
  | t+1, n => xor (xor (core (row r u c x t) n)
     (xor (x (n+(r-(t+1)))) (u (n+(r-(t+1)))))) (c (t+1) n)

theorem row_congr {r} (hr : 4 ≤ r) {u c x y} {t n : Nat} (ht : t < r)
    (H : ∀ i, n+1 ≤ i → i ≤ n+(r-3)+4*t → x i = y i) :
    row r u c x t n = row r u c y t n := by
  induction t generalizing n with
  | zero => simp only [row]; apply H <;> omega
  | succ t IH =>
    simp only [row]
    rw [H (n+(r-(t+1))) (by omega) (by omega)]
    congr 2
    apply core_congr
    intro i hi hj
    apply IH (by omega)
    intro j hj₁ hj₂
    apply H j <;> omega

def pivot (r : Nat) (u : Nat → Bool) (c : Nat → Nat → Bool)
    (x : Nat → Bool) (n : Nat) : Bool :=
  xor (xor (core (row r u c x (r-1)) n) (u n)) (c r n)

theorem pivot_congr {r} (hr : 4 ≤ r) {u c x y n}
    (H : ∀ i, n+1 ≤ i → i ≤ n+(5*r-3) → x i = y i) :
    pivot r u c x n = pivot r u c y n := by
  unfold pivot
  congr 2
  apply core_congr
  intro i hi hj
  apply row_congr hr (by omega)
  intro j hj₁ hj₂
  apply H j <;> omega

theorem row_zero_iff {r} (hr : 4 ≤ r) {u c x n} :
    row r u c x r n = false ↔ x n = pivot r u c x n := by
  have he : r-1+1 = r := by omega
  have heq : row r u c x r n = xor (xor (core (row r u c x (r-1)) n)
      (xor (x n) (u n))) (c r n) := by
    conv_lhs => rw [← he]; unfold row
    simp only [he, Nat.sub_self, Nat.add_zero]
  rw [heq]
  unfold pivot
  cases x n <;> cases u n <;> cases c r n <;>
    cases core (row r u c x (r-1)) n <;> decide

end Sweep25484

namespace BitBridge

def stepBit (k word i : Nat) : Bool :=
  word.testBit i ^^ (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))

def wordStep (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc i => if stepBit k word i then acc ||| 2 ^ i else acc) 0

theorem testBit_foldl_set (p : Nat → Bool) (xs : List Nat) (acc i : Nat) :
    (xs.foldl (fun a j => if p j then a ||| 2 ^ j else a) acc).testBit i =
      (acc.testBit i || (decide (i ∈ xs) && p i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons j xs ih =>
    simp only [List.foldl_cons, ih]
    by_cases hji : j = i
    · subst j
      cases hp : p i <;> simp [hp]
    · cases hp : p j <;> simp [hp, Nat.testBit_two_pow, hji, Ne.symm hji]

theorem testBit_wordStep_all (k word i : Nat) :
    (wordStep k word).testBit i = (decide (i < k) && stepBit k word i) := by
  simp only [wordStep, testBit_foldl_set, Nat.zero_testBit, Bool.false_or, List.mem_range]

theorem testBit_wordStep {k word i : Nat} (hi : i < k) :
    (wordStep k word).testBit i =
      (word.testBit i ^^ (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))) := by
  simp [testBit_wordStep_all, stepBit, hi]

theorem wordStep_lt (k word : Nat) : wordStep k word < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  simp [testBit_wordStep_all, Nat.not_lt_of_ge hi]

def rot (k s w : Nat) : Nat :=
  ((w <<< (s % k)) ||| (w >>> (k - s % k))) % 2 ^ k

theorem rot_lt {k s w : Nat} : rot k s w < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

theorem bit_rot {k s w i : Nat} (wlt : w < 2 ^ k) (ilt : i < k) :
    (rot k s w).testBit i = w.testBit ((i+k-s%k)%k) := by
  have hs : s%k < k := Nat.mod_lt _ (by omega)
  simp only [rot, Nat.testBit_mod_two_pow, ilt, decide_true, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : s%k ≤ i
  · have hz : w.testBit (k-s%k+i) = false :=
      Nat.testBit_lt_two_pow (wlt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
    have he : (i+k-s%k)%k = i-s%k := by
      rw [Nat.mod_eq_sub_mod (by omega : k ≤ i+k-s%k), Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, hz, he]
  · have he : (i+k-s%k)%k = k-s%k+i := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, he]

theorem lt_xor {a b k : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    a ^^^ b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have hm := Nat.pow_le_pow_right Nat.zero_lt_two hi
  simp [Nat.testBit_xor, Nat.testBit_lt_two_pow (ha.trans_le hm),
    Nat.testBit_lt_two_pow (hb.trans_le hm)]

theorem wordStep_eq (k word : Nat) :
    wordStep k word = (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0 := by
  unfold wordStep
  congr 1
  funext a j
  change (if stepBit k word j then a ||| 2^j else a) =
    a ||| ((stepBit k word j).toNat <<< j)
  cases stepBit k word j <;> simp [Nat.shiftLeft_eq]
end BitBridge

namespace Word25484

open BitBridge Sweep25484

def constant (k t : Nat) : Nat := 3^(k+t) % 2^k
def updateRound (k d e t w state : Nat) : Nat :=
  wordStep k (state ^^^ rot k d state ^^^ rot k (k-d) state) ^^^ rot k e w ^^^ constant k t

def rowWord (k w u : Nat) : Nat → Nat
  | 0 => rot k 1 w ^^^ u
  | t+1 => updateRound k 1 (2*t) (t+1) w (rowWord k w u t)

theorem upd_lt (k d e t w state : Nat) : updateRound k d e t w state < 2^k :=
  lt_xor (lt_xor (wordStep_lt _ _) rot_lt) (Nat.mod_lt _ (Nat.two_pow_pos _))

theorem rowWord_lt {k w u : Nat} (hu : u < 2^k) (t : Nat) : rowWord k w u t < 2^k := by
  cases t
  · exact lt_xor rot_lt hu
  · exact upd_lt ..

theorem sub_cyclic {k a m : Nat} (hm : m ≤ k) (ha : m ≤ a) :
    (a%k+k-m)%k = (a-m)%k := by
  apply Nat.ModEq.add_right_cancel' m
  change ((a%k+k-m)+m)%k = ((a-m)+m)%k
  rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel ha, Nat.add_mod_right, Nat.mod_mod]

theorem rbit {k w i : Nat} (h : i < k) {m : Nat} (hm : m < k)
    (hw : w < 2^k) : (rot k m w).testBit i = w.testBit ((i+k-m)%k) := by
  rw [bit_rot hw h, Nat.mod_eq_of_lt hm]

theorem bit_mod_add (w k a j : Nat) :
    w.testBit ((a%k+j)%k) = w.testBit ((a+j)%k) := by rw [Nat.mod_add_mod]

theorem round_fold {α : Type*} (f : Nat → α) (op : α → Nat → α)
    (hf : ∀ j, f (j+1) = op (f j) j) (t : Nat) :
    (List.range t).foldl op (f 0) = f t := by
  induction t with
  | zero => rfl
  | succ t IH => rw [List.range_succ, List.foldl_append, IH, List.foldl_cons, List.foldl_nil, hf]

def coordBit (k z w : Nat) (i : Nat) : Bool := w.testBit ((z+i)%k)
def coordConst (k r z : Nat) (t i : Nat) : Bool :=
  coordBit k z (constant k t) (i+(r+t-3))

theorem rowWord_norm {k r z w u : Nat} (hr : 4 ≤ r) (hkr : 5*r-2 ≤ k)
    (hw : w < 2^k) (hu : u < 2^k) (hz : 0 < z) (t : Nat) (ht : t ≤ r) (i : Nat) :
    coordBit k z (rowWord k w u t) (i+(r+t-3)) =
      row r (coordBit k z u) (coordConst k r z) (coordBit k z (rowWord k w u 0)) t i := by
  induction t generalizing i with
  | zero => rfl
  | succ t IH =>
    let p := z+i+(r+t-3)
    have hk : 0 < k := by omega
    have hi : (p+1)%k < k := Nat.mod_lt _ hk
    have e₁ : z+(i+(r+(t+1)-3)) = p+1 := by dsimp [p]; omega
    have hlin (j : Nat) :
        (rowWord k w u t ^^^ rot k 1 (rowWord k w u t) ^^^
          rot k (k-1) (rowWord k w u t)).testBit ((p+j+1)%k) =
        Sweep25484.mix (row r (coordBit k z u) (coordConst k r z)
          (coordBit k z (rowWord k w u 0)) t) (i+j) := by
      have hm := Nat.mod_lt (p+j+1) hk
      have hs : ((p+j+1)%k+k-1)%k = (p+j)%k := by
        rw [sub_cyclic (by omega) (by omega)]
        simp
      have hs' : ((p+j+1)%k+k-(k-1))%k = (p+j+2)%k := by
        rw [show (p+j+1)%k+k-(k-1) = (p+j+1)%k+1 by omega, Nat.mod_add_mod]
      rw [Nat.testBit_xor, Nat.testBit_xor, rbit hm (by omega) (rowWord_lt hu t),
        rbit hm (by omega) (rowWord_lt hu t), hs, hs']
      have H (d : Nat) := IH (by omega) (i+j+d)
      simp only [coordBit] at H
      have he (d : Nat) : z+(i+j+d+(r+t-3)) = p+j+d := by dsimp [p]; omega
      simp only [he] at H
      rw [show (p+j)%k = (p+j+0)%k by rfl, H 0, H 1, H 2]
      simp [Sweep25484.mix, Bool.xor_comm, Nat.add_assoc]
    have hkey :
        (rot k (2*t) w).testBit ((p+1)%k) =
          xor (coordBit k z (rowWord k w u 0) (i+(r-(t+1))))
            (coordBit k z u (i+(r-(t+1)))) := by
      rw [rbit hi (by omega) hw, sub_cyclic (by omega) (by dsimp [p]; omega)]
      simp only [coordBit, rowWord, Nat.testBit_xor]
      rw [rbit (Nat.mod_lt _ hk) (by omega) hw,
        sub_cyclic (by omega) (by omega)]
      have he : p+1-2*t = z+(i+(r-(t+1)))-1 := by dsimp [p]; omega
      rw [he]
      cases w.testBit ((z+(i+(r-(t+1)))-1)%k) <;>
        cases u.testBit ((z+(i+(r-(t+1))))%k) <;> rfl
    simp only [coordBit, e₁, rowWord, updateRound]
    rw [Nat.testBit_xor, Nat.testBit_xor, testBit_wordStep hi]
    rw [show ((p+1)%k+1)%k = (p+1+1)%k by rw [Nat.mod_add_mod],
      show ((p+1)%k+2)%k = (p+2+1)%k by rw [Nat.mod_add_mod]]
    rw [show (p+1)%k = (p+0+1)%k by rfl, hlin 0, hlin 1, hlin 2]
    simp only [Nat.add_zero]
    rw [hkey]
    simp only [row, core, coordConst, coordBit, e₁, rowWord]

end Word25484

end PEqualNP.Outside.L_meta_25507_aux.Wrap507.Row.Impl

namespace PEqualNP.Outside.L_meta_25507_aux.Wrap507.Row

open Impl.BitBridge Impl.Word25484

def RawRow (k r w name : Nat) : Nat :=
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let constant := fun (j : Nat) => 3 ^ (k + j) % 2 ^ k
  (List.range r).foldl (fun state j =>
    step (state ^^^ rot 1 state ^^^ rot (k - 1) state) ^^^
      rot (2 * j) w ^^^ constant (j + 1)) (rot 1 w ^^^ name)

private theorem rawRow_eq (k r w name : Nat) : RawRow k r w name = rowWord k w name r := by
  unfold RawRow
  simp only [← wordStep_eq]
  exact round_fold (rowWord k w name) (fun s t => updateRound k 1 (2*t) (t+1) w s)
    (by intros; rfl) r

theorem rawRow_lt {k r w name : Nat} (hn : name < 2^k) : RawRow k r w name < 2^k := by
  rw [rawRow_eq]
  exact rowWord_lt hn r

theorem pivot {k r w₁ w₂ name i : Nat}
    (hr : 4 ≤ r) (hk : 6*r-5 < k)
    (h₁ : w₁ < 2^k) (h₂ : w₂ < 2^k) (hn : name < 2^k)
    (hi0 : k ≤ i) (_hi : i < 2*k)
    (agree : ∀ n, i-(2*r-2) < n → n ≤ i+4*r-3 →
      w₁.testBit (n%k) = w₂.testBit (n%k)) :
    xor ((RawRow k r w₁ name).testBit (i%k)) (w₁.testBit ((i-(2*r-2))%k)) =
      xor ((RawRow k r w₂ name).testBit (i%k)) (w₂.testBit ((i-(2*r-2))%k)) := by
  let P := i-(2*r-2)
  let z := P+1
  let U := coordBit k z name
  let C := coordConst k r z
  let X (w : Nat) := coordBit k z (rowWord k w name 0)
  have hkpos : 0 < k := by omega
  have hz : 0 < z := by dsimp [z]; omega
  have xbit (w : Nat) (hw : w < 2^k) (j : Nat) :
      X w j = xor (w.testBit ((P+j)%k)) (U j) := by
    dsimp only [X, U, coordBit, rowWord]
    rw [Nat.testBit_xor, rbit (Nat.mod_lt _ hkpos) (m := 1) (by omega) hw,
      sub_cyclic (by omega) (by omega)]
    rw [show z+j-1 = P+j by dsimp [z]; omega]
  have output (w : Nat) (hw : w < 2^k) :
      (RawRow k r w name).testBit (i%k) = Impl.Sweep25484.row r U C (X w) r 0 := by
    rw [rawRow_eq]
    have H := rowWord_norm (z := z) hr (by omega) hw hn hz r le_rfl 0
    change (rowWord k w name r).testBit ((z+(0+(r+r-3)))%k) = _ at H
    have e : z+(0+(r+r-3)) = i := by dsimp [z, P]; omega
    rwa [e] at H
  have same : Impl.Sweep25484.pivot r U C (X w₁) 0 =
      Impl.Sweep25484.pivot r U C (X w₂) 0 := by
    apply Impl.Sweep25484.pivot_congr hr
    intro j hj hj'
    rw [xbit _ h₁, xbit _ h₂]
    rw [agree (P+j) (by dsimp [P]; omega) (by dsimp [P]; omega)]
  have parity (out key named piv : Bool) (h : out = false ↔ xor key named = piv) :
      xor out key = xor named piv := by
    cases out <;> cases key <;> cases named <;> cases piv <;> simp_all
  have residual (w : Nat) (hw : w < 2^k) :
      xor ((RawRow k r w name).testBit (i%k)) (w.testBit (P%k)) =
        xor (U 0) (Impl.Sweep25484.pivot r U C (X w) 0) := by
    apply parity
    have H := Impl.Sweep25484.row_zero_iff (u := U) (c := C) (x := X w) (n := 0) hr
    rw [← output w hw, xbit _ hw, Nat.add_zero] at H
    exact H
  exact (residual w₁ h₁).trans ((congrArg (xor (U 0)) same).trans (residual w₂ h₂).symm)

end PEqualNP.Outside.L_meta_25507_aux.Wrap507.Row

namespace PEqualNP.Outside.L_meta_25507_aux.Wrap507.ColBase

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

lemma col95_bits {k r w v t : Nat} (hr : 4≤r) (hk : 6*r-5<k) (ht : t≤r)
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

end PEqualNP.Outside.L_meta_25507_aux.Wrap507.ColBase

namespace PEqualNP.Outside.L_meta_25507_aux.Wrap507.Col
open PEqualNP.Outside.L_meta_25507_aux.Wrap507.ColBase

def RawCol (k r w v : Nat) := (List.range r).foldl (fun x i =>
  rawStep k (rawLin k x) ^^^ rot k (3*(i+1)+1) w ^^^ (3^(k+(r+(i+1)))%2^k))
  (rInit k w v)

lemma bound {k r w name : Nat} (hn : name < 2^k) : RawCol k r w name < 2^k := by
  unfold RawCol
  rw [col95_fold]
  exact col95_bound _ _ hn _

private lemma roundsAgree {k r : Nat} {z z' v : Sig} {lo hi : Int}
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

private lemma natIdx (k n : Nat) : idx k (n:Int) = n%k := by
  simp only [idx,←Int.natCast_mod,Int.toNat_natCast]

private lemma nonnegIdx (k : Nat) (j : Int) (hj : 0≤j) : idx k j = j.toNat % k := by
  simpa only [Int.toNat_of_nonneg hj] using natIdx k j.toNat

private lemma coreBit {k t w name i : Nat}
    (hr : 4 ≤ t+1) (hk : 6*(t+1)-5 < k) (hw : w<2^k) (hn : name<2^k)
    (hi0 : k ≤ i) (hi : i<2*k) :
    (RawCol k (t+1) w name).testBit (i%k) =
      xor (xor (sweep (colSignal95 k (t+1) (bits k (rInit k w name)) (bits k name) t) i)
        (w.testBit ((i-(3*(t+1)+1))%k))) (ctr k ((t+1)+(t+1)) i) := by
  unfold RawCol
  rw [col95_fold]
  have hi' : idx k (i:Int)=i%k := natIdx k i
  have eq := congrFun (col95_bits (r:=t+1) (k:=k) (by omega) (by omega)
    (Nat.le_refl (t+1)) hw hn) (i:Int)
  change bits k (col95 k (t+1) w name (t+1)) i = _ at eq
  unfold bits at eq
  rw [hi'] at eq
  rw [eq]
  change xor (xor _ (xor (bits k (rInit k w name) _) (bits k name _))) _ = _
  rw [rInit,bitsXor,bitsRot (show 3<k by omega) hw]
  have hindex : ((i:Int)-((3*(t+1)-2 : Nat):Int)-((3:Nat):Int)) = ((i-(3*(t+1)+1):Nat):Int) := by omega
  rw [hindex]
  unfold bits
  rw [natIdx]
  simp

theorem pivot {k r w₁ w₂ name i : Nat} (hr : 4≤r) (hk : 6*r-5 < k)
    (h₁ : w₁ < 2^k) (h₂ : w₂ < 2^k) (hn : name < 2^k)
    (hi0 : k ≤ i) (hi : i<2*k)
    (agree : ∀ n : Nat, i - (3*r+1) < n → n ≤ i + 4*r - 3 → w₁.testBit (n%k) = w₂.testBit (n%k)) :
    xor ((RawCol k r w₁ name).testBit (i%k)) (w₁.testBit ((i-(3*r+1))%k)) =
      xor ((RawCol k r w₂ name).testBit (i%k)) (w₂.testBit ((i-(3*r+1))%k)) := by
  cases r with
  | zero => omega
  | succ t =>
    rw [coreBit hr hk h₁ hn hi0 hi,coreBit hr hk h₂ hn hi0 hi]
    have earlier : Agrees (bits k (rInit k w₁ name)) (bits k (rInit k w₂ name))
        ((i:Int)-((3*(t+1)-2 : Nat):Int)+1) (i+4*((t+1:Nat):Int)) := by
      intro j jl jh
      rw [rInit,rInit,bitsXor,bitsXor,bitsRot (show 3<k by omega) h₁,bitsRot (show 3<k by omega) h₂]
      have jp : 0 ≤ j-((3:Nat):Int) := by omega
      have changeKey : bits k w₁ (j-((3:Nat):Int)) = bits k w₂ (j-((3:Nat):Int)) := by
        unfold bits
        rw [nonnegIdx k _ jp]
        exact agree _ (by omega) (by omega)
      rw [changeKey]
    have same : sweep (colSignal95 k (t+1) (bits k (rInit k w₁ name)) (bits k name) t) i =
        sweep (colSignal95 k (t+1) (bits k (rInit k w₂ name)) (bits k name) t) i := by
      apply sweepEq
      intro j jl jh
      exact roundsAgree earlier t j (by omega) (by omega) (by omega)
    rw [same]
    exact (show ∀ a b c d : Bool, xor (xor (xor a b) d) b = xor (xor (xor a c) d) c by decide) _ _ _ _

end PEqualNP.Outside.L_meta_25507_aux.Wrap507.Col

namespace PEqualNP.Outside.L_meta_25507_aux.Decoder
abbrev Bits := Nat  →  Bool
def fill (F : Bits  →  Nat  →  Bool) : Nat  →  Bits  →  Bits
 | 0,x=>x
 | n+1,x=>fill F n (Function.update x n (xor (F x n) (x n)))

lemma fill_ge (F:Bits → Nat → Bool) (q:Nat) (x:Bits) (j:Nat) (h:q ≤ j) : fill F q x j = x j := by
 induction q generalizing x with
 | zero => rfl
 | succ q ih =>
   rw [fill,ih _ (by omega),Function.update_of_ne (by omega)]

def Tri (F:Bits → Nat → Bool) (q k:Nat) : Prop :=
 ∀ i, i<q  →  ∀ x y, (∀j,i<j  →  j<k  →  x j=y j)  →  xor (F x i) (x i)=xor (F y i) (y i)

lemma fill_good {F:Bits → Nat → Bool} {q k:Nat} (h:Tri F q k) {n:Nat} (hn:n ≤ q) (x:Bits) :
 ∀ i, i<n  →  F (fill F n x) i=false := by
 induction n generalizing x with
 | zero => omega
 | succ n ih =>
   intro i hi
   rw [fill]
   by_cases ii:i<n
   · exact ih (by omega) _ i ii
   · have eq : i=n := by omega
     subst i
     let w := Function.update x n (xor (F x n) (x n))
     have e : fill F n w n = xor (F x n) (x n) := by rw [fill_ge _ _ _ _ (by omega)]; exact Function.update_self ..
     have z := h n (by omega) (fill F n w) x (fun j hj _ => by rw [fill_ge _ _ _ _ (by omega)];exact Function.update_of_ne (by omega) _ _)
     change F (fill F n w) n = false
     rw [e] at z
     revert z
     cases F (fill F n w) n <;> cases F x n <;> cases x n <;> decide

lemma tri_unique {F:Bits → Nat → Bool} {q k:Nat} (h:Tri F q k) (x y:Bits)
 (xs:∀i,i<q → F x i=false) (ys:∀i,i<q → F y i=false) (above:∀i,q ≤ i → i<k → x i=y i):
 ∀ i,i<k → x i=y i := by
 intro i hi
 suffices H : ∀ d,∀t,t<k → k-t=d → x t=y t by exact H (k-i) i hi rfl
 intro d
 induction d using Nat.strong_induction_on with
 | ind d ih =>
   intro t ht hd
   by_cases lo:t<q
   · have z:=h t lo x y (fun j h1 h2 => ih (k-j) (by omega) j h2 rfl)
     simpa only [xs t lo,ys t lo,Bool.false_xor] using z
   · exact above t (by omega) ht
end PEqualNP.Outside.L_meta_25507_aux.Decoder

namespace PEqualNP.Outside.L_meta_25507_aux.Decoder
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
def encodeBits (k:Nat) (x:Nat→Bool) : Fin (2^k) :=
 ⟨(List.range k).foldl (fun z i => z ||| flipAt x i) 0, by
  apply Nat.lt_pow_two_of_testBit
  intro i h
  simp [packBit,show ¬i<k by omega]⟩

lemma encBit {k i:Nat} (h:i<k) (x:Nat→Bool) : (encodeBits k x).val.testBit i=x i := by
 simp [encodeBits,packBit,h]

def coord {k:Nat} (a:Nat) (w:Fin (2^k)) (t:Nat) := w.val.testBit ((a+t)%k)
def word {k:Nat} (a:Nat) (x:Nat→Bool) : Fin (2^k) :=
 encodeBits k (fun i => x ((i+(k-a))%k))

lemma cdwd {k a t:Nat} (ha:a≤k) (ht:t<k) (x:Nat→Bool) :
 coord a (word (k:=k) a x) t=x t := by
 unfold coord word
 rw [encBit (Nat.mod_lt _ (by omega))]
 rw [Nat.mod_add_mod,show a+t+(k-a)=t+k by omega,Nat.add_mod_right,Nat.mod_eq_of_lt ht]

lemma wdcd {k a:Nat} (ha:a≤k) (w:Fin (2^k)) : word a (coord a w)=w := by
 apply Fin.ext
 apply Nat.eq_of_testBit_eq
 intro i
 by_cases hi:i<k
 · unfold word
   rw [encBit hi]
   simp only [coord,Nat.add_mod_mod]
   rw [show a+(i+(k-a))=i+k by omega,Nat.add_mod_right,Nat.mod_eq_of_lt hi]
 · have h1:= (word (k:=k) a (coord a w)).isLt
   have h2:=w.isLt
   rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (by omega))),
       Nat.testBit_lt_two_pow (lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) (by omega)))]

lemma wordExt {k a:Nat} (x y:Nat→Bool) (h:∀i,i<k→x i=y i) : word (k:=k) a x=word a y := by
 by_cases hk:0<k
 · unfold word;congr 1;funext i;exact h _ (Nat.mod_lt _ hk)
 · obtain rfl:k=0:=by omega
   change (_ : Fin 1) = _; exact Subsingleton.elim _ _
end PEqualNP.Outside.L_meta_25507_aux.Decoder

namespace PEqualNP.Outside.L_meta_25507_aux.Wrap507.ColBase.Builder
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
end PEqualNP.Outside.L_meta_25507_aux.Wrap507.ColBase.Builder

namespace PEqualNP.Outside.L_meta_25507_aux.Wrap507.ColBase.Builder.Bank

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

end PEqualNP.Outside.L_meta_25507_aux.Wrap507.ColBase.Builder.Bank

namespace PEqualNP.Outside.L_meta_25507_aux.Wrap507.ColBase.Name
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

end PEqualNP.Outside.L_meta_25507_aux.Wrap507.ColBase.Name

namespace PEqualNP.Outside.L_meta_25507_aux
open PEqualNP.Outside.L_meta_25507_aux.Wrap507.ColBase.Builder
open PEqualNP.Outside.L_meta_25507_aux.Wrap507.ColBase.Builder.Bank
open PEqualNP.Outside.L_meta_25507_aux.Decoder

def AnyBits {n : Nat} (B : Bank n) (X : (Fin n → Bool) → Bits) :=
  ∀ j, B.Has (fun x => X x j)

lemma seedWires {n : Nat} (B : Bank n) (x : Bits) :
    B.Grow 2 (fun D => AnyBits D (fun _ => x)) := by
  apply (B.const false).bind (b:=1)
  intro D ext h0
  obtain ⟨E,e,sz,h1⟩ := D.const true
  refine ⟨E,e,sz,?_⟩
  intro j
  cases h : x j
  · simpa only [h] using e h0
  · simpa only [h] using h1

lemma fillWires {n q c : Nat} (B : Bank n)
    (F : (Fin n → Bool) → Bits → Nat → Bool)
    (emit : ∀ D : Bank n, B.Ext D → ∀ X : (Fin n → Bool) → Bits, AnyBits D X →
      ∀ i, i < q → D.Grow c (fun E => E.Has (fun x => F x (X x) i))) :
    ∀ t ≤ q, ∀ D : Bank n, B.Ext D → ∀ X : (Fin n → Bool) → Bits, AnyBits D X →
    D.Grow (t*(c+4)) (fun E => AnyBits E (fun x => fill (F x) t (X x))) := by
  intro t
  induction t with
  | zero =>
    intro _ D _ X hX
    exact ⟨D,fun h => h,by simp,hX⟩
  | succ t ih =>
    intro ht D ext X hX
    obtain ⟨E,e,es,hy⟩ := emit D ext X hX t (by omega)
    obtain ⟨G,g,gs,hnew⟩ := xor2 hy (e (hX t))
    let Y := fun x => Function.update (X x) t (xor (F x (X x) t) (X x t))
    have hY : AnyBits G Y := by
      intro j
      by_cases eq : j=t
      · subst j; simpa only [Y, Function.update_self] using hnew
      · simpa only [Y, Function.update_of_ne eq] using g (e (hX j))
    obtain ⟨H,h,hs,ha⟩ := ih (by omega) G (fun w => g (e (ext w))) Y hY
    exact ⟨H,fun w => h (g (e w)),by rw [Nat.succ_mul]; omega,ha⟩

lemma wordWires {n k a : Nat} (_hk : 0 < k) {B : Bank n} {X : (Fin n → Bool) → Bits}
    (h : AnyBits B X) : ∀ j : Fin k,
    B.Has (fun x => (word (k:=k) a (X x)).val.testBit j.val) := by
  intro j
  simpa only [word,encBit j.isLt] using h ((j.val+(k-a))%k)

lemma boundedSlots {n s cost budget : Nat} (f : Fin (2^s) → BitFn n)
    (emit : ∀ D : Bank n, (Bank.empty n).Ext D → ∀ i : Fin (2^s),
      D.Grow cost (fun E => E.Has (f i))) (fit : cost + 2 ≤ budget) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      C.size ≤ 2^s*budget ∧ ∀ x, C.eval (List.ofFn x) = (List.finRange (2^s)).any (fun i => f i x) := by
  obtain ⟨C,fan,back,sz,ok⟩ := finish (anySlots (Bank.empty n) (List.finRange (2^s)) f cost
    (fun D ext i _ => emit D ext i))
  refine ⟨C,fan,back,?_,ok⟩
  simp only [List.length_finRange] at sz
  calc
    C.size ≤ 1+2^s*(cost+1) := sz
    _ ≤ 2^s*(cost+2) := by
      rw [show 2^s*(cost+2) = 2^s*(cost+1)+2^s by ring]
      have : 0<2^s := by positivity
      omega
    _ ≤ _ := Nat.mul_le_mul_left _ fit

lemma fits {k q r : Nat} (hq : q ≤ k) :
    (2+q*(k*(4+19*r)+4)+(2*(k*(4+19*r)+k+2)+1)) + 2 ≤ 24*(k+1)^2*(r+1) := by
  calc
    _ ≤ (2+k*(k*(4+19*r)+4)+(2*(k*(4+19*r)+k+2)+1))+2 := by gcongr
    _ ≤ _ := by ring_nf; omega

end PEqualNP.Outside.L_meta_25507_aux

namespace PEqualNP.Outside.L_meta_25507_aux.Decoder

def labelOf {k:Nat} (a q s:Nat) (w:Fin (2^k)) (j:Fin s) := coord a w (q+j.val)
def zeroTail {k:Nat} (a q s:Nat) (w:Fin (2^k)) := ∀ i, q+s ≤ i → i<k → coord a w i=false
def seedStart {s:Nat} (q:Nat) (l:Fin s → Bool) (i:Nat) :=
 if h : q ≤ i ∧ i<q+s then l ⟨i-q,by omega⟩ else false

lemma decoder {k a q s:Nat} (ha:a≤k) (hqs:q+s≤k)
 (test: Fin (2^k) → Nat → Bool) (joint:Fin (2^k) → Prop)
 (tri:Tri (fun x => test (word a x)) q (q+s))
 (jsel:∀w,joint w → ∀ i,i<q → test w i =false)
 (jr:∀ w v, (∀ i,i<q+s → coord a w i=coord a v i) → joint w → joint v) :
 ∃ d : (Fin s → Bool) → Fin (2^k),
 (∀ l w,w=d l ↔ labelOf a q s w=l ∧ zeroTail a q s w ∧ ∀i,i<q → test w i=false) ∧
 ((∃w,joint w) ↔ ∃l,joint (d l)) := by
 let F := fun x => test (word a x)
 let b := fun (l:Fin s → Bool) => fill F q (seedStart q l)
 let d := fun (l:Fin s → Bool) => word (k:=k) a (b l)
 have dl (l : Fin s → Bool) : labelOf a q s (d l)=l := by
   funext j
   change coord a (word a (fill F q (seedStart q l))) (q+j.val)=l j
   rw [cdwd ha (by have:=j.isLt; omega),fill_ge _ _ _ _ (by omega)]
   simp [seedStart,j.isLt]
 have dz (l: Fin s → Bool) : zeroTail a q s (d l) := by
   intro i h hi
   change coord a (word a (fill F q (seedStart q l))) i=false
   rw [cdwd ha hi,fill_ge _ _ _ _ (by omega)]
   simp [seedStart,show ¬i<q+s by omega]
 have ds (l: Fin s → Bool) : ∀ i,i<q → test (d l) i=false :=
   fill_good tri (Nat.le_refl _) (seedStart q l)
 have same (w: Fin (2^k)) (l : Fin s → Bool) (wl:labelOf a q s w=l)
      (ws:∀i,i<q → test w i=false) : ∀ i,i<q+s → coord a w i=coord a (d l) i := by
   apply tri_unique tri
   · intro i hi
     simpa only [wdcd ha] using ws i hi
   · intro i hi
     simpa only [wdcd ha] using ds l i hi
   · intro i hl hr
     let j : Fin s := ⟨i-q, by omega⟩
     have e := congrFun (wl.trans (dl l).symm) j
     change coord a w (q+(i-q))=coord a (d l) (q+(i-q)) at e
     rwa [show q+(i-q)=i by omega] at e
 refine ⟨d,?_,?_⟩
 · intro l w
   constructor
   · rintro rfl;exact ⟨dl l,dz l,ds l⟩
   · rintro ⟨wl,wz,ws⟩
     have h := same w l wl ws
     have eq := wordExt (a:=a) (k:=k) (coord a w) (coord a (d l)) (fun i hi => by
       by_cases e:i<q+s
       · exact h i e
       · rw [wz i (by omega) hi,dz l i (by omega) hi])
     simpa only [wdcd ha] using eq
 · constructor
   · rintro ⟨w,hw⟩
     let l := labelOf a q s w
     exact ⟨l,jr w (d l) (same w l rfl (jsel w hw)) hw⟩
   · rintro ⟨l,hl⟩;exact ⟨d l,hl⟩
end PEqualNP.Outside.L_meta_25507_aux.Decoder

namespace PEqualNP.Outside.L_meta_25507_aux.Sweep507
open PEqualNP.Outside.L_meta_25507_aux.Decoder
abbrev s (r : Nat) := 6*r-5
abbrev hh (k : Nat) := (k+1)/2
abbrev q (k r : Nat) := min (k-s r) (hh k+r+3)
abbrev a (k r : Nat) := 2*k-(2*r-2)-q k r-k
def dist (r : Nat) (b : Bool) := if b then 3*r+1 else 2*r-2
def col (k r t : Nat) := decide (t < q k r-hh k)
def pos (k r t : Nat) := (a k r+t+dist r (col k r t))%k
def valBit {k : Nat} (r u v : Nat) (b : Bool) (w : Fin (2^k)) (i : Nat) :=
  if b then (Wrap507.Col.RawCol k r w.val v).testBit i else (Wrap507.Row.RawRow k r w.val u).testBit i
def test {k : Nat} (r u v : Nat) (w : Fin (2^k)) (t : Nat) :=
  valBit r u v (col k r t) w (pos k r t)
def both {k : Nat} (r u v : Nat) (w : Fin (2^k)) :=
  Wrap507.Row.RawRow k r w.val u  <  2^(k-hh k) ∧ Wrap507.Col.RawCol k r w.val v  <  2^(k-hh k)
def key {k : Nat} (r u v : Nat) (seed : Fin (2^(s r))) :=
  word (k:=k) (a k r) (fill (fun x=>test r u v (word (k:=k) (a k r) x))
    (q k r) (seedStart (q k r) (fun j:Fin (s r)=>seed.val.testBit j.val)))
lemma keyLaw {k r u v i:Nat} (hr:4 ≤ r) (hk:s r < k) (hu:u < 2^k) (hv:v < 2^k)
    (b:Bool) (w z:Fin (2^k)) (hi0 : k ≤ i) (hi:i < 2*k)
    (ag:∀ n,i-dist r b < n → n ≤ i+4*r-3 → w.val.testBit (n%k)=z.val.testBit (n%k)) :
    xor (valBit r u v b w (i%k)) (w.val.testBit ((i-dist r b)%k)) =
    xor (valBit r u v b z (i%k)) (z.val.testBit ((i-dist r b)%k)) := by
  cases b
  · exact Wrap507.Row.pivot hr hk w.isLt z.isLt hu hi0 hi ag
  · exact Wrap507.Col.pivot hr hk w.isLt z.isLt hv hi0 hi ag

lemma coordLift {k a n:Nat} (hn:k+a ≤ n) (w:Fin (2^k)) :
    w.val.testBit (n%k)=coord a w (n-(k+a)) := by
  have e:n=(a+(n-(k+a)))+k := by omega
  unfold coord
  conv_lhs => rw [e,Nat.add_mod_right]
lemma lowTest {k l x:Nat} (hx:x < 2^k) :
 x < 2^l ↔ ∀ i,l  ≤  i → i < k → x.testBit i=false := by
 constructor
 · intro h i hi _
   exact Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hi))
 · intro h
   apply Nat.lt_pow_two_of_testBit
   intro i hi
   by_cases b:i < k
   · exact h _ hi b
   · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
end PEqualNP.Outside.L_meta_25507_aux.Sweep507

namespace PEqualNP.Outside.L_meta_25507_aux.Wrap507.ColBase
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

lemma roundBound {k dist shift C w state : Nat} (hC:C<2^k) : round k dist shift C w state<2^k :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepBound ..) (Nat.mod_lt _ (by positivity))) hC

end Eval
end PEqualNP.Outside.L_meta_25507_aux.Wrap507.ColBase

namespace PEqualNP.Outside.L_meta_25507_aux.Eval507
open PEqualNP.Outside.L_meta_25507_aux.Wrap507.ColBase
open Builder Builder.Bank Eval

variable {n k r : Nat}

def FiniteBits (k : Nat) (B : Bank n) (W : Word n) : Prop :=
  ∀ j : Fin k, B.Has (fun x => (W x).testBit j.val)

private lemma finiteOfWord {B : Bank n} {W : Word n} (h : HasWord k B W) :
    FiniteBits k B W := by
  intro j
  simpa only [bits, idxNat j.isLt] using h (j.val : Int)

private lemma rotateAny {B : Bank n} {W : Word n} (hk : 0 < k) (h : HasWord k B W)
    (bounded : ∀ x, W x < 2^k) (s : Nat) :
    HasWord k B (fun x => rot k s (W x)) := by
  have e (v : Nat) : rot k (s%k) v = rot k s v := by simp [rot]
  simpa only [e] using rotated h (Nat.mod_lt s hk) bounded

private lemma roundAny {B : Bank n} {W V : Word n} (hk : 0 < k) (dist shift c : Nat)
    (hw : HasWord k B W) (hv : HasWord k B V)
    (bw : ∀ x, W x < 2^k) (bv : ∀ x, V x < 2^k) :
    B.Grow (k*19) (fun D => HasWord k D (fun x => round k dist shift c (W x) (V x))) := by
  have a := rotateAny hk hv bv dist
  have b := rotateAny hk hv bv (k-dist)
  have key := rotateAny hk hw bw shift
  obtain ⟨D, e, de, t⟩ := xorWords hk hv a
  obtain ⟨E, f, ef, u⟩ := xorWords hk t (wordLift e b)
  obtain ⟨F, g, fg, v⟩ := nonlinear hk u
  obtain ⟨G, j, gj, p⟩ := xorWords hk v (wordLift g (wordLift f (wordLift e key)))
  obtain ⟨H, m, mh, q⟩ := xorConst hk p c
  exact ⟨H, fun h => m (j (g (f (e h)))), by omega, q⟩

private def state (k initial dist : Nat) (shift c : Nat → Nat) (w u t : Nat) : Nat :=
  (List.range t).foldl (fun s j => round k dist (shift j) (c j) w s)
    (rot k initial w ^^^ u)

private lemma stateSucc (k initial dist : Nat) (shift c : Nat → Nat) (w u t : Nat) :
    state k initial dist shift c w u (t+1) =
      round k dist (shift t) (c t) w (state k initial dist shift c w u t) := by
  simp [state, List.range_succ, List.foldl_append]

private lemma stateBound (k initial dist : Nat) (shift c : Nat → Nat) (w u : Nat)
    (hb : u < 2^k) (hc : ∀ t, c t < 2^k) (t : Nat) :
    state k initial dist shift c w u t < 2^k := by
  cases t with
  | zero => exact Nat.xor_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos _)) hb
  | succ t => rw [stateSucc]; exact roundBound (hc t)

private lemma allStates {B : Bank n} {W U : Word n} (initial dist : Nat)
    (shift c : Nat → Nat) (hc : ∀ t, c t < 2^k)
    (hw : FiniteBits k B W) (hu : FiniteBits k B U)
    (bw : ∀ x, W x < 2^k) (bu : ∀ x, U x < 2^k) (t : Nat) :
    B.Grow (k*(4+19*t))
      (fun D => FiniteBits k D (fun x => state k initial dist shift c (W x) (U x) t)) := by
  by_cases hk : 0 < k
  · have hW := fromFin hk hw
    have hU := fromFin hk hu
    have build (s : Nat) : B.Grow (k*(4+19*s))
        (fun D => HasWord k D (fun x => state k initial dist shift c (W x) (U x) s)) := by
      induction s with
      | zero => simpa [state] using
          xorWords hk (rotateAny hk hW bw initial) hU
      | succ s ih =>
        obtain ⟨D, e, de, hv⟩ := ih
        obtain ⟨E, f, ef, hnext⟩ := roundAny hk dist (shift s) (c s) (wordLift e hW) hv
          bw (fun x => stateBound k initial dist shift c (W x) (U x) (bu x) hc s)
        refine ⟨E, fun h => f (e h), ?_, ?_⟩
        · rw [Nat.mul_succ 19, ← Nat.add_assoc 4, Nat.mul_add]
          omega
        · simpa only [stateSucc] using hnext
    exact (build t).weaken (le_refl _) (fun _ h => finiteOfWord h)
  · refine ⟨B, fun h => h, by omega, ?_⟩
    intro j
    have hj := j.isLt
    omega

theorem rowState {B : Bank n} {W U : Word n}
    (hw : FiniteBits k B W) (hu : FiniteBits k B U)
    (bw : ∀ x, W x < 2^k) (bu : ∀ x, U x < 2^k) :
    B.Grow (k*(4+19*r))
      (fun D => FiniteBits k D (fun x => Wrap507.Row.RawRow k r (W x) (U x))) := by
  exact allStates 1 1 (fun j => 2*j) (fun j => 3^(k+(j+1))%2^k)
    (fun _ => Nat.mod_lt _ (Nat.two_pow_pos _)) hw hu bw bu r

theorem colState {B : Bank n} {W U : Word n}
    (hw : FiniteBits k B W) (hu : FiniteBits k B U)
    (bw : ∀ x, W x < 2^k) (bu : ∀ x, U x < 2^k) :
    B.Grow (k*(4+19*r))
      (fun D => FiniteBits k D (fun x => Wrap507.Col.RawCol k r (W x) (U x))) := by
  exact allStates 3 2 (fun j => 3*(j+1)+1) (fun j => 3^(k+(r+(j+1)))%2^k)
    (fun _ => Nat.mod_lt _ (Nat.two_pow_pos _)) hw hu bw bu r

end PEqualNP.Outside.L_meta_25507_aux.Eval507

namespace PEqualNP.Outside.L_meta_25507_aux.Wrap507.ColBase.Eval

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

end PEqualNP.Outside.L_meta_25507_aux.Wrap507.ColBase.Eval

namespace PEqualNP.Outside.L_meta_25507_aux
open PEqualNP.Outside.L_meta_25507_aux.Decoder (Bits fill word seedStart)
open PEqualNP.Outside.L_meta_25507_aux.Wrap507.ColBase
open Builder Builder.Bank Eval507

private lemma finiteLift {n k : Nat} {B D : Bank n} {W : Eval.Word n}
    (e : B.Ext D) (hw : FiniteBits k B W) : FiniteBits k D W := fun j => e (hw j)

private lemma finiteHigh {n k : Nat} {B : Bank n} {W : Eval.Word n} (l : Nat)
    (hw : FiniteBits k B W) (bw : ∀ x, W x < 2^k) :
    B.Grow (k+2) (fun D => D.Has (fun x => decide (W x < 2^l))) := by
  have wires (i : Nat) (hi : i ∈ Eval.highIndices k l) : B.Has (fun x => (W x).testBit i) :=
    hw ⟨i,List.mem_range.mp (List.mem_filter.mp hi).1⟩
  obtain ⟨D,e,de,hD⟩ := anyBits (Eval.highIndices k l) (fun i x => (W x).testBit i) wires
  obtain ⟨E,f,ef,hE⟩ := inv hD
  have ln : (Eval.highIndices k l).length ≤ k := by simpa [Eval.highIndices] using
    (List.length_filter_le (fun i : Nat => decide (l ≤ i)) (List.range k))
  refine ⟨E,fun h => f (e h),by omega,?_⟩
  simpa only [Eval.highEq (bw _)] using hE

def check (k r u v w : Nat) :=
  decide (Wrap507.Row.RawRow k r w u < 2^(k-Sweep507.hh k)) &&
    decide (Wrap507.Col.RawCol k r w v < 2^(k-Sweep507.hh k))

abbrev stateCost (k r : Nat) := k*(4+19*r)
abbrev verifyCost (k r : Nat) := 2*(stateCost k r+k+2)+1

private lemma verify {n k r : Nat} {B : Bank n} {W U V : Eval.Word n}
    (hw : FiniteBits k B W) (hu : FiniteBits k B U) (hv : FiniteBits k B V)
    (bw : ∀ x, W x < 2^k) (bu : ∀ x, U x < 2^k) (bv : ∀ x, V x < 2^k) :
    B.Grow (verifyCost k r) (fun D => D.Has (fun x => check k r (U x) (V x) (W x))) := by
  obtain ⟨D,e,de,hR⟩ := rowState (r:=r) hw hu bw bu
  obtain ⟨E,f,ef,hRT⟩ := finiteHigh (k-Sweep507.hh k) hR (fun x =>
    Wrap507.Row.rawRow_lt (k:=k) (r:=r) (w:=W x) (bu x))
  obtain ⟨G,g,gs,hC⟩ := colState (r:=r) (finiteLift f (finiteLift e hw)) (finiteLift f (finiteLift e hv)) bw bv
  obtain ⟨H,h,hs,hCT⟩ := finiteHigh (k-Sweep507.hh k) hC (fun x =>
    Wrap507.Col.bound (k:=k) (r:=r) (w:=W x) (bv x))
  obtain ⟨J,j,js,hJ⟩ := meet (h (g hRT)) hCT
  exact ⟨J,fun z => j (h (g (f (e z)))),by dsimp [verifyCost,stateCost]; omega,hJ⟩

private lemma nameWires {n k : Nat} (atWire : Fin k → Fin n) {D : Bank n} (e : (Bank.empty n).Ext D) :
    FiniteBits k D (Name.name atWire) := by
  intro j
  simpa only [Name.nameBit] using e (Bank.input (atWire j))

private lemma sweepWire {n k r : Nat} (hk : 0 < k) {B : Bank n} {U V : Eval.Word n}
    (hu : FiniteBits k B U) (hv : FiniteBits k B V) (bu : ∀ x,U x<2^k) (bv : ∀ x,V x<2^k)
    {X : (Fin n → Bool) → Bits} (hx : AnyBits B X) (t : Nat) :
    B.Grow (stateCost k r) (fun D => D.Has (fun x =>
      Sweep507.test r (U x) (V x) (word (k:=k) (Sweep507.a k r) (X x)) t)) := by
  let W := fun x => (word (k:=k) (Sweep507.a k r) (X x)).val
  have hw : FiniteBits k B W := wordWires hk hx
  have bw (x) : W x < 2^k := (word (k:=k) _ (X x)).isLt
  let p : Fin k := ⟨Sweep507.pos k r t,Nat.mod_lt _ hk⟩
  cases eq : Sweep507.col k r t with
  | false =>
    apply (rowState (r:=r) hw hu bw bu).weaken (le_refl _)
    intro D ht
    simpa only [Sweep507.test,Sweep507.valBit,eq,Bool.false_eq_true,ite_false] using ht p
  | true =>
    apply (colState (r:=r) hw hv bw bv).weaken (le_refl _)
    intro D ht
    simpa only [Sweep507.test,Sweep507.valBit,eq,ite_true] using ht p

abbrev slotCost (k r : Nat) := 2+Sweep507.q k r*(stateCost k r+4)+verifyCost k r

private lemma compiledSlot {n k r : Nat} (hk : 0 < k) (B : Bank n) {U V : Eval.Word n}
    (hu : FiniteBits k B U) (hv : FiniteBits k B V) (bu : ∀ x,U x<2^k) (bv : ∀ x,V x<2^k)
    (seed : Fin (2^Sweep507.s r)) :
    B.Grow (slotCost k r) (fun D => D.Has (fun x =>
      check k r (U x) (V x) (Sweep507.key (k:=k) r (U x) (V x) seed).val)) := by
  let start := seedStart (Sweep507.q k r) (fun j : Fin (Sweep507.s r) => seed.val.testBit j.val)
  let F := fun x y t => Sweep507.test r (U x) (V x) (word (k:=k) (Sweep507.a k r) y) t
  obtain ⟨D,e,de,h0⟩ := seedWires B start
  have out := fillWires B F (c:=stateCost k r) (q:=Sweep507.q k r)
    (fun E ext X hx t _ => sweepWire hk (finiteLift ext hu) (finiteLift ext hv) bu bv hx t)
    (Sweep507.q k r) (le_refl _) D e (fun _ => start) h0
  obtain ⟨E,f,ef,hX⟩ := out
  let W := fun x => (Sweep507.key (k:=k) r (U x) (V x) seed).val
  have hw : FiniteBits k E W := wordWires hk hX
  obtain ⟨G,g,gs,hG⟩ := verify (r:=r) hw (finiteLift f (finiteLift e hu)) (finiteLift f (finiteLift e hv))
    (fun x => (Sweep507.key (k:=k) r (U x) (V x) seed).isLt) bu bv
  exact ⟨G,fun z => g (f (e z)),by dsimp [slotCost];omega,hG⟩

lemma anyRange {k : Nat} (f : Nat → Bool) :
    (List.range (2^k)).any f = true ↔ ∃ w : Fin (2^k), f w.val = true := by
  simp only [List.any_eq_true,List.mem_range]
  constructor
  · rintro ⟨i,hi,ok⟩; exact ⟨⟨i,hi⟩,ok⟩
  · rintro ⟨i,ok⟩; exact ⟨i.val,i.isLt,ok⟩

lemma anyFin {m : Nat} (f : Fin m → Bool) :
    (List.finRange m).any f = true ↔ ∃ i, f i = true := by simp [List.any_eq_true]

lemma checkSpec {k r u v : Nat} (w : Fin (2^k)) :
    check k r u v w.val = true ↔ Sweep507.both r u v w := by simp [check,Sweep507.both]

lemma whole {k r : Nat} (_hr : 4 ≤ r)
    (complete : Sweep507.s r < k → ∀ u v : Nat, u < 2^k → v < 2^k →
      ((∃ w : Fin (2^k), Sweep507.both r u v w) ↔
        ∃ seed, Sweep507.both r u v (Sweep507.key (k:=k) r u v seed))) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+k) C ∧
      C.size ≤ 2^(min k (Sweep507.s r))*(24*(k+1)^2*(r+1)) ∧
      ∀ x, C.eval (List.ofFn x) =
        (List.range (2^k)).any (check k r (Name.row k x) (Name.col k x)) := by
  let U := Name.row k
  let V := Name.col k
  by_cases h : k ≤ Sweep507.s r
  · rw [Nat.min_eq_left h]
    let f := fun (w : Fin (2^k)) x => check k r (U x) (V x) w.val
    have cost : 2+verifyCost k r+2 ≤ 24*(k+1)^2*(r+1) := by simpa using fits (k:=k) (r:=r) (q:=0) (Nat.zero_le k)
    obtain ⟨C,fan,back,sz,ok⟩ := boundedSlots f (cost:=2+verifyCost k r) (fun D ext w => by
      obtain ⟨E,e,es,hb⟩ := seedWires D (fun j => w.val.testBit j)
      have hW : FiniteBits k E (fun _ => w.val) := fun i => hb i.val
      have hU := nameWires (fun i : Fin k => Fin.castAdd k i) (D:=E) (fun z => e (ext z))
      have hV := nameWires (fun i : Fin k => Fin.natAdd k i) (D:=E) (fun z => e (ext z))
      obtain ⟨G,g,gs,hg⟩ := verify (r:=r) hW hU hV (fun _ => w.isLt) (Name.nameLt _) (Name.nameLt _)
      exact ⟨G,fun z => g (e z),by omega,hg⟩) cost
    refine ⟨C,fan,back,sz,fun x => ?_⟩
    rw [ok]
    apply Bool.eq_iff_iff.mpr
    rw [anyFin,anyRange]
  · have hs : Sweep507.s r < k := by omega
    rw [Nat.min_eq_right hs.le]
    let f := fun (seed : Fin (2^Sweep507.s r)) x =>
      check k r (U x) (V x) (Sweep507.key (k:=k) r (U x) (V x) seed).val
    have fits' := fits (k:=k) (q:=Sweep507.q k r) (r:=r)
      (Nat.le_trans (Nat.min_le_left ..) (Nat.sub_le ..))
    obtain ⟨C,fan,back,sz,ok⟩ := boundedSlots f (cost:=slotCost k r) (fun D ext seed =>
      compiledSlot (by omega) D
        (nameWires (fun i : Fin k => Fin.castAdd k i) ext)
        (nameWires (fun i : Fin k => Fin.natAdd k i) ext)
        (Name.nameLt _) (Name.nameLt _) seed) fits'
    refine ⟨C,fan,back,sz,fun x => ?_⟩
    rw [ok]
    apply Bool.eq_iff_iff.mpr
    rw [anyFin,anyRange]
    calc
      _ ↔ (∃ seed, Sweep507.both r (U x) (V x) (Sweep507.key (k:=k) r (U x) (V x) seed)) :=
        exists_congr fun _ => checkSpec _
      _ ↔ ∃ w : Fin (2^k), Sweep507.both r (U x) (V x) w :=
        (complete hs _ _ (Name.nameLt _ x) (Name.nameLt _ x)).symm
      _ ↔ _ := exists_congr fun _ => (checkSpec _).symm

end PEqualNP.Outside.L_meta_25507_aux

namespace PEqualNP.Outside.L_meta_25507_aux.Sweep507
open PEqualNP.Outside.L_meta_25507_aux.Decoder

lemma rangeData {k r : Nat} (hr:4 ≤ r) (hk:s r < k) :
    a k r  ≤  k ∧ q k r + s r  ≤  k ∧ k+a k r+q k r=2*k-(2*r-2) ∧
    q k r  ≤  hh k+r+3 ∧ hh k ≥ r+3 := by
  have l := Nat.min_le_left (k-s r) (hh k+r+3)
  have h := Nat.min_le_right (k-s r) (hh k+r+3)
  change q k r  ≤  k-s r at l
  change q k r  ≤  hh k+r+3 at h
  dsimp only [a,hh,s] at *
  omega
lemma pivotData {k r t:Nat} (hr:4 ≤ r) (hk:s r < k) (ht:t < q k r) :
    let j:=k+a k r+t+dist r (col k r t)
    k+(k-hh k)  ≤  j ∧ j < 2*k ∧ j+4*r-3 < k+a k r+(q k r+s r) := by
  obtain ⟨ha,hqs,e,hq,hh'⟩:=rangeData hr hk
  dsimp only
  by_cases h:t < q k r-hh k
  · simp only [col,h,decide_true,dist,if_true];dsimp only [s,hh] at *;omega
  · simp only [col,h,decide_false,dist,Bool.false_eq_true,if_false];dsimp only [s,hh] at *;omega

lemma triangular {k r u v:Nat} (hr:4 ≤ r) (hk:s r < k) (hu:u < 2^k) (hv:v < 2^k) :
    Tri (fun x=>test r u v (word (k:=k) (a k r) x)) (q k r) (q k r+s r) := by
  intro t ht x y ag
  let aa:=a k r
  let b:=col k r t
  let j:=k+aa+t+dist r b
  obtain ⟨ha,len,ed,hq,hh'⟩:=rangeData hr hk
  have pdata:=pivotData hr hk ht
  change k+(k-hh k) ≤ j ∧ j < 2*k ∧ j+4*r-3 < k+aa+(q k r+s r) at pdata
  have modj : j%k = pos k r t := by
    change (k+aa+t+dist r b)%k=(aa+t+dist r b)%k
    rw [show k+aa+t+dist r b=aa+t+dist r b+k by omega,Nat.add_mod_right]
  have e : j-dist r b=k+aa+t := by dsimp [j];omega
  have vals (z : Bits) {n:Nat} (hl:k+aa ≤ n) (hh:n < k+aa+(q k r+s r)) :
      (word (k:=k) aa z).val.testBit (n%k)=z (n-(k+aa)) := by
    rw [coordLift hl,cdwd ha (by omega)]
  have law:=keyLaw hr hk hu hv b (word aa x) (word aa y) (show k ≤ j by omega) pdata.2.1 (by
    intro n hn he
    rw [e] at hn
    rw [vals _ (by omega) (by omega),vals _ (by omega) (by omega)]
    exact ag _ (by omega) (by omega))
  rw [modj,e,vals _ (by omega) (by omega),vals _ (by omega) (by omega),Nat.add_sub_cancel_left] at law
  exact law

lemma jointSelected {k r u v:Nat} (hr:4 ≤ r) (hk:s r < k) (hu:u < 2^k) (hv:v < 2^k)
    (w:Fin (2^k)) (hw:both r u v w) {t:Nat} (ht:t < q k r) : test r u v w t=false := by
  let j:=k+a k r+t+dist r (col k r t)
  have hh':=pivotData hr hk ht
  change k+(k-hh k) ≤ j ∧ j < 2*k ∧ _ at hh'
  have z : pos k r t=j-k := by
    have e : j=k+(a k r+t+dist r (col k r t)) := by dsimp [j];omega
    unfold pos
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  unfold test valBit
  rw [z]
  split
  · exact (lowTest (Wrap507.Col.bound hv)).mp hw.2 _ (by omega) (by omega)
  · exact (lowTest (Wrap507.Row.rawRow_lt hu)).mp hw.1 _ (by omega) (by omega)

end PEqualNP.Outside.L_meta_25507_aux.Sweep507

namespace PEqualNP.Outside.L_meta_25507_aux.Sweep507
open PEqualNP.Outside.L_meta_25507_aux.Decoder

theorem joinTransfer {k r u v:Nat} (hr:4 ≤ r) (hk:s r<k) (hu:u<2^k) (hv:v<2^k)
 (w z:Fin (2^k)) (ag:∀t,t<q k r+s r → coord (a k r) w t=coord (a k r) z t)
 (hw:both r u v w) : both r u v z := by
 have al : a k r ≤ k := by dsimp [a,s,q,hh] at *;omega
 have qs : q k r + s r ≤ k := by dsimp [a,s,q,hh] at *;omega
 by_cases eq:q k r+s r=k
 · have h:=wordExt (k:=k) (a:=a k r) (coord (a k r) w) (coord (a k r) z) (fun i hi => ag i (by omega))
   rw [wdcd al,wdcd al] at h
   rwa [←h]
 · have nq : q k r = hh k+r+3 := by dsimp [q] at *;omega
   have ed : k+a k r+(q k r+s r) = 2*k+(4*r-3) := by dsimp [a,s,q,hh] at *;omega
   have base (n:Nat) (hs:k+a k r ≤ n) (he:n<k+a k r+(q k r+s r)):
     w.val.testBit (n%k)=z.val.testBit (n%k) := by
      rw [coordLift hs,coordLift hs];exact ag _ (by omega)
   have fixBit (b:Bool) (i:Nat) (h0:k-hh k ≤ i) (h1:i<k) :
       valBit r u v b w i = valBit r u v b z i := by
     have lo : k+a k r ≤ k+i-dist r b := by
       cases b <;> dsimp [a,s,q,hh,dist] at * <;> omega
     have hi : k+i+4*r-3<k+a k r+(q k r+s r) := by omega
     have zz := keyLaw hr hk hu hv b w z (i:=k+i) (by omega) (by omega)
        (fun n hl _ => base n (by omega) (by omega))
     have p:=base (k+i-dist r b) lo (by omega)
     rw [p, Nat.add_mod_left, Nat.mod_eq_of_lt h1] at zz
     exact Bool.xor_left_inj.mp zz
   constructor
   · apply (lowTest (PEqualNP.Outside.L_meta_25507_aux.Wrap507.Row.rawRow_lt hu)).mpr
     intro i h0 h1
     exact (fixBit false i h0 h1).symm.trans ((lowTest (PEqualNP.Outside.L_meta_25507_aux.Wrap507.Row.rawRow_lt hu)).mp hw.1 i h0 h1)
   · apply (lowTest (PEqualNP.Outside.L_meta_25507_aux.Wrap507.Col.bound hv)).mpr
     intro i h0 h1
     exact (fixBit true i h0 h1).symm.trans ((lowTest (PEqualNP.Outside.L_meta_25507_aux.Wrap507.Col.bound hv)).mp hw.2 i h0 h1)

end PEqualNP.Outside.L_meta_25507_aux.Sweep507

namespace PEqualNP.Outside.L_meta_25507_aux.Sweep507
open PEqualNP.Outside.L_meta_25507_aux.Decoder
lemma complete {k r u v:Nat} (hr:4 ≤ r) (hk:s r < k) (hu:u < 2^k) (hv:v < 2^k) :
    (∃ w : Fin (2^k), both r u v w) ↔ ∃ seed : Fin (2^s r), both r u v (key (k:=k) r u v seed) := by
  constructor
  · rintro ⟨w,hw⟩
    let l := labelOf (a k r) (q k r) (s r) w
    let sd := encodeBits (s r) (fun j=>if h:j < s r then l ⟨j,h⟩ else false)
    let x := seedStart (q k r) (fun j : Fin (s r) => sd.val.testBit j.val)
    let F := fun z => test r u v (word (k:=k) (a k r) z)
    let f := fill F (q k r) x
    obtain ⟨ha,hlen,ed⟩ := rangeData hr hk
    have tri : Tri F (q k r) (q k r+s r) := triangular hr hk hu hv
    have legal (t : Nat) (ht:t < q k r) : F (coord (a k r) w) t = false := by
      change test r u v (word (a k r) (coord (a k r) w)) t=false
      rw [wdcd ha]
      exact jointSelected hr hk hu hv _ hw ht
    have same:=tri_unique tri (coord (a k r) w) f legal (fill_good tri le_rfl x) (by
      intro j hj hjs
      let i : Fin (s r) := ⟨j-q k r,by omega⟩
      change coord (a k r) w j = fill F (q k r) x j
      rw [fill_ge _ _ _ _ hj]
      change coord (a k r) w j = seedStart (q k r) (fun h : Fin (s r)=>sd.val.testBit h.val) j
      have hjj : q k r ≤ j ∧ j < q k r+s r := ⟨hj,hjs⟩
      simp only [seedStart,dite_eq_left hjj]
      change coord (a k r) w j=sd.val.testBit i.val
      rw [show sd.val.testBit i.val = l i by
        dsimp only [sd]
        rw [encBit i.isLt,dite_eq_left i.isLt]]
      change coord (a k r) w j = coord (a k r) w (q k r+(j-q k r))
      congr 1;omega)
    refine ⟨sd,joinTransfer hr hk hu hv w _ ?_ hw⟩
    intro t ht
    change coord (a k r) w t = coord (a k r) (word (a k r) f) t
    rw [cdwd ha (by omega)]
    exact same _ ht
  · rintro ⟨seed,hw⟩
    exact ⟨key r u v seed,hw⟩

end PEqualNP.Outside.L_meta_25507_aux.Sweep507

open PEqualNP.Outside.L_meta_25507_aux in
theorem PEqualNP.Outside.L_meta_25507 :
∀ (k r : Nat), 4 ≤ r →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let constant := fun (j : Nat) => 3 ^ (k + j) % 2 ^ k
  let first := fun (rowKey rowName : Nat) =>
    (List.range r).foldl (fun rowState rowIndex =>
      step (rowState ^^^ rot 1 rowState ^^^ rot (k - 1) rowState) ^^^
        rot (2 * rowIndex) rowKey ^^^ constant (rowIndex + 1)) (rot 1 rowKey ^^^ rowName)
  let second := fun (colKey colName : Nat) =>
    (List.range r).foldl (fun colState colIndex =>
      step (colState ^^^ rot 2 colState ^^^ rot (k - 2) colState) ^^^
        rot (3 * (colIndex + 1) + 1) colKey ^^^ constant (r + (colIndex + 1)))
      (rot 3 colKey ^^^ colName)
  let h := (k + 1) / 2
  let graph : Fin (2 ^ k) → Fin (2 ^ k) → Bool := fun row col =>
    (List.range (2 ^ k)).any (fun w =>
      decide (first w row.val < 2 ^ (k - h)) && decide (second w col.val < 2 ^ (k - h)))
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + k) C ∧
    C.size ≤ 2 ^ (min k (6 * r - 5)) * (24 * (k + 1) ^ 2 * (r + 1)) ∧
    ∀ bits : Fin (k + k) → Bool,
      C.eval (List.ofFn bits) = PEqualNP.Represents.adjFun (k := k) (l := k) graph bits := by
  intro k r hr
  exact whole hr (fun hk _ _ hu hv => Sweep507.complete hr hk hu hv)
