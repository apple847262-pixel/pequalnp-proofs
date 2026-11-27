import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25504
import PEqualNP.Outside.L_meta_25522
import Mathlib.Data.Nat.Fib.Basic

namespace PEqualNP.Outside.L_meta_25523_aux

def prefix23 {α : Type} (test : α → Nat → Bool) : Nat → α → Bool
  | 0, _ => true
  | d+1, x => prefix23 test d x && test x d

lemma prefixIff23 {α : Type} (test : α → Nat → Bool) (d : Nat) (x : α) :
    prefix23 test d x = true ↔ ∀ j<d, test x j = true := by
  induction d with
  | zero => simp [prefix23]
  | succ d ih =>
    rw [prefix23,Bool.and_eq_true,ih]
    refine ⟨fun H j hj => ?_,fun H => ⟨fun j hj => H j (by omega),H d (by omega)⟩⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with lt|rfl
    · exact H.1 j lt
    · exact H.2

private lemma prefixCongr23 {α : Type} (test : α → Nat → Bool) {x y : α} {d : Nat}
    (h : ∀ i<d, test x i=test y i) : prefix23 test d x = prefix23 test d y := by
  apply Bool.eq_iff_iff.mpr
  simpa only [prefixIff23] using
    (forall_congr' fun i : Nat => forall_congr' fun hi : i<d => by rw [h i hi])

private theorem four23 : ∀ (a b v t u s z : Bool),
    (a=true → v=true) → (b=true → v=true) → ¬(t=true ∧ u=true ∧ s=true ∧ z=true) →
    (a&&t).toNat+(a&&u).toNat+(b&&s).toNat+(b&&z).toNat ≤ a.toNat+b.toNat+v.toNat := by
  decide

private def count23 {α : Type} [Fintype α] (test : α → Nat → Bool) (d : Nat) :=
  ∑ x : α, (prefix23 test d x).toNat

private theorem recurse23 {α : Type} [Fintype α] (test : α → Nat → Bool) (d : Nat)
    (A B : Equiv.Perm α) (ha : ∀ w j, j<d → test (A w) j = test w j)
    (hb : ∀ w j, j+1<d → test (B w) j = test w j)
    (sq : ∀ w, ¬(test w d=true ∧ test (A w) d=true ∧ test (B w) d=true ∧ test (A (B w)) d=true)) :
    4*count23 test (d+1) ≤ 2*count23 test d + count23 test (d-1) := by
  let f (i : Nat) (x : α) := (prefix23 test i x).toNat
  have lower (w : α) (hw : prefix23 test d w=true) : prefix23 test (d-1) w=true :=
    (prefixIff23 ..).mpr (fun j hj => (prefixIff23 ..).mp hw j (by omega))
  have inA (w : α) := prefixCongr23 test (ha w)
  have inB (w : α) : prefix23 test (d-1) (B w) = prefix23 test (d-1) w :=
    prefixCongr23 test (fun j hj => hb w j (by omega))
  have point (w : α) : f (d+1) w+f (d+1) (A w)+f (d+1) (B w)+f (d+1) (A (B w))
       ≤ f d w+f d (B w)+f (d-1) w := by
    simp only [f,prefix23,inA]
    exact four23 _ _ _ _ _ _ _ (lower w) (fun h => (inB w) ▸ lower (B w) h) (sq w)
  have all := Finset.sum_le_sum (s:=Finset.univ) (fun w _ => point w)
  simp only [Finset.sum_add_distrib,Equiv.sum_comp A (f (d+1)),Equiv.sum_comp B (f (d+1)),Equiv.sum_comp B (f d),
    Equiv.sum_comp B (fun w => f (d+1) (A w))] at all
  change 4*(∑ w, f (d+1) w) ≤ 2*(∑ w, f d w)+(∑ w, f (d-1) w)
  omega

theorem fibonacci23 {α : Type} [Fintype α] (k q : Nat) (test : α → Nat → Bool)
    (hq : q+1≤k) (card : Fintype.card α=2^k)
    (law : ∀ d, d<q → ∃ A B : Equiv.Perm α,
        (∀ w j, j<d → test (A w) j=test w j) ∧
        (∀ w j, j+1<d → test (B w) j=test w j) ∧
        (∀ w, ¬(test w d=true ∧ test (A w) d=true ∧ test (B w) d=true ∧ test (A (B w)) d=true))) :
    (Finset.univ.filter (fun w : α => prefix23 test q w)).card ≤ 2^(k-(q+1))*Nat.fib (q+3) := by
  have initial : count23 test 0 = 2^k := by simp [count23,prefix23,card]
  have recur (d : Nat) (hd : d<q) : 4*count23 test (d+1) ≤ 2*count23 test d+count23 test (d-1) := by
    obtain ⟨A,B,a,b,s⟩ := law d hd
    exact recurse23 test d A B a b s
  have value (j : Nat) (hj : j≤q) : count23 test j ≤ 2^(k-(j+1))*Nat.fib (j+3) := by
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      rcases j with _|(_|t)
      · rw [initial,show (0:Nat)+3=3 by decide,show Nat.fib 3=2 by decide]
        change 2^k ≤ 2^(k-1)*2
        rw [←Nat.pow_succ,show (k-1).succ=k by omega]
      · have R := recur 0 (by omega)
        change 4*count23 test 1≤2*count23 test 0+count23 test 0 at R
        rw [initial] at R
        rw [show k=k-2+2 by omega,pow_add] at R
        change count23 test 1 ≤ 2^(k-2)*Nat.fib 4
        rw [show Nat.fib 4=3 by decide]
        omega
      · have R := recur (t+1) (by omega)
        simp only [Nat.add_sub_cancel] at R
        have G := ih (t+1) (by omega) (by omega)
        have F := ih t (by omega) (by omega)
        let a := 2^(k-(t+3))
        have g : 2^(k-(t+1+1))=2*a := by
          dsimp [a]; rw [show k-(t+1+1)=k-(t+3)+1 by omega,pow_succ];omega
        have f : 2^(k-(t+1))=4*a := by
          dsimp [a]; rw [show k-(t+1)=k-(t+3)+2 by omega,pow_add];omega
        rw [g,Nat.mul_assoc] at G
        rw [f,Nat.mul_assoc] at F
        change count23 test (t+2) ≤ a*Nat.fib ((t+3)+2)
        rw [Nat.fib_add_two,Nat.mul_add]
        change 4*count23 test (t+2) ≤ 2*count23 test (t+1)+count23 test t at R
        rw [show t+1+3=t+3+1 by omega] at G
        omega
  have eq : (Finset.univ.filter (fun w : α => prefix23 test q w)).card = count23 test q := by
    unfold count23
    have cv (w : α) : (prefix23 test q w).toNat = if prefix23 test q w then 1 else 0 := by
      cases prefix23 test q w <;> rfl
    simp only [cv,Finset.sum_boole,Nat.cast_id]
  exact eq ▸ value q le_rfl

end PEqualNP.Outside.L_meta_25523_aux

namespace PEqualNP.Outside.L_meta_25523_aux

open PEqualNP.Outside.L_meta_25504_aux

def test23 {k h : Nat} (c : Nat → Fin (2^k)) (row : Fin (2^k))
    (target : Fin (2^h)) (w : Fin (2^k)) (d : Nat) : Bool :=
  (first k c row.val w.val).testBit (k-1-d) == target.val.testBit (h-1-d)

theorem local23 {k} (hk : 13 ≤ k) (c : Nat → Fin (2^k)) (row w z : Fin (2^k))
    (i : Fin k) (eqs : ∀ t : Fin 12,
        w.val.testBit ((i.val+k-3+t.val)%k) = z.val.testBit ((i.val+k-3+t.val)%k)) :
    (first k c row.val w.val).testBit i.val = (first k c row.val z.val).testBit i.val := by
  apply PEqualNP.Outside.L_meta_25504_aux.main k hk c i row w row z
  · intro t
    rw [Nat.testBit_xor, Nat.testBit_xor, rot_testBit _ _ _ _ w.isLt (Nat.mod_lt _ (by omega)),
      rot_testBit _ _ _ _ z.isLt (Nat.mod_lt _ (by omega)), Nat.mod_eq_of_lt (show 1 < k by omega)]
    have he : ((i.val+k-2+t.val)%k+k-1)%k = (i.val+k-3+t.val)%k := by
      rw [show i.val+k-2+t.val=i.val+k-3+(t.val+1) by omega]
      exact P_sub k (i.val+k-3) t.val 1 (by omega)
    rw [he, eqs]
  · intro t
    rfl

def toggle23 {k} (p : Fin k) : Equiv.Perm (Fin (2^k)) where
  toFun w := ⟨w.val ^^^ 2^p.val,
    Nat.xor_lt_two_pow w.isLt (Nat.pow_lt_pow_right (by decide) p.isLt)⟩
  invFun w := ⟨w.val ^^^ 2^p.val,
    Nat.xor_lt_two_pow w.isLt (Nat.pow_lt_pow_right (by decide) p.isLt)⟩
  left_inv w := by apply Fin.ext; simp
  right_inv w := by apply Fin.ext; simp

theorem mod_gap23 {k b a : Nat} (hb : b<k) (h1 : b<a) (h2 : a<b+k) : a%k ≠ b := by
  by_cases ha : a<k
  · rw [Nat.mod_eq_of_lt ha]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

theorem earlier23 {k h} (hk : 13≤k) (c : Nat → Fin (2^k)) (row : Fin (2^k))
    (target : Fin (2^h)) (j : Nat) (p : Fin k) (hp : p.val<k-1-j-3)
    (hspan : k-1-j-3+11 < p.val + k) (hj : j<k-3) (w : Fin (2^k)) :
    test23 c row target (toggle23 p w) j = test23 c row target w j := by
  unfold test23
  congr 1
  apply local23 hk c row _ _ (⟨k-1-j, by omega⟩ : Fin k)
  intro t
  change (w.val ^^^ 2^p.val).testBit _ = w.val.testBit _
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  have ht := t.isLt
  have he : (k-1-j+k-3+t.val)%k=(k-1-j-3+t.val)%k := by
    rw [show k-1-j+k-3+t.val=(k-1-j-3+t.val)+k by omega, Nat.add_mod_right]
  have hn := mod_gap23 (k:=k) p.isLt (a:=k-1-j-3+t.val) (by omega) (by omega)
  simp [he, hn, Ne.symm hn]

theorem law23 {k h} (hk : 13≤k) (c : Nat → Fin (2^k)) (row : Fin (2^k))
    (target : Fin (2^h)) (d : Nat) (hd : d < min h (k-11)) :
    ∃ A B : Equiv.Perm (Fin (2^k)),
      (∀ w j, j<d → test23 c row target (A w) j=test23 c row target w j) ∧
      (∀ w j, j+1<d → test23 c row target (B w) j=test23 c row target w j) ∧
      (∀ w, ¬(test23 c row target w d=true ∧ test23 c row target (A w) d=true ∧
        test23 c row target (B w) d=true ∧ test23 c row target (A (B w)) d=true)) := by
  let i : Fin k := ⟨k-1-d, by omega⟩
  let p : Fin k := ⟨k-4-d, by omega⟩
  let s : Fin k := ⟨k-3-d, by omega⟩
  refine ⟨toggle23 p, toggle23 s, ?_, ?_, ?_⟩
  · intro w j hj
    exact earlier23 hk c row target j p (by dsimp [p]; omega) (by dsimp [p]; omega) (by omega) w
  · intro w j hj
    exact earlier23 hk c row target j s (by dsimp [s]; omega) (by dsimp [s]; omega) (by omega) w
  · intro w ⟨h0,h1,h2,h3⟩
    have sq := PEqualNP.Outside.L_meta_25522 k hk c row w i
    change xor (xor ((first k c row.val w.val).testBit i.val)
      ((first k c row.val (w.val ^^^ 2^((i.val+k-3)%k))).testBit i.val))
      (xor ((first k c row.val (w.val ^^^ 2^((i.val+k-2)%k))).testBit i.val)
      ((first k c row.val (w.val ^^^ 2^((i.val+k-3)%k) ^^^ 2^((i.val+k-2)%k))).testBit i.val)) = true at sq
    have ep : (i.val+k-3)%k=p.val := by
      dsimp [i,p]
      rw [show k-1-d+k-3=k-4-d+k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have es : (i.val+k-2)%k=s.val := by
      dsimp [i,s]
      rw [show k-1-d+k-2=k-3-d+k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [ep,es] at sq
    have eswap : w.val ^^^ 2^p.val ^^^ 2^s.val = w.val ^^^ 2^s.val ^^^ 2^p.val := by ac_rfl
    rw [eswap] at sq
    simp only [test23, beq_iff_eq] at h0 h1 h2 h3
    change (first k c row.val (w.val ^^^ 2^p.val)).testBit i.val = _ at h1
    change (first k c row.val (w.val ^^^ 2^s.val)).testBit i.val = _ at h2
    change (first k c row.val (w.val ^^^ 2^s.val ^^^ 2^p.val)).testBit i.val = _ at h3
    change (first k c row.val w.val).testBit i.val = _ at h0
    simp [h0,h1,h2,h3] at sq

end PEqualNP.Outside.L_meta_25523_aux

namespace PEqualNP.Outside.L_meta_25523_aux
open PEqualNP.Outside.L_meta_25504_aux

private theorem range23 (N : Nat) (p : Nat → Bool) :
    ((List.range N).filter p).length = (Finset.univ.filter (fun w : Fin N => p w.val)).card := by
  have eqr : (List.range N).toFinset = Finset.range N := by ext; simp
  have mem := (List.nodup_range (n:=N)).card_eq_countP (P:=fun i => p i = true)
  rw [eqr] at mem
  simp only [Bool.decide_eq_true] at mem
  rw [← List.countP_eq_length_filter,← mem]
  apply Finset.card_bij (fun i hi => (⟨i,Finset.mem_range.mp (Finset.mem_filter.mp hi).1⟩ : Fin N))
  · intro i hi; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
  · intro i hi j hj h; exact congrArg Fin.val h
  · intro b hb
    exact ⟨b.val,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr b.isLt,(Finset.mem_filter.mp hb).2⟩,rfl⟩

theorem bound23 {k h : Nat} (hk:13≤k) (hpos:0<h) (hh:h≤k)
    (c : Nat → Fin (2^k)) (row : Fin (2^k)) (target : Fin (2^h)) :
    ((List.range (2^k)).filter (fun w => decide (first k c row.val w >>> (k-h) = target.val))).length ≤
      2^(k-(min h (k-11)+1))*Nat.fib (min h (k-11)+3) := by
  let q := min h (k-11)
  have qSmall : q≤k-11 := Nat.min_le_right .. 
  have qh : q≤h := Nat.min_le_left .. 
  rw [range23]
  apply le_trans (b := (Finset.univ.filter (fun w => prefix23 (test23 c row target) q w)).card)
  · apply Finset.card_le_card
    intro w hw
    obtain ⟨_,he⟩ := Finset.mem_filter.mp hw
    simp only [decide_eq_true_eq] at he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, (prefixIff23 ..).mpr ?_⟩
    intro j hj
    have b := congrArg (fun v : Nat => v.testBit (h-1-j)) he
    simp only [Nat.testBit_shiftRight] at b
    rw [show k-h+(h-1-j) = k-1-j by omega] at b
    simpa only [test23,beq_iff_eq] using b
  · exact fibonacci23 k q (test23 c row target) (by omega) (Fintype.card_fin _)
      (law23 hk c row target)

end PEqualNP.Outside.L_meta_25523_aux

theorem PEqualNP.Outside.L_meta_25523 :
∀ (k h : Nat), 13 ≤ k → 0 < h → h ≤ k →
  ∀ (c : Nat → Fin (2 ^ k)) (u : Fin (2 ^ k)) (target : Fin (2 ^ h)),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc j =>
      acc ||| ((xor (word.testBit j)
        (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0
  let start := fun (row key : Nat) => rot 1 key ^^^ row
  let first := fun (row key : Nat) =>
    (List.range 3).foldl (fun prev roundIndex =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * roundIndex) key ^^^ (c (roundIndex + 1)).val)
      (start row key)
  let q := min h (k - 11)
  ((List.range (2 ^ k)).filter (fun w =>
    decide ((first u.val w >>> (k - h)) = target.val))).length ≤
    2 ^ (k - (q + 1)) * Nat.fib (q + 3) := by
  intro k h hk hp hh c row target
  exact PEqualNP.Outside.L_meta_25523_aux.bound23 hk hp hh c row target
