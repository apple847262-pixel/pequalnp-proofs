import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_25547_aux

def gain (a : Fin 16) : Nat :=
  if a.val < 4 then 0 else if a.val < 12 then 1 else if a.val < 15 then 2 else 3

def slots (n k d : Nat) :=
  ∑ history : Fin n → Fin 16,
    (2 : Nat) ^ (k - 4 * n - ((∑ i : Fin n, gain (history i)) - d))

end PEqualNP.Outside.L_meta_25547_aux

namespace PEqualNP.Outside.L_meta_25547_aux

private theorem point47 (B d g : Nat) (hg : g≤B) :
    (2:ℝ)^(B-(g-d))*(15/16:ℝ)^d ≤ (2:ℝ)^B*(15/16:ℝ)^g := by
  by_cases h : g≤d
  · rw [Nat.sub_eq_zero_of_le h,Nat.sub_zero]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) h) (by positivity)
  · let v := g-d
    have eg : g=d+v := by dsimp [v];omega
    have eB : B=(B-v)+v := by dsimp [v];omega
    have grow : (1:ℝ) ≤ (2*(15/16))^v := one_le_pow₀ (by norm_num)
    have bound := mul_le_mul_of_nonneg_left grow
      (mul_nonneg (by positivity : (0:ℝ)≤2^(B-v)) (pow_nonneg (by norm_num : 0≤(15/16:ℝ)) d))
    rw [mul_one,mul_pow] at bound
    change (2:ℝ)^(B-v)*(15/16:ℝ)^d ≤ _
    conv_rhs => rw [eB,eg,pow_add,pow_add]
    calc _ ≤ _ := bound
         _ = _ := by ring

theorem gainMoment47 (n : Nat) :
    (∑ h : Fin n → Fin 16, (15/16:ℝ)^(∑ i, gain (h i))) = (61279/4096:ℝ)^n := by
  have letter : (∑ a : Fin 16, (15/16:ℝ)^(gain a))=(61279/4096:ℝ) := by
    norm_num [Fin.sum_univ_succ,gain]
  rw [←letter,Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro h _
  exact (Finset.prod_pow_eq_pow_sum _ _ _).symm

theorem slotMoment47 {n k d : Nat} (wide : 7*n≤k) :
    (slots n k d:ℝ)*(15/16:ℝ)^d ≤ (2:ℝ)^k*(61279/65536:ℝ)^n := by
  have gainCap (a : Fin 16) : gain a ≤ 3 := by unfold gain; split <;> (repeat' split) <;> decide
  have cap (h : Fin n → Fin 16) : (∑ i, gain (h i)) ≤ k-4*n := by
    have H := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => gainCap (h i))
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at H
    omega
  rw [slots,Nat.cast_sum,Finset.sum_mul]
  calc
    _ ≤ ∑ h : Fin n → Fin 16, (2:ℝ)^(k-4*n)*(15/16:ℝ)^(∑ i, gain (h i)) := by
      apply Finset.sum_le_sum
      intro h _
      push_cast
      exact point47 _ _ _ (cap h)
    _ = (2:ℝ)^(k-4*n)*(61279/4096:ℝ)^n := by rw [← Finset.mul_sum,gainMoment47]
    _ = _ := by
      have eq : (61279/4096:ℝ)=2^4*(61279/65536:ℝ) := by norm_num
      rw [eq,mul_pow,←pow_mul,←mul_assoc,←pow_add,Nat.sub_add_cancel (by omega)]

end PEqualNP.Outside.L_meta_25547_aux

namespace PEqualNP.Outside.L_meta_25547_aux
theorem scaleCost47 {s : Nat} (_hs : 0<s) :
    (61279/65536:ℝ)^(32*s)*(2:ℝ)^(s/64) ≤ (15/16:ℝ)^(33*s) := by
  have two : (2:ℝ)≤(65/64:ℝ)^64 := by norm_num
  have grow : (2:ℝ)^(s/64)≤(65/64:ℝ)^s := by
    calc
      _ ≤ ((65/64:ℝ)^64)^(s/64) := pow_le_pow_left₀ (by norm_num) two _
      _ = (65/64:ℝ)^(64*(s/64)) := (pow_mul ..).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have localbound : (61279/65536:ℝ)^32*(65/64)≤(15/16:ℝ)^33 := by norm_num
  rw [pow_mul,pow_mul]
  calc
    _ ≤ ((61279/65536:ℝ)^32)^s*(65/64:ℝ)^s := mul_le_mul_of_nonneg_left grow (by positivity)
    _ = ((61279/65536:ℝ)^32*(65/64))^s := (mul_pow ..).symm
    _ ≤ _ := pow_le_pow_left₀ (by positivity) localbound _
end PEqualNP.Outside.L_meta_25547_aux

namespace PEqualNP.Outside.L_meta_25547_aux

theorem upperFromRatio47 (s : Nat)
    (ratio : (61279/65536:ℝ)^(32*s)*(2:ℝ)^(s/64) ≤ (15/16:ℝ)^(33*s)) :
    slots (32*s) (287*s+22) (33*s) ≤ 2^(287*s+22-s/64) := by
  let n := 32*s
  let k := 287*s+22
  let d := 33*s
  let j := s/64
  have wide : 7*n≤k := by dsimp [n,k];omega
  have sub : j≤k := by dsimp [j,k];omega
  have z : 0<(15/16:ℝ)^d := by positivity
  have bound := slotMoment47 (d:=d) wide
  have priceBound : (slots n k d:ℝ)*(2:ℝ)^j ≤ (2:ℝ)^k := by
    apply le_of_mul_le_mul_right _ z
    calc
      _ = ((slots n k d:ℝ)*(15/16:ℝ)^d)*(2:ℝ)^j := by ring
      _ ≤ ((2:ℝ)^k*(61279/65536:ℝ)^n)*(2:ℝ)^j :=
        mul_le_mul_of_nonneg_right bound (by positivity)
      _ = (2:ℝ)^k*((61279/65536:ℝ)^n*(2:ℝ)^j) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ratio (by positivity)
  have result : slots n k d*2^j ≤ 2^k := by exact_mod_cast priceBound
  rw [show (2:Nat)^k=2^(k-j)*2^j by rw [←pow_add,Nat.sub_add_cancel sub]] at result
  exact Nat.le_of_mul_le_mul_right result (Nat.two_pow_pos _)

end PEqualNP.Outside.L_meta_25547_aux

namespace PEqualNP.Outside.L_meta_25547_aux

theorem upper47 (s : Nat) (hs:0<s) :
    slots (32*s) (287*s+22) (33*s) ≤ 2^(287*s+22-s/64) :=
  upperFromRatio47 s (scaleCost47 hs)

end PEqualNP.Outside.L_meta_25547_aux

namespace PEqualNP.Outside.L_meta_25547_aux

private theorem total47 (n : Nat) :
  16*(∑ w : Fin n → Fin 16, ∑ i, gain (w i)) = (16^n)*(17*n) := by
  classical
  cases n with
  | zero => simp
  | succ n =>
    have digit (i : Fin (n+1)) : (∑ w : Fin (n+1) → Fin 16, gain (w i)) = 16^n*17 := by
      let e := Fin.insertNthEquiv (fun _ : Fin (n+1) => Fin 16) i
      rw [← e.sum_comp (fun w => gain (w i)), Fintype.sum_prod_type]
      simp only [e,Fin.insertNthEquiv_apply,Fin.insertNth_apply_same, Finset.sum_const,
        Finset.card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,←Finset.mul_sum]
      have hg : (∑ a : Fin 16, gain a) = 17 := by decide +kernel
      rw [hg]
      simp
    rw [Finset.sum_comm]
    simp only [digit,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,pow_succ]
    push_cast
    ring

theorem lower47 (n k d : Nat) (hk : 4*n ≤ k) (hd : 17*n/16 ≤ d) :
    2^k ≤ 16*(d+1)*slots n k d := by
  classical
  let A := (Finset.univ : Finset (Fin n → Fin 16))
  let score := fun (w : Fin n → Fin 16) => ∑ i, gain (w i)
  let above := A.filter (fun w => d < score w)
  let full := A.filter (fun w => ¬ d < score w)
  have cardA : A.card = 16^n := by simp [A]
  have split : above.card + full.card = 16^n :=
    (Finset.card_filter_add_card_filter_not (s:=A) (fun w => d < score w)).trans cardA
  have small : above.card*(d+1) ≤ ∑ w ∈ A, score w := calc
    _ = ∑ w ∈ above, (d+1) := by simp
    _ ≤ ∑ w ∈ above, score w := Finset.sum_le_sum (fun w hw => (Finset.mem_filter.mp hw).2)
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have h := Nat.mul_le_mul_left 16 small
  have tot := total47 n
  change 16*(∑ w ∈ A, score w) = _ at tot
  rw [tot] at h
  have hr : 17*n+1 ≤ 16*(d+1) := by omega
  have h' := Nat.mul_le_mul_left (16^n) hr
  have enough : 16^n ≤ 16*(d+1)*full.card := by
    rw [←split] at h h' ⊢
    nlinarith
  have pay : full.card * 2^(k-4*n) ≤ slots n k d := calc
    _ = ∑ w ∈ full, 2^(k-4*n) := by simp
    _ = ∑ w ∈ full, 2^(k-4*n-(score w-d)) := by
      apply Finset.sum_congr rfl
      intro w hw
      have hg := (Finset.mem_filter.mp hw).2
      rw [Nat.sub_eq_zero_of_le (show score w ≤ d by omega), Nat.sub_zero]
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  calc
    2^k = 16^n * 2^(k-4*n) := by
      rw [show (16:Nat)=2^4 by decide,←pow_mul,←pow_add,Nat.add_sub_of_le hk]
    _ ≤ (16*(d+1)*full.card)*2^(k-4*n) := Nat.mul_le_mul_right _ enough
    _ = 16*(d+1)*(full.card*2^(k-4*n)) := Nat.mul_assoc ..
    _ ≤ _ := Nat.mul_le_mul_left _ pay

end PEqualNP.Outside.L_meta_25547_aux

theorem PEqualNP.Outside.L_meta_25547 :
let gain := fun (a : Fin 16) =>
  if a.val < 4 then 0 else if a.val < 12 then 1 else if a.val < 15 then 2 else 3
let slots := fun (n k d : Nat) =>
  ∑ history : Fin n → Fin 16,
    (2 : Nat) ^ (k - 4 * n - ((∑ i : Fin n, gain (history i)) - d))
(∀ scale : Nat, 0 < scale →
  slots (32 * scale) (287 * scale + 22) (33 * scale) ≤
    2 ^ (287 * scale + 22 - scale / 64)) ∧
(∀ (n k d : Nat), 4 * n ≤ k → 17 * n / 16 ≤ d →
  2 ^ k ≤ 16 * (d + 1) * slots n k d) := by
  dsimp only
  exact ⟨PEqualNP.Outside.L_meta_25547_aux.upper47, PEqualNP.Outside.L_meta_25547_aux.lower47⟩
