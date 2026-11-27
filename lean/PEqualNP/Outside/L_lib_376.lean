import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_376_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem ofFn_getD_ge {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : n ≤ u) :
    (List.ofFn x).getD u false = false := getD_ge _ _ (by simpa using hu)

theorem ev_W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem ev_getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

theorem ev_getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

theorem ev_getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact ev_getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

def ev_OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def ev_statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def ev_statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def ev_simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def ev_simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def ev_simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def ev_simp (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => ev_simpAnd m ins
  | GateOp.or => ev_simpOr m ins
  | GateOp.not => ev_simpNot m ins
  | _ => (none, Sum.inl false)

theorem ev_simp_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (ev_simp op m ins).1, ev_OkGate g := by
  intro g hg
  cases op <;> simp only [ev_simp] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [ev_simpAnd] at hg
    subst hg; simp [ev_OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [ev_simpOr] at hg
    subst hg; simp [ev_OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [ev_simpNot] at hg
    subst hg; simp [ev_OkGate]
  · simp at hg
  · simp at hg

theorem ev_simp_none_of_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (ev_simp op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [ev_simp, ev_simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [ev_simp, ev_simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [ev_simp, ev_simpNot]

theorem ev_simp_and_false (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (hf : Sum.inl false ∈ ins) :
    ev_simp GateOp.and m ins = (none, Sum.inl false) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at hf
  · cases a <;> simp_all [ev_simp, ev_simpAnd]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [ev_simp, ev_simpAnd]
      | inr j => cases c <;> simp_all [ev_simp, ev_simpAnd]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [ev_simp, ev_simpAnd]
      | inr j => simp at hf
  · simp at hlen

theorem ev_simp_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, ev_statValid w.length s) :
    ev_statValid (w.length + (ev_simp op w.length ins).1.toList.length)
      (ev_simp op w.length ins).2 ∧
    ev_statVal (W (ev_simp op w.length ins).1.toList w)
      (ev_simp op w.length ins).2 = op.eval (ins.map (ev_statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [ev_simp, ev_simpAnd, ev_statValid, ev_statVal, GateOp.eval]
    · cases a <;> simp_all [ev_simp, ev_simpAnd, ev_statValid, ev_statVal, GateOp.eval, W, step]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [ev_simp, ev_simpAnd, ev_statValid, ev_statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [ev_simp, ev_simpAnd, ev_statValid, ev_statVal, GateOp.eval, W, step]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [ev_simp, ev_simpAnd, ev_statValid, ev_statVal, GateOp.eval, W, step]
        | inr j => simp_all [ev_simp, ev_simpAnd, ev_statValid, ev_statVal, GateOp.eval, W, step]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [ev_simp, ev_simpOr, ev_statValid, ev_statVal, GateOp.eval]
    · cases a <;> simp_all [ev_simp, ev_simpOr, ev_statValid, ev_statVal, GateOp.eval, W, step]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [ev_simp, ev_simpOr, ev_statValid, ev_statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [ev_simp, ev_simpOr, ev_statValid, ev_statVal, GateOp.eval, W, step]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [ev_simp, ev_simpOr, ev_statValid, ev_statVal, GateOp.eval, W, step]
        | inr j => simp_all [ev_simp, ev_simpOr, ev_statValid, ev_statVal, GateOp.eval, W, step]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [ev_simp, ev_simpNot, ev_statValid, ev_statVal, GateOp.eval]
    · cases a <;> simp_all [ev_simp, ev_simpNot, ev_statValid, ev_statVal, GateOp.eval, W, step]

def ev_elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := ev_simp g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def ev_elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (ev_elimStep m) acc

theorem ev_elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    ev_elimPass m (g :: gs) acc = ev_elimPass m gs (ev_elimStep m acc g) := rfl

theorem ev_elimPass_append (m : ℕ) (gs₁ gs₂ : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    ev_elimPass m (gs₁ ++ gs₂) acc = ev_elimPass m gs₂ (ev_elimPass m gs₁ acc) := by
  induction gs₁ generalizing acc with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, ev_elimPass_cons, ih]

theorem ev_elimPass_fst_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (ev_elimPass m gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [ev_elimPass]
  | cons g gs ih =>
    rw [ev_elimPass_cons, ih]
    simp [ev_elimStep]
    omega

theorem ev_elimPass_getD_lt (m k : ℕ) (d : Bool ⊕ ℕ) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) (hk : k < acc.1.length) :
    (ev_elimPass m gs acc).1.getD k d = acc.1.getD k d := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [ev_elimPass_cons, ih _ (by simp [ev_elimStep]; omega)]
    exact ev_getD_snoc_lt _ _ _ _ hk

theorem ev_toList_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem ev_elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, ev_OkGate g) : ∀ g ∈ (ev_elimPass m gs acc).2, ev_OkGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [ev_elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact ev_simp_ok _ _ _ g' (by simpa using h1)

def ev_Inv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    ev_statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    ev_statVal (W acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

theorem ev_Inv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : ev_OkGate g)
    (hinv : ev_Inv m w_in w_old acc) :
    ev_Inv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (ev_elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := W acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, W_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, ev_statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := ev_simp_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [ev_elimStep, hlen], ?_⟩
  intro i
  simp only [ev_elimStep]
  by_cases hieq : i = acc.1.length
  · rw [ev_getD_snoc_eq _ _ _ _ hieq, ev_getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [W_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [ev_getD_snoc_ne _ _ _ _ hieq, ev_getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [ev_statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [ev_statValid] at hv
        simp only [ev_statVal] at hval ⊢
        rw [W_append, ← hw_new, W_prefix _ _ _ (by omega)]
        exact hval

theorem ev_Inv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, ev_OkGate g) (hinv : ev_Inv m w_in w_old acc) :
    ev_Inv m w_in (W gs w_old) (ev_elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [ev_W_cons, ev_elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (ev_Inv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)

theorem ev_ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

def RBo (b : ℕ) (gs : List Gate) : Prop :=
  ∀ p < gs.length, ∀ i ∈ (gs.getD p ⟨GateOp.or, []⟩).inputs, i < b + p

theorem RBo_nil (b : ℕ) : RBo b [] := by
  intro p hp
  simp at hp

theorem RBo_append (b : ℕ) (g1 g2 : List Gate) (h1 : RBo b g1)
    (h2 : RBo (b + g1.length) g2) : RBo b (g1 ++ g2) := by
  intro p hp i hi
  by_cases hlt : p < g1.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    exact h1 p hlt i hi
  · have hge : g1.length ≤ p := by omega
    rw [List.getD_append_right _ _ _ _ hge] at hi
    have hp2 : p - g1.length < g2.length := by
      rw [List.length_append] at hp
      omega
    have := h2 (p - g1.length) hp2 i hi
    omega

def pt (n m a b : ℕ) : Fin (n + m) → Bool := fun k => decide (k.val = a) || decide (k.val = b)

theorem oneEach_pt (n m : ℕ) (u : Fin n) (v : Fin m) :
    PEqualNP.Represents.oneEach u v = List.ofFn (pt n m u.val (n + v.val)) := by
  rw [List.ofFn_add]
  unfold PEqualNP.Represents.oneEach
  have hu := u.isLt
  have hv := v.isLt
  congr 1
  · congr 1
    funext k
    have hk := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [pt, decide_eq_true_eq, Bool.or_eq_true, Fin.ext_iff, Fin.val_castAdd, Fin.coe_castLE]
    omega
  · congr 1
    funext k
    have hk := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [pt, decide_eq_true_eq, Bool.or_eq_true, Fin.ext_iff, Fin.coe_natAdd]
    omega

theorem oe_getD (n m : ℕ) (u : Fin n) (v : Fin m) (k : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD k false = true ↔ (k = u.val ∨ k = n + v.val) := by
  rw [oneEach_pt]
  have hu := u.isLt
  have hv := v.isLt
  by_cases hk : k < n + m
  · rw [ofFn_getD _ k hk]
    simp [pt]
  · rw [ofFn_getD_ge _ k (by omega)]
    simp only [Bool.false_eq_true, false_iff]
    omega

theorem oe_len (n m : ℕ) (u : Fin n) (v : Fin m) :
    (PEqualNP.Represents.oneEach u v).length = n + m := by
  rw [oneEach_pt, List.length_ofFn]

theorem sa_val {m : ℕ} (k : Fin (m + 1)) (v : Fin m) :
    (k.succAbove v).val = if v.val < k.val then v.val else v.val + 1 := by
  split_ifs with h
  · rw [Fin.succAbove_of_castSucc_lt k v (by rw [Fin.lt_def, Fin.coe_castSucc]; exact h)]
    simp
  · rw [Fin.succAbove_of_le_castSucc k v (by rw [Fin.le_def, Fin.coe_castSucc]; omega)]
    simp

theorem simp_gate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (ev_simp op m ins).1, ∀ j ∈ g.inputs, Sum.inr j ∈ ins := by
  intro g hg j hj
  cases op <;> simp only [ev_simp] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try rcases a with (_ | _) | a) <;>
      (try rcases b with (_ | _) | b) <;> simp [ev_simpAnd] at hg <;> subst hg <;> simp at hj ⊢ <;>
      omega
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try rcases a with (_ | _) | a) <;>
      (try rcases b with (_ | _) | b) <;> simp [ev_simpOr] at hg <;> subst hg <;> simp at hj ⊢ <;>
      omega
  · rcases ins with _ | ⟨a, l⟩ <;> (try rcases a with (_ | _) | a) <;> simp [ev_simpNot] at hg <;>
      subst hg <;> simp at hj ⊢ <;> omega
  · simp at hg
  · simp at hg

def initR (N K : ℕ) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i : Fin N =>
    if i.val < K then Sum.inr i.val else if i.val = K then Sum.inl false else Sum.inr (i.val - 1)

theorem initR_len (N K : ℕ) : (initR N K).length = N := by
  rw [initR, List.length_ofFn]

theorem initR_getD (N K i : ℕ) (hi : i < N) :
    (initR N K).getD i (Sum.inl false) =
      if i < K then Sum.inr i else if i = K then Sum.inl false else Sum.inr (i - 1) := by
  rw [initR, ev_ofFn_getD_lt _ _ _ hi]

theorem inv_init (n m : ℕ) (k : Fin (n + 1)) (u : Fin n) (v : Fin m) :
    ev_Inv (n + m) (PEqualNP.Represents.oneEach u v) (PEqualNP.Represents.oneEach (k.succAbove u) v)
      (initR (n + 1 + m) k.val, []) := by
  have hk := k.isLt
  have hu := u.isLt
  have hv := v.isLt
  have hsa := sa_val k u
  refine ⟨oe_len n m u v, by rw [initR_len, oe_len], ?_⟩
  intro i
  by_cases hi : i < n + 1 + m
  · rw [initR_getD _ _ i hi]
    split_ifs with h1 h2
    · refine ⟨by simp only [ev_statValid]; omega, ?_⟩
      show (PEqualNP.Represents.oneEach u v).getD i false = _
      rw [Bool.eq_iff_iff, oe_getD, oe_getD, hsa]
      split_ifs <;> omega
    · refine ⟨trivial, ?_⟩
      show false = _
      symm
      rw [← Bool.not_eq_true, oe_getD, hsa]
      split_ifs <;> omega
    · refine ⟨by simp only [ev_statValid]; omega, ?_⟩
      show (PEqualNP.Represents.oneEach u v).getD (i - 1) false = _
      rw [Bool.eq_iff_iff, oe_getD, oe_getD, hsa]
      split_ifs <;> omega
  · rw [List.getD_eq_default _ _ (by rw [initR_len]; omega)]
    refine ⟨trivial, ?_⟩
    show false = _
    rw [List.getD_eq_default _ _ (by rw [oe_len]; omega)]

def st (M : ℕ) (gs : List Gate) (a0 : List (Bool ⊕ ℕ) × List Gate) (t : ℕ) :
    List (Bool ⊕ ℕ) × List Gate := ev_elimPass M (gs.take t) a0

theorem st_succ (M : ℕ) (gs : List Gate) (a0 : List (Bool ⊕ ℕ) × List Gate) (t : ℕ)
    (ht : t < gs.length) : st M gs a0 (t + 1) = ev_elimStep M (st M gs a0 t) gs[t] := by
  unfold st
  rw [List.take_succ, List.getElem?_eq_getElem ht, ev_elimPass_append]
  rfl

theorem st_len1 (M : ℕ) (gs : List Gate) (a0 : List (Bool ⊕ ℕ) × List Gate) (t : ℕ)
    (ht : t ≤ gs.length) : (st M gs a0 t).1.length = a0.1.length + t := by
  unfold st
  rw [ev_elimPass_fst_len, List.length_take]
  omega

theorem st_stable (M : ℕ) (gs : List Gate) (a0 : List (Bool ⊕ ℕ) × List Gate) (t t' i : ℕ)
    (htt : t ≤ t') (ht' : t' ≤ gs.length) (hi : i < (st M gs a0 t).1.length) :
    (st M gs a0 t').1.getD i (Sum.inl false) = (st M gs a0 t).1.getD i (Sum.inl false) := by
  have e : gs.take t' = gs.take t ++ (gs.drop t).take (t' - t) := by
    conv_lhs => rw [show t' = t + (t' - t) by omega]
    rw [List.take_add]
  unfold st at hi ⊢
  rw [e, ev_elimPass_append, ev_elimPass_getD_lt _ _ _ _ _ hi]

def idx (s : Bool ⊕ ℕ) : ℕ := Sum.elim (fun _ => 0) id s

def RedG (g : Gate) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = GateOp.not ∧ g.inputs.length = 1)

theorem simp_red (op : GateOp) (mm : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (ev_simp op mm ins).1, RedG g := by
  intro g hg
  cases op <;> simp only [ev_simp] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try rcases a with (_ | _) | a) <;>
      (try rcases b with (_ | _) | b) <;> simp [ev_simpAnd] at hg <;> subst hg <;> simp [RedG]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try rcases a with (_ | _) | a) <;>
      (try rcases b with (_ | _) | b) <;> simp [ev_simpOr] at hg <;> subst hg <;> simp [RedG]
  · rcases ins with _ | ⟨a, l⟩ <;> (try rcases a with (_ | _) | a) <;> simp [ev_simpNot] at hg <;>
      subst hg <;> simp [RedG]
  · simp at hg
  · simp at hg

theorem pass_red (M : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, RedG g) : ∀ g ∈ (ev_elimPass M gs acc).2, RedG g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [ev_elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simp_red _ _ _ g' (by simpa using h1)

theorem sv_mono (a b : ℕ) (s : Bool ⊕ ℕ) (h : a ≤ b) (hs : ev_statValid a s) : ev_statValid b s := by
  cases s with
  | inl c => trivial
  | inr j => simp only [ev_statValid] at hs ⊢; omega

theorem pass_vrb (M : ℕ) (gs : List Gate) (hok : ∀ g ∈ gs, ev_OkGate g) :
    ∀ acc : List (Bool ⊕ ℕ) × List Gate,
      (∀ i, ev_statValid (M + acc.2.length) (acc.1.getD i (Sum.inl false))) → RBo M acc.2 →
      (∀ i, ev_statValid (M + (ev_elimPass M gs acc).2.length) ((ev_elimPass M gs acc).1.getD i (Sum.inl false))) ∧
        RBo M (ev_elimPass M gs acc).2 := by
  induction gs with
  | nil => intro acc h1 h2; exact ⟨h1, h2⟩
  | cons g gs ih =>
    intro acc h1 h2
    rw [ev_elimPass_cons]
    apply ih (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    · have hg := hok g List.mem_cons_self
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hv : ∀ s ∈ ins, ev_statValid (List.replicate (M + acc.2.length) false).length s := by
        intro s hs
        obtain ⟨i, _, rfl⟩ := List.mem_map.1 hs
        rw [List.length_replicate]
        exact h1 i
      have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
        have := hg.1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
        exact this
      have hsd := (ev_simp_sound g.op hop (List.replicate (M + acc.2.length) false) ins
        (by simp [hins]; exact hg.2) hv).1
      rw [List.length_replicate] at hsd
      intro i
      simp only [ev_elimStep, List.length_append]
      by_cases hlt : i < acc.1.length
      · rw [ev_getD_snoc_lt _ _ _ _ hlt]
        exact sv_mono _ _ _ (by omega) (h1 i)
      · by_cases heq : i = acc.1.length
        · rw [ev_getD_snoc_eq _ _ _ _ heq]
          rw [Nat.add_assoc] at hsd
          exact hsd
        · rw [ev_getD_snoc_ne _ _ _ _ heq, List.getD_eq_default _ _ (by omega)]
          trivial
    · simp only [ev_elimStep]
      apply RBo_append M _ _ h2
      intro p hp i hi
      have hg1 : ∀ g' ∈ (ev_simp g.op (M + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1,
          ∀ j ∈ g'.inputs, j < M + acc.2.length := by
        intro g' hg' j hj
        have hm := simp_gate _ _ _ g' hg' j hj
        obtain ⟨i0, _, hie⟩ := List.mem_map.1 hm
        have := h1 i0
        rw [hie] at this
        exact this
      cases hr : (ev_simp g.op (M + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 with
      | none => rw [hr] at hp; simp at hp
      | some G =>
        rw [hr] at hp hi
        simp at hp
        subst hp
        simp only [Option.toList_some, List.getD_cons_zero] at hi
        have := hg1 G (by rw [hr]; rfl) i hi
        omega
end PEqualNP.Outside.L_lib_376_aux

namespace PEqualNP.Outside.L_lib_376_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def readsWire (g : Gate) (w : Nat) : Prop :=
  (g.op = .not ∧ g.inputs.head? = some w) ∨ (g.op ≠ .not ∧ w ∈ g.inputs)

theorem simpNotHead (g : Gate) (m w : Nat) (f : Nat → Bool ⊕ Nat) (c : Bool)
    (hop : g.op = .not) (hd : g.inputs.head? = some w) (hc : f w = Sum.inl c) :
    ev_simp g.op m (g.inputs.map f) = (none,Sum.inl (!c)) := by
  cases h : g.inputs with
  | nil => simp [h] at hd
  | cons a l =>
    have eq : a = w := by simpa [h] using hd
    rw [hop,eq,List.map_cons,hc]
    rfl

theorem folded (g : Gate) (ok : ev_OkGate g) (m w : Nat) (f : Nat → Bool ⊕ Nat)
    (rd : readsWire g w) (c : Bool) (hc : f w = Sum.inl c) :
    (ev_simp g.op m (g.inputs.map f)).1 = none := by
  rcases rd with ⟨op,head⟩|⟨op,mem⟩
  · exact congrArg Prod.fst (simpNotHead g m w f c op head hc)
  · apply ev_simp_none_of_const
    · exact ok.1
    · simpa using ok.2
    · exact fun e => False.elim (op e)
    · exact ⟨c,List.mem_map.mpr ⟨w,mem,hc⟩⟩

theorem directConst (g : Gate) (ok : ev_OkGate g) (m w : Nat) (f : Nat → Bool ⊕ Nat)
    (rd : readsWire g w) (hop : g.op=.and ∨ g.op=.not) (hc : f w=Sum.inl false) :
    ∃ c : Bool, ev_simp g.op m (g.inputs.map f) = (none,Sum.inl c) := by
  rcases hop with op|op
  · have wr : w∈g.inputs := rd.elim (fun h => by rw [op] at h; cases h.1) And.right
    refine ⟨false,?_⟩
    rw [op]
    exact ev_simp_and_false _ _ (by simpa using ok.2) (List.mem_map.mpr ⟨w,wr,hc⟩)
  · have head : g.inputs.head? = some w := rd.elim And.right (fun h => False.elim (h.1 op))
    exact ⟨true,simpNotHead g m w f false op head hc⟩

theorem markedCount (M : Nat) (gs : List Gate) (a0 : List (Bool ⊕ Nat) × List Gate)
    (K : Finset (Fin gs.length))
    (skips : ∀ j ∈ K, (ev_simp (gs.get j).op (M+(st M gs a0 j.val).2.length)
      ((gs.get j).inputs.map (fun i => (st M gs a0 j.val).1.getD i (Sum.inl false)))).1 = none) :
    (ev_elimPass M gs a0).2.length + K.card ≤ a0.2.length + gs.length := by
  classical
  let marks (t : Nat) := K.filter (fun j => j.val < t)
  have stepMarks (j : Fin gs.length) :
      marks (j.val+1) = if j∈K then insert j (marks j.val) else marks j.val := by
    by_cases h : j∈K <;> simp only [h,ite_true,ite_false]
    · ext p
      by_cases e : p=j
      · subst p; simp [marks,h]
      · have ne : p.val ≠ j.val := fun z => e (Fin.ext z)
        simp [marks,e]
        intro _
        change p.val ≤ j.val ↔ p.val < j.val
        omega
    · ext p
      by_cases e : p=j
      · subst p; simp [marks,h]
      · have ne : p.val ≠ j.val := fun z => e (Fin.ext z)
        simp [marks]
        intro _
        change p.val ≤ j.val ↔ p.val < j.val
        omega
  have bound (t : Nat) (ht : t ≤ gs.length) :
      (st M gs a0 t).2.length + (marks t).card ≤ a0.2.length + t := by
    induction t with
    | zero => simp [st,marks,ev_elimPass]
    | succ t ih =>
      let j : Fin gs.length := ⟨t,by omega⟩
      have prev := ih (by omega)
      rw [st_succ M gs a0 t (by omega)]
      simp only [ev_elimStep,List.length_append]
      let op := (ev_simp gs[t].op (M+(st M gs a0 t).2.length)
        (gs[t].inputs.map fun i => (st M gs a0 t).1.getD i (Sum.inl false))).1
      change (st M gs a0 t).2.length + op.toList.length + (marks (t+1)).card ≤ a0.2.length+(t+1)
      have eq := stepMarks j
      change marks (t+1) = if j∈K then insert j (marks t) else marks t at eq
      rw [eq]
      by_cases mem : j∈K
      · rw [if_pos mem,Finset.card_insert_of_notMem (by simp [marks,j])]
        have h : op = none := skips j mem
        simp only [h,Option.toList_none,List.length_nil]
        omega
      · rw [if_neg mem]
        have := ev_toList_len_le op
        omega
  have h := bound gs.length le_rfl
  have e : marks gs.length = K := by ext j; simp [marks,j.isLt]
  simpa [st,e] using h

theorem witnessInit (M k : Nat) (hk : k<M+1) (x : List Bool) (hx : x.length=M+1)
    (hz : x.getD k false=false) :
    ∃ y : List Bool, ev_Inv M y x (initR (M+1) k,[]) := by
  let y := List.ofFn (fun j : Fin M => x.getD (if j.val<k then j.val else j.val+1) false)
  have get (j : Nat) (hj : j<M) : y.getD j false = x.getD (if j<k then j else j+1) false :=
    ev_ofFn_getD_lt _ false _ hj
  refine ⟨y,by simp [y],by rw [initR_len,hx],?_⟩
  intro i
  by_cases hi : i<M+1
  · rw [initR_getD _ _ _ hi]
    split_ifs with lt eq
    · exact ⟨by change i<M+0;omega,by change y.getD i false = x.getD i false;rw [get i (by omega),if_pos lt]⟩
    · subst i; exact ⟨trivial,hz.symm⟩
    · refine ⟨by change i-1<M+0;omega,?_⟩
      change y.getD (i-1) false = x.getD i false
      rw [get (i-1) (by omega),if_neg (by omega),show i-1+1=i by omega]
  · rw [List.getD_eq_default (initR (M+1) k) _ (by rw [initR_len];omega)]
    exact ⟨trivial,(List.getD_eq_default _ _ (by omega)).symm⟩

def AO (g : Gate) := g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem simpAO (op : GateOp) (m : Nat) (ins : List (Bool ⊕ Nat))
    (hop : op=.and ∨ op=.or) : ∀ g ∈ (ev_simp op m ins).1, AO g := by
  intro g hg
  rcases hop with rfl|rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [ev_simp, ev_simpAnd] at hg
    subst hg
    simp [AO]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [ev_simp, ev_simpOr] at hg
    subst hg
    simp [AO]

theorem passAO (m : Nat) (gs : List Gate) (acc : List (Bool ⊕ Nat) × List Gate)
    (hg : ∀ g ∈ gs, AO g) (ha : ∀ g ∈ acc.2, AO g) :
    ∀ g ∈ (ev_elimPass m gs acc).2, AO g := by
  induction gs generalizing acc with
  | nil => exact ha
  | cons g gs ih =>
    rw [ev_elimPass_cons]
    apply ih _ (fun e h => hg e (List.mem_cons_of_mem _ h))
    intro e he
    rcases List.mem_append.mp he with old|newmem
    · exact ha e old
    · have hop := (hg g (List.mem_cons_self ..)).1
      exact simpAO _ _ _ hop e (by simpa using newmem)

theorem restrictMarked {n m : Nat} {A : Fin (n+1) → Fin m → Bool} (u : Fin (n+1))
    (C : Circuit) (K : Finset (Fin C.gates.length)) (fan : FanInTwo C) (rep : Represents A C)
    (wit : ∃ x : List Bool, x.length = n+1+m ∧ x.getD u.val false = false ∧ C.eval x = false)
    (marks : ∀ j ∈ K, readsWire (C.gates.get j) u.val ∨
      ∃ i : Fin C.gates.length, i<j ∧ readsWire (C.gates.get i) u.val ∧
        ((C.gates.get i).op=.and ∨ (C.gates.get i).op=.not) ∧
        readsWire (C.gates.get j) (n+1+m+i.val)) :
    ∃ D : Circuit, D.size + K.card ≤ C.size ∧
      Represents (fun a c => A (u.succAbove a) c) D ∧ FanInTwo D ∧
      (Monotone2 C → Monotone2 D) ∧ ReadsBack (n+m) D ∧
      (∀ g∈D.gates,RedG g) ∧ (D.output<n+m+D.gates.length ∨ D.gates=[]) := by
  let N := n+1+m
  let M := n+m
  let a0 : List (Bool ⊕ Nat) × List Gate := (initR N u.val, [])
  let acc := ev_elimPass M C.gates a0
  let status (j i : Nat) := (st M C.gates a0 j).1.getD i (Sum.inl false)
  let test (j : Fin C.gates.length) := ev_simp (C.gates.get j).op (M+(st M C.gates a0 j.val).2.length)
    ((C.gates.get j).inputs.map (status j.val))
  have hu := u.isLt
  have len (j : Nat) (hj : j ≤ C.gates.length) : (st M C.gates a0 j).1.length = N+j := by
    rw [st_len1 _ _ _ _ hj]
    exact congrArg (fun a => a+j) (initR_len N u.val)
  have zero (j : Nat) (hj : j ≤ C.gates.length) : status j u.val = Sum.inl false := by
    dsimp only [status]
    rw [st_stable _ _ _ 0 j _ (by omega) hj (by rw [len 0 (by omega)]; dsimp [N];omega)]
    change (initR N u.val).getD u.val (Sum.inl false)=Sum.inl false
    rw [initR_getD _ _ _ (by dsimp [N];omega),if_neg (by omega),if_pos rfl]
  have ok (j : Fin C.gates.length) : ev_OkGate (C.gates.get j) := fan _ (List.get_mem ..)
  have sc (j : Fin C.gates.length) (hj : j∈K) : (test j).1=none := by
    rcases marks j hj with rd|⟨i,ij,ri,op,rj⟩
    · exact folded _ (ok j) _ _ _ rd false (zero j.val (Nat.le_of_lt j.isLt))
    · obtain ⟨b,hb⟩ := directConst _ (ok i) (M+(st M C.gates a0 i.val).2.length) _ (status i.val)
        ri op (zero i.val (Nat.le_of_lt i.isLt))
      change test i = (none,Sum.inl b) at hb
      have early : status (i.val+1) (N+i.val) = Sum.inl b := by
        dsimp only [status]
        rw [st_succ _ _ _ _ i.isLt]
        simp only [ev_elimStep]
        rw [ev_getD_snoc_eq _ _ _ _ (by rw [len _ (Nat.le_of_lt i.isLt)])]
        exact congrArg Prod.snd hb
      have late : status j.val (N+i.val) = Sum.inl b := by
        dsimp only [status]
        rw [st_stable _ _ _ (i.val+1) j.val _ (show i.val+1 ≤ j.val from ij) (Nat.le_of_lt j.isLt)
          (by rw [len _ i.isLt];omega)]
        exact early
      exact folded _ (ok j) _ _ _ rj b late
  have bound : acc.2.length+K.card ≤ C.size := by
    change (ev_elimPass M C.gates a0).2.length+K.card ≤ C.gates.length
    simpa only [show a0.2.length=0 from rfl,Nat.zero_add] using markedCount M C.gates a0 K sc
  have truth (a : Fin n) (c : Fin m) :
      ev_statVal (W acc.2 (oneEach a c)) (acc.1.getD C.output (Sum.inl false))=A (u.succAbove a) c := by
    have h := ev_Inv_pass M _ C.gates _ a0 fan (inv_init n m u a c)
    exact (h.2.2 C.output).2.trans (rep _ _)
  cases h : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    obtain ⟨x,hx,hz,hf⟩ := wit
    have ar : M+1=N := by dsimp [M,N];omega
    obtain ⟨y,hy⟩ := witnessInit M u.val (by dsimp [M];omega) x (by rw [ar];exact hx) hz
    rw [ar] at hy
    have inv := ev_Inv_pass M y C.gates x a0 fan hy
    have fx := (inv.2.2 C.output).2
    change ev_statVal _ (acc.1.getD C.output (Sum.inl false))=C.eval x at fx
    rw [h,hf] at fx
    change b = false at fx
    subst b
    let D : Circuit := ⟨[],M⟩
    refine ⟨D,?_,?_,?_,?_,?_,?_,Or.inr rfl⟩
    · change 0+K.card ≤ C.size
      omega
    · intro a c
      have e := truth a c
      rw [h] at e
      change false = A (u.succAbove a) c at e
      change (oneEach a c).getD M false = _
      rw [List.getD_eq_default _ _ (by rw [oe_len])]
      exact e
    · intro g hg
      cases hg
    · intro hm g hg
      cases hg
    · intro j hj
      exact False.elim (Nat.not_lt_zero _ hj)
    · intro g hg
      cases hg
  | inr out =>
    have hvr := pass_vrb M C.gates fan a0 (by
      intro i
      change ev_statValid (M+0) ((initR N u.val).getD i (Sum.inl false))
      by_cases hi : i<N
      · rw [initR_getD _ _ _ hi]
        split_ifs <;> simp only [ev_statValid] <;> dsimp [M,N] at * <;> omega
      · rw [List.getD_eq_default _ _ (by rw [initR_len];omega)]
        trivial) (RBo_nil M)
    have valid := hvr.1 C.output
    change ev_statValid (M+acc.2.length) (acc.1.getD C.output (Sum.inl false)) at valid
    rw [h] at valid
    refine ⟨⟨acc.2,out⟩,bound,?_,ev_elimPass_ok _ _ _ (by simp [a0]),?_,
      hvr.2,pass_red _ _ _ (by simp [a0]),Or.inl valid⟩
    · intro a c
      have e := truth a c
      rw [h] at e
      exact e
    · intro hm
      exact passAO _ _ _ hm (by simp [a0])

end PEqualNP.Outside.L_lib_376_aux

namespace PEqualNP.Outside.L_lib_376_aux.Clean376

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.CircuitMoves
  PEqualNP.HeptadCover

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepW x := rfl

lemma foldl_stepW_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepW]; omega

lemma foldl_stepW_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepW_len, List.length_ofFn]

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt; exact List.getD_eq_getElem C.gates _ hj

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma wireVal_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) (x : Fin n → Bool) :
    wireVal n C w x = x ⟨w, hw⟩ := by
  unfold wireVal
  rw [wires_eq_foldl, foldl_stepW_getD_lt _ _ _ (by simp; exact hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma wireVal_ge {n : ℕ} (C : Circuit) (w : ℕ) (hw : n + C.gates.length ≤ w) (x : Fin n → Bool) :
    wireVal n C w x = false := by
  unfold wireVal
  exact getD_ge_len _ _ (by rw [wires_len]; exact hw)

lemma wireVal_gate {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool) :
    wireVal n C (n + j) x = (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i => if i < n + j then wireVal n C i x else false) := by
  unfold wireVal
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    rw [gateAt_eq hj]
    exact (List.take_append_drop j C.gates).symm.trans (by
      congr 1; exact (List.cons_getElem_drop_succ (h := hj)).symm)
  set pre := (C.gates.take j).foldl stepW (List.ofFn x)
  have hpre_len : pre.length = n + j := by
    rw [foldl_stepW_len, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have heq : C.wires (List.ofFn x) = (C.gates.drop (j + 1)).foldl stepW (stepW pre (gateAt C j)) := by
    rw [wires_eq_foldl]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hpre_get : ∀ i < n + j, (C.wires (List.ofFn x)).getD i false = pre.getD i false := by
    intro i hi
    rw [heq, foldl_stepW_getD_lt _ _ _ (by simp [stepW, hpre_len]; omega)]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left (show i < pre.length by omega)]
  have hnj : (C.wires (List.ofFn x)).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => pre.getD i false) := by
    rw [heq, foldl_stepW_getD_lt _ _ _ (by simp [stepW, hpre_len])]
    simp [stepW, List.getD_eq_getElem?_getD, hpre_len]
  rw [hnj]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < n + j
  · simp only [hi, ↓reduceIte]; exact (hpre_get i hi).symm
  · simp only [hi, ↓reduceIte]; exact getD_ge_len pre i (by omega)

lemma wireVal_gate_rb {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j : ℕ} (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    wireVal n C (n + j) x = (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i => wireVal n C i x) := by
  rw [wireVal_gate C j hj x]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp [hRB j hj i hi]

lemma eraseGate_len (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates.length = C.gates.length - 1 := by
  unfold eraseGate
  simp only [hm, ↓reduceIte, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

lemma eraseGate_gateAt_lt (n : ℕ) (C : Circuit) (m p j : ℕ) (hm : m < C.gates.length) (hj : j < m) :
    gateAt (eraseGate n C m p) j = gateAt C j := by
  unfold gateAt eraseGate
  simp only [hm, ↓reduceIte, List.getD_eq_getElem?_getD]
  have htl : j < (C.gates.take m).length := by simp; omega
  rw [List.getElem?_append_left htl, List.getElem?_take_of_lt hj]

lemma eraseGate_gateAt_ge (n : ℕ) (C : Circuit) (m p j : ℕ) (hm : m < C.gates.length)
    (hj1 : m ≤ j) (hj2 : j + 1 < C.gates.length) :
    gateAt (eraseGate n C m p) j =
      ⟨(gateAt C (j + 1)).op, (gateAt C (j + 1)).inputs.map (eraseRedirect n m p)⟩ := by
  unfold gateAt eraseGate
  simp only [hm, ↓reduceIte, List.getD_eq_getElem?_getD]
  have htl : (C.gates.take m).length = m := by simp; omega
  rw [List.getElem?_append_right (by omega), htl, List.getElem?_map, List.getElem?_drop]
  have heq : m + 1 + (j - m) = j + 1 := by omega
  rw [heq, List.getElem?_eq_getElem hj2]
  simp

lemma eraseGate_monotone2 {n : ℕ} {C : Circuit} (hM : Monotone2 C) {m p : ℕ}
    (hm : m < C.gates.length) : Monotone2 (eraseGate n C m p) := by
  have hlen := eraseGate_len n C m p hm
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
  rw [← gateAt_eq hj]
  by_cases hjm : j < m
  · rw [eraseGate_gateAt_lt n C m p j hm hjm]
    exact hM _ (gateAt_mem (by omega))
  · rw [eraseGate_gateAt_ge n C m p j hm (by omega) (by omega)]
    have hm1 := hM _ (gateAt_mem (show j + 1 < C.gates.length by omega))
    exact ⟨hm1.1, by simp [hm1.2]⟩

lemma eraseGate_readsBack {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {m p : ℕ}
    (hm : m < C.gates.length) (hp : p < n + m) : ReadsBack n (eraseGate n C m p) := by
  have hlen := eraseGate_len n C m p hm
  intro j hj i hi
  by_cases hjm : j < m
  · rw [eraseGate_gateAt_lt n C m p j hm hjm] at hi
    exact hRB j (by omega) i hi
  · rw [eraseGate_gateAt_ge n C m p j hm (by omega) (by omega)] at hi
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hi
    have hult := hRB (j + 1) (by omega) u hu
    unfold eraseRedirect
    split_ifs <;> omega

lemma eraseGate_wireVal_eq {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {m p : ℕ}
    (hm : m < C.gates.length) (hp : p < n + m) (x : Fin n → Bool)
    (heq_mp : wireVal n C (n + m) x = wireVal n C p x) :
    ∀ w < n + C.gates.length,
      wireVal n (eraseGate n C m p) (eraseRedirect n m p w) x = wireVal n C w x := by
  have hRB' := eraseGate_readsBack hRB hm hp
  have hlen := eraseGate_len n C m p hm
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · have hred : eraseRedirect n m p w = w := by unfold eraseRedirect; split_ifs <;> omega
      rw [hred, wireVal_input _ w hwn, wireVal_input _ w hwn]
    · set j := w - n
      have hwj : w = n + j := by omega
      have hj : j < C.gates.length := by omega
      by_cases hjm : j < m
      · have hred : eraseRedirect n m p w = n + j := by unfold eraseRedirect; split_ifs <;> omega
        rw [hred, hwj]
        have hj' : j < (eraseGate n C m p).gates.length := by omega
        rw [wireVal_gate_rb hRB' hj', wireVal_gate_rb hRB hj, eraseGate_gateAt_lt n C m p j hm hjm]
        congr 1
        apply List.map_congr_left
        intro u hu
        have hult := hRB j hj u hu
        have hured : eraseRedirect n m p u = u := by unfold eraseRedirect; split_ifs <;> omega
        have := ih u (by omega) (by omega)
        rwa [hured] at this
      · by_cases heqm : j = m
        · have hw_eq : w = n + m := by omega
          have hred : eraseRedirect n m p w = p := by unfold eraseRedirect; simp [hw_eq]
          rw [hred, hw_eq, heq_mp]
          have hpred : eraseRedirect n m p p = p := by unfold eraseRedirect; split_ifs <;> omega
          have := ih p (by omega) (by omega)
          rwa [hpred] at this
        · have hgt : m < j := by omega
          have hred : eraseRedirect n m p w = n + (j - 1) := by unfold eraseRedirect; split_ifs <;> omega
          rw [hred, hwj]
          have hj' : j - 1 < (eraseGate n C m p).gates.length := by omega
          rw [wireVal_gate_rb hRB' hj', wireVal_gate_rb hRB hj,
            eraseGate_gateAt_ge n C m p (j - 1) hm (by omega) (by omega)]
          have hj1 : j - 1 + 1 = j := by omega
          rw [hj1]
          simp only [List.map_map]
          congr 1
          apply List.map_congr_left
          intro u hu
          have hult := hRB j hj u hu
          exact ih u (by omega) (by omega)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem getD_snoc (w : List Bool) (x : Bool) (i : ℕ) :
    (w ++ [x]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then x else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2
  · rfl
  · subst h2; simp
  · have : 1 ≤ i - w.length := by omega
    rw [List.getElem?_eq_none (by simpa using this)]; rfl

theorem getD_big (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

theorem fold_stab (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    simp only [step, getD_snoc, if_pos h]

theorem main_fold2 (n m p : ℕ) (B : List Gate)
    (hB : ∀ g ∈ B, n + m ∉ g.inputs) (w w' : List Bool)
    (hl : w.length = w'.length + 1) (hm : n + m ≤ w'.length)
    (hI : ∀ i, i ≠ n + m → w.getD i false = w'.getD (eraseRedirect n m p i) false) :
    ∀ i, i ≠ n + m → (B.foldl step w).getD i false =
      ((B.map (fun g => (⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ : Gate))).foldl step
        w').getD (eraseRedirect n m p i) false := by
  induction B generalizing w w' with
  | nil => simpa using hI
  | cons g B ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hg := hB g (by simp)
    apply ih (fun g' hg' => hB g' (by simp [hg']))
    · simp [step, hl]
    · simp [step]; omega
    · intro i hi
      simp only [step, getD_snoc, List.map_map]
      have hx : g.op.eval (g.inputs.map fun i => w.getD i false) =
          g.op.eval (g.inputs.map ((fun i => w'.getD i false) ∘ eraseRedirect n m p)) := by
        congr 1
        apply List.map_congr_left
        intro a ha
        exact hI a (fun h => hg (h ▸ ha))
      have hIi := hI i hi
      obtain ⟨r, hr⟩ : ∃ r, r = eraseRedirect n m p i := ⟨_, rfl⟩
      rw [← hr] at hIi ⊢
      unfold eraseRedirect at hr
      rw [if_neg hi] at hr
      by_cases h1 : i < w.length
      · have hr1 : r < w'.length := by split_ifs at hr <;> omega
        rw [if_pos h1, if_pos hr1]; exact hIi
      · rw [if_neg h1]
        by_cases h2 : i = w.length
        · have h4 : r = w'.length := by split_ifs at hr <;> omega
          rw [if_pos h2, if_neg (by omega), if_pos h4]
          exact hx
        · have h4 : w'.length < r := by split_ifs at hr <;> omega
          rw [if_neg h2, if_neg (by omega), if_neg (by omega)]

theorem split_fold (C : Circuit) (x : List Bool) (m : ℕ) (hm : m < C.gates.length) :
    C.gates.foldl step x = (C.gates.drop (m + 1)).foldl step
      (step ((C.gates.take m).foldl step x) C.gates[m]) := by
  have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by simp
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]

theorem unread (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (hu : ∀ k, m < k → ∀ hk : k < C.gates.length, n + m ∉ C.gates[k].inputs)
    (x : List Bool) (hx : x.length = n) (i : ℕ) (hi : i ≠ n + m) :
    PEqualNP.LowMerge.wireVal C x i =
      PEqualNP.LowMerge.wireVal (eraseGate n C m p) x (eraseRedirect n m p i) := by
  simp only [PEqualNP.LowMerge.wireVal, wires_eq]
  rw [split_fold C x m hm]
  simp only [eraseGate, if_pos hm]
  rw [List.foldl_append]
  have hWA : (List.foldl step x (List.take m C.gates)).length = n + m := by
    rw [fold_len, hx, List.length_take]; omega
  apply main_fold2 n m p _ _ _ _ _ _ _ i hi
  · intro g hg
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hg
    simp only [List.getElem_drop]
    exact hu _ (by omega) _
  · simp [step]
  · omega
  · intro j hj
    generalize List.foldl step x (List.take m C.gates) = WA at *
    unfold eraseRedirect
    rw [if_neg hj]
    simp only [step, getD_snoc, hWA]
    by_cases h3 : j < n + m
    · rw [if_pos h3, if_neg (by omega)]
    · rw [if_neg h3, if_neg hj, if_pos (by omega), getD_big _ _ (by omega)]

abbrev shape (g : Gate) :=
  ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
  (g.op = .not ∧ g.inputs.length = 1)
abbrev reads (g : Gate) (w : ℕ) :=
  (g.op = .not ∧ g.inputs.head? = some w) ∨ (g.op ≠ .not ∧ w ∈ g.inputs)

private theorem kept {N p j : ℕ} {C : Circuit} (hj : j < C.gates.length)
    (Q : GateOp → ℕ → Prop) (h : ∀ g ∈ C.gates, Q g.op g.inputs.length) :
    ∀ g ∈ (eraseGate N C j p).gates, Q g.op g.inputs.length := by
  intro g hg
  simp only [eraseGate, hj, ↓reduceIte, List.mem_append, List.mem_map] at hg
  rcases hg with ha | ⟨g',hb,rfl⟩
  · exact h g (List.mem_of_mem_take ha)
  · simpa using h g' (List.mem_of_mem_drop hb)

private theorem read_iff_mem {g : Gate} (sh : shape g) (w : ℕ) :
    reads g w ↔ w ∈ g.inputs := by
  by_cases hn : g.op = .not
  · have sz : g.inputs.length = 1 := by
      rcases sh with ⟨h, _⟩ | ⟨_, h⟩
      · rcases h with h|h <;> simp [hn] at h
      · exact h
    cases e : g.inputs with
    | nil => simp [e] at sz
    | cons a tail =>
      cases tail with
      | nil => simp [reads,hn,e,eq_comm]
      | cons b rest => simp [e] at sz
  · simp [reads,hn]

private theorem onList (x : List Bool) {N : ℕ} (hx : x.length = N) :
    ∃ a : Fin N → Bool, List.ofFn a = x := by
  subst N
  exact ⟨x.get,List.ofFn_get x⟩

private theorem min_gates (M : ℕ) (D : Circuit) (f : FanInTwo D)
    (rb : ReadsBack M D) (sh : ∀ g ∈ D.gates, shape g) (valid : D.output<M+D.gates.length) :
    ∃ E : Circuit, E.size ≤ D.size ∧
      (∀ x : List Bool, x.length = M → E.eval x = D.eval x) ∧ FanInTwo E ∧
      (Monotone2 D → Monotone2 E) ∧ ReadsBack M E ∧ (∀ g ∈ E.gates, shape g) ∧
      E.output < M+E.gates.length ∧
      (∀ (F : Circuit), (∀ x : List Bool, x.length=M → F.eval x=E.eval x) →
        FanInTwo F → (Monotone2 E → Monotone2 F) → ReadsBack M F →
        (∀ g ∈ F.gates, shape g) → F.output<M+F.gates.length → E.size≤F.size) := by
  classical
  let P := fun E : Circuit => (∀ x : List Bool, x.length = M → E.eval x = D.eval x) ∧
    FanInTwo E ∧ (Monotone2 D → Monotone2 E) ∧ ReadsBack M E ∧
    (∀ g ∈ E.gates, shape g) ∧ E.output < M+E.gates.length
  let W := fun s : ℕ => ∃ E : Circuit, P E ∧ E.size = s
  have pd : P D := ⟨fun _ _ => rfl,f,id,rb,sh,valid⟩
  have existsSize : ∃ s,W s := ⟨D.size,D,pd,rfl⟩
  obtain ⟨E,pe,se⟩ := Nat.find_spec existsSize
  have minE (F : Circuit) (pf : P F) : E.size ≤ F.size := by
    rw [se]
    exact Nat.find_min' existsSize (show W F.size from ⟨F,pf,rfl⟩)
  obtain ⟨he,hf,hm,hr,hs,hv⟩ := pe
  refine ⟨E,minE D pd,he,hf,hm,hr,hs,hv,?_⟩
  intro F eq fan mon back sha vo
  exact minE F ⟨fun x hx=>(eq x hx).trans (he x hx),fan,mon.comp hm,back,sha,vo⟩

theorem normalize (M : ℕ) (D : Circuit) (fan : FanInTwo D) (rb : ReadsBack M D)
    (sh : ∀ g ∈ D.gates, shape g) (valid : D.output<M+D.gates.length) :
    ∃ E : Circuit, E.size ≤ D.size ∧
      (∀ x : List Bool, x.length = M → E.eval x = D.eval x) ∧
      FanInTwo E ∧ (Monotone2 D → Monotone2 E) ∧ ReadsBack M E ∧
      (∀ g ∈ E.gates, (g.op = .not → g.inputs.length = 1) ∧
        (g.op ≠ .not → g.inputs.length = 2 ∧ g.inputs.Nodup)) ∧
      (∀ i : Fin E.gates.length, M+i.val ≠ E.output →
        ∃ j : Fin E.gates.length, i < j ∧ reads (E.gates.get j) (M+i.val)) := by
  classical
  obtain ⟨E,hs,eq,fe,me,re,se,ve,least⟩ := min_gates M D fan rb sh valid
  have cannot (j p : ℕ) (hj : j < E.gates.length) (hp : p < M+j)
      (keq : ∀ x : List Bool, x.length=M → (eraseGate M E j p).eval x=E.eval x) : False := by
    let F := eraseGate M E j p
    have fanF : FanInTwo F := kept hj (fun op sz => op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp) ∧ sz ≤ 2) fe
    have shaF : ∀ g ∈ F.gates, shape g := kept hj (fun op sz =>
      ((op = .and ∨ op = .or) ∧ sz = 2) ∨ (op = .not ∧ sz = 1)) se
    have len := eraseGate_len M E j p hj
    have vo : F.output < M+F.gates.length := by
      change (eraseGate M E j p).output < M+(eraseGate M E j p).gates.length
      rw [len]
      simp only [eraseGate,hj,↓reduceIte]
      unfold eraseRedirect
      split_ifs <;> omega
    have le := least F keq fanF (fun h => eraseGate_monotone2 h hj) (eraseGate_readsBack re hj hp) shaF vo
    change E.gates.length ≤ (eraseGate M E j p).gates.length at le
    omega
  refine ⟨E,hs,eq,fe,me,re,?_,?_⟩
  · intro g hg
    have gt := se g hg
    constructor
    · intro nt
      rcases gt with ⟨ho,_⟩ | ⟨_,h⟩
      · rcases ho with h|h <;> simp [nt] at h
      · exact h
    · intro nt
      rcases gt with ⟨hop,hlen⟩ | ⟨hnot,_⟩
      · refine ⟨hlen,?_⟩
        obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
        have hg : gateAt E j = E.gates[j] := gateAt_eq hj
        rcases il : E.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨q,qs⟩⟩⟩
        · simp [il] at hlen
        · simp [il] at hlen
        · simp only [List.nodup_cons, List.mem_singleton, List.nodup_nil, List.not_mem_nil,
            not_false_eq_true, and_self, and_true]
          intro ab
          subst b
          have hp : a < M+j := re j hj a (by simp [hg,il])
          apply cannot j a hj hp
          intro x hx
          obtain ⟨z,rfl⟩ := onList x hx
          have hdup : wireVal M E (M+j) z = wireVal M E a z := by
            rw [wireVal_gate_rb re hj,hg,il]
            rcases hop with h|h <;> rw [h] <;> simp [GateOp.eval]
          have hh := eraseGate_wireVal_eq re hj hp z hdup E.output ve
          change wireVal M (eraseGate M E j a) (eraseGate M E j a).output z =
            wireVal M E E.output z
          simpa only [eraseGate,hj,↓reduceIte] using hh
        · simp [il] at hlen
      · exact False.elim (nt hnot)
  · intro i hno
    by_contra hnone
    have hu : ∀ j, i.val < j → ∀ hj : j < E.gates.length, M+i.val ∉ E.gates[j].inputs := by
      intro j ij hj hmem
      have rd := (read_iff_mem (se _ (List.getElem_mem hj)) (M+i.val)).2 hmem
      exact hnone ⟨⟨j,hj⟩, ij, rd⟩
    have shapeI := se _ (List.getElem_mem i.isLt)
    have ne : E.gates[i.val].inputs ≠ [] := by
      intro z
      rcases shapeI with ⟨_,h⟩|⟨_,h⟩ <;> simp [z] at h
    obtain ⟨p, ps, hps⟩ := List.exists_cons_of_ne_nil ne
    have hp : p < M+i.val := re i.val i.isLt p (by simp [gateAt_eq i.isLt,hps])
    apply cannot i.val p i.isLt hp
    intro x hx
    have hh := unread M E i.val p i.isLt hu x hx E.output hno.symm
    change PEqualNP.LowMerge.wireVal (eraseGate M E i.val p) x (eraseGate M E i.val p).output =
      PEqualNP.LowMerge.wireVal E x E.output
    simpa only [eraseGate,i.isLt,↓reduceIte] using hh.symm

end PEqualNP.Outside.L_lib_376_aux.Clean376

open PEqualNP.Outside.L_lib_376_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

theorem PEqualNP.Outside.L_lib_376 :
∀ (n m : ℕ) (A : Fin (n + 1) → Fin m → Bool) (u : Fin (n + 1))
    (C : PEqualNP.CircuitLowerBounds.Circuit) (K : Finset (Fin C.gates.length)),
  let N := n + 1 + m
  let reads := fun (g : PEqualNP.CircuitLowerBounds.Gate) (w : ℕ) =>
    (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some w) ∨
    (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ w ∈ g.inputs)
  PEqualNP.MetaComplexity.FanInTwo C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack N C →
  PEqualNP.Represents.Represents A C →
  (∃ x : List Bool, x.length = N ∧ x.getD u.val false = false ∧ C.eval x = false) →
  (∀ j ∈ K, reads (C.gates.get j) u.val ∨
    ∃ i : Fin C.gates.length, i < j ∧ reads (C.gates.get i) u.val ∧
      ((C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
       (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      reads (C.gates.get j) (N + i.val)) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
    D.size + K.card ≤ C.size ∧
    PEqualNP.Represents.Represents (fun a c => A (u.succAbove a) c) D ∧
    PEqualNP.MetaComplexity.FanInTwo D ∧
    (PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.Monotone2 D) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) D ∧
    (∀ g ∈ D.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 1) ∧
      (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not →
        g.inputs.length = 2 ∧ g.inputs.Nodup)) ∧
    (∀ i : Fin D.gates.length, n + m + i.val ≠ D.output →
      ∃ j : Fin D.gates.length, i < j ∧ reads (D.gates.get j) (n + m + i.val)) := by
  intro n m A u C K N reads fan rb rep wit marks
  obtain ⟨D,sizeD,repD,fanD,monoD,backD,shapeD,valid|empty⟩ :=
    restrictMarked u C K fan rep wit marks
  · obtain ⟨E,le,eq,fanE,monoE,backE,shapeE,liveE⟩ :=
      Clean376.normalize (n+m) D fanD backD shapeD valid
    exact ⟨E,by omega,fun a c => (eq (oneEach a c) (oe_len ..)).trans (repD a c),
      fanE,monoE.comp monoD,backE,shapeE,liveE⟩
  · refine ⟨D,sizeD,repD,fanD,monoD,backD,?_,?_⟩
    · intro g hg
      rw [empty] at hg
      cases hg
    · intro i
      have hi := i.isLt
      have len : D.gates.length = 0 := congrArg List.length empty
      omega
