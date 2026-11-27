import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_25489_aux

namespace Trace87

open PEqualNP.CircuitLowerBounds



def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem stp_len (W : List Bool) (g : Gate) : (stp W g).length = W.length + 1 := by
  simp [stp]

theorem stp_getD (W : List Bool) (g : Gate) (j : ℕ) : (stp W g).getD j false =
    if j < W.length then W.getD j false else if j = W.length then
      g.op.eval (g.inputs.map fun i => W.getD i false) else false := getD_snoc _ _ _

theorem flen : ∀ (gs : List Gate) (W : List Bool), (gs.foldl stp W).length = W.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro W; simp
  | cons g t ih => intro W; rw [List.foldl_cons, ih, stp_len]; simp; omega

theorem pre : ∀ (gs : List Gate) (W : List Bool) (j : ℕ), j < W.length →
    (gs.foldl stp W).getD j false = W.getD j false := by
  intro gs
  induction gs with
  | nil => intro W j _; rfl
  | cons g t ih =>
    intro W j hj
    rw [List.foldl_cons, ih _ _ (by rw [stp_len]; omega), stp_getD, if_pos hj]

theorem vgate : ∀ (gs : List Gate) (W : List Bool) (r : ℕ) (h : r < gs.length),
    (gs.foldl stp W).getD (W.length + r) false = gs[r].op.eval (gs[r].inputs.map fun a =>
      if a < W.length + r then (gs.foldl stp W).getD a false else false) := by
  intro gs
  induction gs with
  | nil => intro W r h; simp at h
  | cons g t ih =>
    intro W r h
    cases r with
    | zero =>
      simp only [List.foldl_cons, List.getElem_cons_zero, Nat.add_zero]
      rw [pre t (stp W g) W.length (by rw [stp_len]; omega), stp_getD, if_neg (lt_irrefl _), if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro a _
      split_ifs with ha
      · rw [pre t _ a (by rw [stp_len]; omega), stp_getD, if_pos ha]
      · exact getD_ge W a (by omega)
    | succ r =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      have := ih (stp W g) r (by simp at h; omega)
      rw [stp_len] at this
      rw [show W.length + (r + 1) = W.length + 1 + r by omega]
      exact this

theorem run (R : ℕ → Bool → Prop) : ∀ (gs : List Gate) (W : List Bool),
    (∀ j < W.length, R j (W.getD j false)) →
    (∀ r (h : r < gs.length) (w : List Bool), w.length = W.length + r →
      (∀ j < W.length + r, R j (w.getD j false)) →
      R (W.length + r) (gs[r].op.eval (gs[r].inputs.map fun a => w.getD a false))) →
    ∀ j < W.length + gs.length, R j ((gs.foldl stp W).getD j false) := by
  intro gs
  induction gs with
  | nil => intro W hW _ j hj; exact hW j (by simpa using hj)
  | cons g t ih =>
    intro W hW H j hj
    rw [List.foldl_cons]
    apply ih (stp W g)
    · intro j' hj'
      rw [stp_len] at hj'
      rw [stp_getD]
      by_cases h1 : j' < W.length
      · rw [if_pos h1]; exact hW j' h1
      · have e : j' = W.length := by omega
        rw [if_neg h1, if_pos e]
        subst e
        have := H 0 (by simp) W (by simp) (by intro j2 hj2; exact hW j2 (by omega))
        simpa using this
    · intro r hr w hw hrel
      rw [stp_len] at hw hrel ⊢
      have := H (r + 1) (by simp; omega) w (by omega) (by intro j2 hj2; exact hrel j2 (by omega))
      rw [show W.length + 1 + r = W.length + (r + 1) by omega]
      simpa using this
    · rw [stp_len]; simp at hj; omega
theorem allP (P : Bool → Bool → Prop) (ht : P true true)
    (hand : ∀ a b c d : Bool, P a b → P c d → P (a && c) (b && d)) :
    ∀ (l : List ℕ) (f1 f2 : ℕ → Bool), (∀ a ∈ l, P (f1 a) (f2 a)) →
      P ((l.map f1).all id) ((l.map f2).all id) := by
  intro l
  induction l with
  | nil => intro f1 f2 _; simpa using ht
  | cons x l ih =>
    intro f1 f2 h
    simp only [List.map_cons, List.all_cons, id]
    exact hand _ _ _ _ (h x (by simp)) (by simpa using ih f1 f2 (fun a ha => h a (by simp [ha])))

theorem anyP (P : Bool → Bool → Prop) (hf : P false false)
    (hor : ∀ a b c d : Bool, P a b → P c d → P (a || c) (b || d)) :
    ∀ (l : List ℕ) (f1 f2 : ℕ → Bool), (∀ a ∈ l, P (f1 a) (f2 a)) →
      P ((l.map f1).any id) ((l.map f2).any id) := by
  intro l
  induction l with
  | nil => intro f1 f2 _; simpa using hf
  | cons x l ih =>
    intro f1 f2 h
    simp only [List.map_cons, List.any_cons, id]
    exact hor _ _ _ _ (h x (by simp)) (by simpa using ih f1 f2 (fun a ha => h a (by simp [ha])))


theorem oe_len {n m : ℕ} (u : Fin n) (v : Fin m) : (PEqualNP.Represents.oneEach u v).length = n + m := by
  simp [PEqualNP.Represents.oneEach]


theorem p1and : ∀ a b c d : Bool, (a = true → b = true) → (c = true → d = true) →
    (a && c) = true → (b && d) = true := by decide

theorem p1or : ∀ a b c d : Bool, (a = true → b = true) → (c = true → d = true) →
    (a || c) = true → (b || d) = true := by decide


theorem all_mem_true (l : List ℕ) (f : ℕ → Bool) (a : ℕ) (ha : a ∈ l)
    (h : GateOp.and.eval (l.map f) = true) : f a = true := by
  have h' : (l.map f).all id = true := h
  rw [List.all_eq_true] at h'
  exact h' (f a) (List.mem_map.2 ⟨a, ha, rfl⟩)

theorem any_mem_true (l : List ℕ) (f : ℕ → Bool) (a : ℕ) (ha : a ∈ l) (h : f a = true) :
    GateOp.or.eval (l.map f) = true := by
  show (l.map f).any id = true
  rw [List.any_eq_true]
  exact ⟨f a, List.mem_map.2 ⟨a, ha, rfl⟩, h⟩


theorem oe_get {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge i n with h | h
  · rw [List.getElem?_append_left (by simp; omega)]
    simp only [List.getElem?_ofFn, h, dite_true, Option.getD_some, Fin.ext_iff]
    apply decide_eq_decide.2
    constructor <;> intro hh <;> omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem?_ofFn]
    by_cases h2 : i - n < m
    · simp only [h2, dite_true, Option.getD_some, Fin.ext_iff]
      apply decide_eq_decide.2
      constructor <;> intro hh <;> omega
    · simp only [h2, dite_false, Option.getD_none]
      symm
      apply decide_eq_false
      omega

theorem col_get {m : ℕ} (v : Fin m) (n i : ℕ) :
    (List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v))).getD i false =
      decide (i = n + v.val) := by
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge i n with h | h
  · rw [List.getElem?_append_left (by simp; omega)]
    simp only [List.getElem?_replicate, h, if_true, Option.getD_some]
    symm
    apply decide_eq_false
    omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_replicate, List.getElem?_ofFn]
    by_cases h2 : i - n < m
    · simp only [h2, dite_true, Option.getD_some, Fin.ext_iff]
      apply decide_eq_decide.2
      constructor <;> intro hh <;> omega
    · simp only [h2, dite_false, Option.getD_none]
      symm
      apply decide_eq_false
      omega


theorem gval (C : Circuit) (N : ℕ) (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack N C)
    (X : List Bool) (hX : X.length = N) (k : ℕ) (hk : k < C.gates.length) :
    (C.wires X).getD (N + k) false =
      (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun a => (C.wires X).getD a false) := by
  have hv := vgate C.gates X k hk
  rw [hX] at hv
  show (C.gates.foldl stp X).getD (N + k) false = _
  rw [hv]
  congr 1
  apply List.map_congr_left
  intro a ha
  have : a < N + k := by
    apply hrb k hk a
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ hk]
    exact ha
  rw [if_pos this]
  rfl

theorem dom (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (X Y : List Bool)
    (hl : X.length = Y.length) (T : ℕ → Prop) (O : ℕ)
    (hin : ∀ i < X.length, ¬ T i → X.getD i false = true → Y.getD i false = true)
    (hcl : ∀ r (hr : r < C.gates.length), X.length + r ≠ O → ¬ T (X.length + r) →
      ∀ a ∈ (C.gates[r]).inputs, ¬ T a)
    (hO : (C.wires X).getD O false = true → (C.wires Y).getD O false = true) (t : ℕ) (ht : ¬ T t) :
    (C.wires X).getD t false = true → (C.wires Y).getD t false = true := by
  show (C.gates.foldl stp X).getD t false = true → (C.gates.foldl stp Y).getD t false = true
  have hO' : (C.gates.foldl stp X).getD O false = true →
      (C.gates.foldl stp Y).getD O false = true := hO
  have hrun := run (fun j bb => bb = (C.gates.foldl stp X).getD j false ∧
      (¬ T j → bb = true → (C.gates.foldl stp Y).getD j false = true)) C.gates X
    (by
      intro j hj
      refine ⟨(pre _ _ _ hj).symm, fun hT h => ?_⟩
      rw [pre _ _ _ (by omega)]
      exact hin j hj hT h)
    (by
      intro r hr w hw hrel
      have hvX := vgate C.gates X r hr
      have hvY := vgate C.gates Y r hr
      rw [← hl] at hvY
      have heq : (C.gates[r]).op.eval ((C.gates[r]).inputs.map fun a => w.getD a false) =
          (C.gates.foldl stp X).getD (X.length + r) false := by
        rw [hvX]
        congr 1
        apply List.map_congr_left
        intro a _
        by_cases hlt : a < X.length + r
        · rw [if_pos hlt]; exact (hrel a hlt).1
        · rw [if_neg hlt]; exact getD_ge w a (by omega)
      refine ⟨heq, fun hT h => ?_⟩
      by_cases hrO : X.length + r = O
      · rw [heq] at h
        rw [hrO] at h ⊢
        exact hO' h
      rw [hvY]
      have hna := hcl r hr hrO hT
      have key : ∀ a ∈ (C.gates[r]).inputs, (fun p q : Bool => p = true → q = true) (w.getD a false)
          (if a < X.length + r then (C.gates.foldl stp Y).getD a false else false) := by
        intro a ha
        by_cases hlt : a < X.length + r
        · rw [if_pos hlt]; exact (hrel a hlt).2 (hna a ha)
        · rw [getD_ge w a (by omega)]; intro h; exact absurd h (by simp)
      have hop := (hC _ (List.getElem_mem hr)).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with e | e
      · rw [e] at h ⊢
        simp only [GateOp.eval] at h ⊢
        exact allP (fun p q : Bool => p = true → q = true) (fun h => h) p1and _ _ _ key h
      · rw [e] at h ⊢
        simp only [GateOp.eval] at h ⊢
        exact anyP (fun p q : Bool => p = true → q = true) (fun h => h) p1or _ _ _ key h)
  intro h
  by_cases hj : t < X.length + C.gates.length
  · exact (hrun t hj).2 ht h
  · rw [getD_ge _ _ (by rw [flen]; omega)] at h
    exact absurd h (by simp)

theorem hga (C : Circuit) (r : ℕ) (hr : r < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C r = C.gates[r] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hr]

theorem avoid_ne (C : Circuit) (n m z s a : ℕ) (hs : s ≠ z)
    (h : Relation.ReflTransGen (fun prev next : ℕ => prev ≠ z ∧ next ≠ z ∧
      ∃ idx : Fin C.gates.length, next = n + m + idx.val ∧
        prev ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C idx.val).inputs) s a) : a ≠ z := by
  induction h with
  | refl => exact hs
  | tail _ hb _ => exact hb.2.1

theorem mono2 (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (X Y : List Bool)
    (hl : X.length = Y.length) (hXY : ∀ i < X.length, X.getD i false = true → Y.getD i false = true)
    (t : ℕ) : (C.wires X).getD t false = true → (C.wires Y).getD t false = true := by
  apply dom C hC X Y hl (fun _ => False) (X.length + C.gates.length)
    (fun i hi _ h => hXY i hi h) (fun _ _ _ _ _ _ h => h) ?_ t (fun h => h)
  intro h
  have e : (C.wires X).getD (X.length + C.gates.length) false = false := by
    show (C.gates.foldl stp X).getD _ false = false
    exact getD_ge _ _ (by rw [flen])
  rw [e] at h
  exact absurd h (by simp)

end Trace87

open Trace87 PEqualNP.CircuitLowerBounds in
theorem cut87 : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : Fin n)
    (j : Fin C.gates.length) (q : ℕ),
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let g := n + m + j.val
  let edge := fun source target : ℕ => ∃ idx : Fin C.gates.length,
    target = n + m + idx.val ∧ source ∈ (gate idx.val).inputs
  let cuts := fun (z start : ℕ) =>
    ¬ (start ≠ z ∧ C.output ≠ z ∧ Relation.ReflTransGen
      (fun prev next : ℕ => prev ≠ z ∧ next ≠ z ∧ edge prev next) start C.output)
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents G C → u ≠ v →
  (gate j.val).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  q ∈ (gate j.val).inputs →
  cuts g u.val → cuts q v.val → ¬ Relation.ReflTransGen edge u.val q →
  ∀ c : Fin m, (∃ w : Fin n, G w c = false) →
    let col := List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c))
    let value := (C.wires col).getD q false
    (G u c = true → value = true) ∧ (G v c = true → value = false) := by
  intro n m G C u v j q gate g edge cuts hC hrb hrep huv hop hq hcu hcv hnr c hw col value
  obtain ⟨w0, hw0⟩ := hw
  have hu1 := u.2
  have hv1 := v.2
  have hc1 := c.2
  have hj1 := j.2
  have hvu : u.val ≠ v.val := fun e => huv (Fin.ext e)
  have hcolg : ∀ i, col.getD i false = decide (i = n + c.val) := fun i => col_get c n i
  have hcoll : col.length = n + m := by simp [col]
  have hgj : PEqualNP.MetaComplexity.NestedCover.gateAt C j.val = C.gates[j.val] := hga C j.val j.2
  have hop' : (C.gates[j.val]).op = GateOp.and := by rw [← hgj]; exact hop
  have hq' : q ∈ (C.gates[j.val]).inputs := by rw [← hgj]; exact hq
  have hqlt : q < n + m + j.val := by
    apply hrb j.val j.2 q
    exact hq
  have hcolW : ∀ t, (C.wires col).getD t false = true →
      (C.wires (PEqualNP.Represents.oneEach w0 c)).getD t false = true := by
    intro t
    apply mono2 C hC col _ (by rw [hcoll, oe_len])
    intro i _ h
    rw [hcolg] at h
    rw [oe_get]
    simp only [decide_eq_true_eq] at h ⊢
    omega
  have hWo : (C.wires (PEqualNP.Represents.oneEach w0 c)).getD C.output false = true → False := by
    intro h
    have e : C.eval (PEqualNP.Represents.oneEach w0 c) = true := h
    rw [hrep, hw0] at e
    exact absurd e (by simp)
  refine ⟨fun hu => ?_, fun hv => ?_⟩
  · have hXl : (PEqualNP.Represents.oneEach u c).length = n + m := oe_len u c
    have hXc : (PEqualNP.Represents.oneEach u c).length = col.length := by rw [hXl, hcoll]
    have hinX : ∀ T : ℕ → Prop, T u.val → ∀ i' < (PEqualNP.Represents.oneEach u c).length, ¬ T i' →
        (PEqualNP.Represents.oneEach u c).getD i' false = true → col.getD i' false = true := by
      intro T hTu i' _ hT h
      have : i' ≠ u.val := fun e => hT (e ▸ hTu)
      rw [oe_get] at h
      rw [hcolg]
      simp only [decide_eq_true_eq] at h ⊢
      omega
    have hXo : (C.wires (PEqualNP.Represents.oneEach u c)).getD C.output false = true := by
      show C.eval _ = true
      rw [hrep]; exact hu
    have hXg : (C.wires (PEqualNP.Represents.oneEach u c)).getD (n + m + j.val) false = true := by
      by_contra hne
      rw [Bool.not_eq_true] at hne
      by_cases hog : C.output = n + m + j.val
      · rw [hog, hne] at hXo
        exact absurd hXo (by simp)
      apply hWo
      apply hcolW
      refine dom C hC _ _ hXc (fun t => Relation.ReflTransGen
          (fun prev next : ℕ => prev ≠ n + m + j.val ∧ next ≠ n + m + j.val ∧ edge prev next)
          u.val t) (n + m + j.val) (hinX _ Relation.ReflTransGen.refl) ?_
        (fun h => by rw [hne] at h; exact absurd h (by simp)) C.output
        (fun h => hcu ⟨by show u.val ≠ n + m + j.val; omega, hog, h⟩) hXo
      intro r hr hrO hnT a ha hTa
      rw [hXl] at hrO hnT
      apply hnT
      exact Relation.ReflTransGen.tail hTa
        ⟨avoid_ne C n m _ u.val a (by omega) hTa, hrO, ⟨r, hr⟩, rfl,
          by show a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs; rw [hga C r hr]; exact ha⟩
    have hXq : (C.wires (PEqualNP.Represents.oneEach u c)).getD q false = true := by
      rw [gval C (n + m) hrb _ hXl j.val j.2, hop'] at hXg
      exact all_mem_true _ _ q hq' hXg
    show (C.wires col).getD q false = true
    refine dom C hC _ _ hXc (fun t => Relation.ReflTransGen edge u.val t)
      (n + m + C.gates.length) (hinX _ Relation.ReflTransGen.refl) ?_ ?_ q hnr hXq
    · intro r hr _ hnT a ha hTa
      rw [hXl] at hnT
      apply hnT
      exact Relation.ReflTransGen.tail hTa
        ⟨⟨r, hr⟩, rfl, by show a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs; rw [hga C r hr]; exact ha⟩
    · intro h
      have e : (C.wires (PEqualNP.Represents.oneEach u c)).getD (n + m + C.gates.length) false = false := by
        show (C.gates.foldl stp _).getD _ false = false
        exact getD_ge _ _ (by rw [flen, hXl])
      rw [e] at h
      exact absurd h (by simp)
  · show (C.wires col).getD q false = false
    by_contra hne
    rw [Bool.not_eq_false] at hne
    by_cases hqv : q = v.val
    · have e : (C.wires col).getD q false = col.getD q false := pre _ _ _ (by rw [hcoll]; omega)
      rw [e, hcolg] at hne
      simp only [decide_eq_true_eq] at hne
      omega
    by_cases hoq : C.output = q
    · apply hWo
      rw [hoq]
      exact hcolW q hne
    have hYl : (PEqualNP.Represents.oneEach v c).length = n + m := oe_len v c
    have hYW : (PEqualNP.Represents.oneEach v c).length =
        (PEqualNP.Represents.oneEach w0 c).length := by rw [hYl, oe_len]
    have hYo : (C.wires (PEqualNP.Represents.oneEach v c)).getD C.output false = true := by
      show C.eval _ = true
      rw [hrep]; exact hv
    apply hWo
    refine dom C hC _ _ hYW (fun t => Relation.ReflTransGen
        (fun prev next : ℕ => prev ≠ q ∧ next ≠ q ∧ edge prev next) v.val t) q ?_ ?_
      (fun _ => hcolW q hne) C.output (fun h => hcv ⟨fun e => hqv e.symm, hoq, h⟩) hYo
    · intro i' _ hT h
      have : i' ≠ v.val := fun e => hT (by subst e; exact Relation.ReflTransGen.refl)
      rw [oe_get] at h ⊢
      simp only [decide_eq_true_eq] at h ⊢
      omega
    · intro r hr hrO hnT a ha hTa
      rw [hYl] at hrO hnT
      apply hnT
      exact Relation.ReflTransGen.tail hTa
        ⟨avoid_ne C n m _ v.val a (fun e => hqv e.symm) hTa, hrO, ⟨r, hr⟩, rfl,
          by show a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs; rw [hga C r hr]; exact ha⟩

end PEqualNP.Outside.L_meta_25489_aux

namespace PEqualNP.Outside.L_meta_25489_aux

open PEqualNP.CircuitLowerBounds



def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem stp_len (W : List Bool) (g : Gate) : (stp W g).length = W.length + 1 := by
  simp [stp]

theorem stp_getD (W : List Bool) (g : Gate) (j : ℕ) : (stp W g).getD j false =
    if j < W.length then W.getD j false else if j = W.length then
      g.op.eval (g.inputs.map fun i => W.getD i false) else false := getD_snoc _ _ _

theorem flen : ∀ (gs : List Gate) (W : List Bool), (gs.foldl stp W).length = W.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro W; simp
  | cons g t ih => intro W; rw [List.foldl_cons, ih, stp_len]; simp; omega

theorem pre : ∀ (gs : List Gate) (W : List Bool) (j : ℕ), j < W.length →
    (gs.foldl stp W).getD j false = W.getD j false := by
  intro gs
  induction gs with
  | nil => intro W j _; rfl
  | cons g t ih =>
    intro W j hj
    rw [List.foldl_cons, ih _ _ (by rw [stp_len]; omega), stp_getD, if_pos hj]

theorem vgate : ∀ (gs : List Gate) (W : List Bool) (r : ℕ) (h : r < gs.length),
    (gs.foldl stp W).getD (W.length + r) false = gs[r].op.eval (gs[r].inputs.map fun a =>
      if a < W.length + r then (gs.foldl stp W).getD a false else false) := by
  intro gs
  induction gs with
  | nil => intro W r h; simp at h
  | cons g t ih =>
    intro W r h
    cases r with
    | zero =>
      simp only [List.foldl_cons, List.getElem_cons_zero, Nat.add_zero]
      rw [pre t (stp W g) W.length (by rw [stp_len]; omega), stp_getD, if_neg (lt_irrefl _), if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro a _
      split_ifs with ha
      · rw [pre t _ a (by rw [stp_len]; omega), stp_getD, if_pos ha]
      · exact getD_ge W a (by omega)
    | succ r =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      have := ih (stp W g) r (by simp at h; omega)
      rw [stp_len] at this
      rw [show W.length + (r + 1) = W.length + 1 + r by omega]
      exact this

theorem run (R : ℕ → Bool → Prop) : ∀ (gs : List Gate) (W : List Bool),
    (∀ j < W.length, R j (W.getD j false)) →
    (∀ r (h : r < gs.length) (w : List Bool), w.length = W.length + r →
      (∀ j < W.length + r, R j (w.getD j false)) →
      R (W.length + r) (gs[r].op.eval (gs[r].inputs.map fun a => w.getD a false))) →
    ∀ j < W.length + gs.length, R j ((gs.foldl stp W).getD j false) := by
  intro gs
  induction gs with
  | nil => intro W hW _ j hj; exact hW j (by simpa using hj)
  | cons g t ih =>
    intro W hW H j hj
    rw [List.foldl_cons]
    apply ih (stp W g)
    · intro j' hj'
      rw [stp_len] at hj'
      rw [stp_getD]
      by_cases h1 : j' < W.length
      · rw [if_pos h1]; exact hW j' h1
      · have e : j' = W.length := by omega
        rw [if_neg h1, if_pos e]
        subst e
        have := H 0 (by simp) W (by simp) (by intro j2 hj2; exact hW j2 (by omega))
        simpa using this
    · intro r hr w hw hrel
      rw [stp_len] at hw hrel ⊢
      have := H (r + 1) (by simp; omega) w (by omega) (by intro j2 hj2; exact hrel j2 (by omega))
      rw [show W.length + 1 + r = W.length + (r + 1) by omega]
      simpa using this
    · rw [stp_len]; simp at hj; omega
theorem allP (P : Bool → Bool → Prop) (ht : P true true)
    (hand : ∀ a b c d : Bool, P a b → P c d → P (a && c) (b && d)) :
    ∀ (l : List ℕ) (f1 f2 : ℕ → Bool), (∀ a ∈ l, P (f1 a) (f2 a)) →
      P ((l.map f1).all id) ((l.map f2).all id) := by
  intro l
  induction l with
  | nil => intro f1 f2 _; simpa using ht
  | cons x l ih =>
    intro f1 f2 h
    simp only [List.map_cons, List.all_cons, id]
    exact hand _ _ _ _ (h x (by simp)) (by simpa using ih f1 f2 (fun a ha => h a (by simp [ha])))

theorem anyP (P : Bool → Bool → Prop) (hf : P false false)
    (hor : ∀ a b c d : Bool, P a b → P c d → P (a || c) (b || d)) :
    ∀ (l : List ℕ) (f1 f2 : ℕ → Bool), (∀ a ∈ l, P (f1 a) (f2 a)) →
      P ((l.map f1).any id) ((l.map f2).any id) := by
  intro l
  induction l with
  | nil => intro f1 f2 _; simpa using hf
  | cons x l ih =>
    intro f1 f2 h
    simp only [List.map_cons, List.any_cons, id]
    exact hor _ _ _ _ (h x (by simp)) (by simpa using ih f1 f2 (fun a ha => h a (by simp [ha])))


theorem oe_len {n m : ℕ} (u : Fin n) (v : Fin m) : (PEqualNP.Represents.oneEach u v).length = n + m := by
  simp [PEqualNP.Represents.oneEach]


theorem p1and : ∀ a b c d : Bool, (a = true → b = true) → (c = true → d = true) →
    (a && c) = true → (b && d) = true := by decide

theorem p1or : ∀ a b c d : Bool, (a = true → b = true) → (c = true → d = true) →
    (a || c) = true → (b || d) = true := by decide


theorem oe_get {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge i n with h | h
  · rw [List.getElem?_append_left (by simp; omega)]
    simp only [List.getElem?_ofFn, h, dite_true, Option.getD_some, Fin.ext_iff]
    apply decide_eq_decide.2
    constructor <;> intro hh <;> omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem?_ofFn]
    by_cases h2 : i - n < m
    · simp only [h2, dite_true, Option.getD_some, Fin.ext_iff]
      apply decide_eq_decide.2
      constructor <;> intro hh <;> omega
    · simp only [h2, dite_false, Option.getD_none]
      symm
      apply decide_eq_false
      omega

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
abbrev signal {n m : Nat} (C : Circuit) (v : Fin n) (c : Fin m) (i : Nat) :=
  (C.wires (oneEach v c)).getD i false
lemma uniqueReader {C : Circuit} {u : Nat} {i j : Fin C.gates.length}
    (hr : readsIn C (Finset.range C.gates.length) u = 1)
    (hi : u ∈ (gateAt C i.val).inputs) (hj : u ∈ (gateAt C j.val).inputs) : j=i := by
  by_contra hn
  have ne : j.val ≠ i.val := fun h => hn (Fin.ext h)
  have sub : ({i.val,j.val} : Finset Nat) ⊆ Finset.range C.gates.length := by
    intro z hz; simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl <;> simp
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f:=fun k => (gateAt C k).inputs.count u) sub (by intros;omega)
  simp only [Finset.sum_insert (by simpa using ne.symm : i.val ∉ ({j.val} : Finset Nat)),Finset.sum_singleton] at h
  change (∑ a ∈ Finset.range C.gates.length, (gateAt C a).inputs.count u) = 1 at hr
  have ha := List.count_pos_iff.mpr hi
  have hb := List.count_pos_iff.mpr hj
  omega
lemma saturated {n m : Nat} {G : Fin n → Fin m → Bool} {C : Circuit} {u v : Fin n} {c : Fin m}
    (hC : Monotone2 C) (rb : ReadsBack (n+m) C) (rep : Represents G C)
    (gu : G u c = true) (gv : G v c = false)
    (S : Nat → Prop) (su : S u.val) (out : ¬ S C.output)
    (cut : ∀ z : Fin C.gates.length, ¬ S (n+m+z.val) → ∀ a ∈ (gateAt C z.val).inputs,
      S a → signal C v c (n+m+z.val) = true) : False := by
  have hXl := oe_len u c
  have hYl := oe_len v c
  have hrun := run (fun t b => ¬ S t → b=true → signal C v c t=true) C.gates (oneEach u c)
    (by
      intro t ht hns hu
      change (C.gates.foldl stp (oneEach v c)).getD t false = true
      rw [pre _ _ _ (by rw [hYl]; rwa [hXl] at ht),oe_get]; rw [oe_get] at hu
      simp only [decide_eq_true_eq] at hu ⊢
      have ne : t ≠ u.val := fun e => hns (e.symm ▸ su)
      omega)
    (by
      intro j hj w hw rel
      rw [hXl] at hw rel ⊢
      intro ns h
      have ga : gateAt C j = C.gates[j] := by unfold gateAt;rw [List.getD_eq_getElem _ _ hj]
      by_cases crossed : ∃ a ∈ (gateAt C j).inputs, S a
      · obtain ⟨a,ha,sa⟩ := crossed;exact cut ⟨j,hj⟩ ns a ha sa
      have eqv := vgate C.gates (oneEach v c) j hj
      rw [hYl] at eqv
      change (C.gates.foldl stp (oneEach v c)).getD (n+m+j) false = true
      rw [eqv]
      have key : ∀ a ∈ (C.gates[j]).inputs, (fun p q : Bool => p = true → q = true) (w.getD a false)
          (if a < n+m+j then (C.gates.foldl stp (oneEach v c)).getD a false else false) := by
        intro a ha
        have ha' := ga.symm ▸ ha
        have lt := rb j hj a ha'
        rw [if_pos lt]
        exact rel a lt (fun hs => crossed ⟨a,ha',hs⟩)
      have op := (hC _ (List.getElem_mem hj)).1
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
      rcases op with e|e
      · rw [e] at h ⊢;simp only [GateOp.eval] at h ⊢
        exact allP (fun p q : Bool => p=true → q=true) (fun h=>h) p1and _ _ _ key h
      · rw [e] at h ⊢;simp only [GateOp.eval] at h ⊢
        exact anyP (fun p q : Bool => p=true → q=true) (fun h=>h) p1or _ _ _ key h)
  have pos : (C.gates.foldl stp (oneEach u c)).getD C.output false = true := (rep u c).trans gu
  have neg : signal C v c C.output = false := (rep v c).trans gv
  by_cases lt : C.output < n+m+C.gates.length
  · have bad := hrun C.output (by rwa [hXl]) out pos; rw [neg] at bad; contradiction
  · rw [getD_ge _ _ (by rw [flen,hXl];omega)] at pos; contradiction
abbrev orForm (C : Circuit) (j : Fin C.gates.length) (a b : Nat) :=
  (gateAt C j.val).op=.or ∧ ((gateAt C j.val).inputs=[a,b] ∨ (gateAt C j.val).inputs=[b,a])
lemma orMem {C : Circuit} {j : Fin C.gates.length} {a b} (h : orForm C j a b) :
    a ∈ (gateAt C j.val).inputs := by rcases h.2 with q|q <;> simp [q]
lemma orHigh {n m : Nat} (C : Circuit) (v : Fin n) (c : Fin m) (j : Fin C.gates.length) (a b : Nat)
    (h : orForm C j a b) (rb : ReadsBack (n+m) C) (ha : signal C v c a = true) : signal C v c (n+m+j.val) = true := by
  have eqv := vgate C.gates (oneEach v c) j.val j.isLt
  rw [oe_len] at eqv
  have hg : C.gates[j.val] = gateAt C j.val := by unfold gateAt;rw [List.getD_eq_getElem _ _ j.isLt]
  rw [hg,h.1] at eqv
  have lt := rb j.val j.isLt a (orMem h)
  change (C.gates.foldl stp (oneEach v c)).getD _ false = true at ha ⊢
  rw [eqv]
  rw [List.getD_eq_getElem?_getD] at ha
  rcases h.2 with q|q <;> simp [q,GateOp.eval,lt,ha]


end PEqualNP.Outside.L_meta_25489_aux

namespace PEqualNP.Outside.L_meta_25489_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

lemma rowSep {n m d : ℕ} {G : Fin n → Fin m → Bool} (inj : Function.Injective G)
    (hc : ∀ u, (Finset.univ.filter (fun c => G u c = true)).card = d) {u v : Fin n}
    (hne : u ≠ v) : ∃ c, G u c = true ∧ G v c = false := by
  classical
  by_contra hn
  let U := Finset.univ.filter (fun c => G u c = true)
  let V := Finset.univ.filter (fun c => G v c = true)
  have sub : U ⊆ V := by
    intro c h
    have hu : G u c = true := (Finset.mem_filter.mp h).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    cases hv : G v c with
    | false => exact (hn ⟨c, hu, hv⟩).elim
    | true => rfl
  have eqv : U = V := Finset.eq_of_subset_of_card_le sub (by simp [U,V,hc])
  apply hne
  apply inj
  funext c
  have key : G u c = true ↔ G v c = true := by
    simpa [U,V] using (Finset.ext_iff.mp eqv c)
  cases h : G u c <;> cases h' : G v c <;> simp_all

lemma rowHasTrue {m d : ℕ} {g : Fin m → Bool}
    (hc : (Finset.univ.filter (fun c => g c = true)).card = d) (hd : 0 < d) :
    ∃ c, g c = true := by
  have h : 0 < (Finset.univ.filter (fun c => g c = true)).card := by omega
  obtain ⟨c,hc⟩ := Finset.card_pos.mp h
  exact ⟨c,(Finset.mem_filter.mp hc).2⟩

lemma rowHasFalse {m d : ℕ} {g : Fin m → Bool}
    (hc : (Finset.univ.filter (fun c => g c = true)).card = d) (hd : d < m) :
    ∃ c, g c = false := by
  classical
  by_contra hn
  have hall : ∀ c, g c = true := by
    intro c
    cases he : g c with
    | false => exact (hn ⟨c,he⟩).elim
    | true => rfl
  simp [hall] at hc
  omega

lemma rowInputHigh {n m : Nat} (C : Circuit) (u : Fin n) (c : Fin m) :
    signal C u c u.val = true := by
  change (C.gates.foldl stp (oneEach u c)).getD u.val false = true
  rw [pre _ _ _ (by rw [oe_len]; omega), oe_get]
  simp

lemma orHighMem {n m : Nat} {C : Circuit} {v : Fin n} {c : Fin m}
    {j : Fin C.gates.length} {a b t : Nat} (oj : orForm C j a b)
    (rb : ReadsBack (n+m) C) (ht : t ∈ (gateAt C j.val).inputs) (hi : signal C v c t = true) :
    signal C v c (n+m+j.val) = true := by
  have h : t = a ∨ t = b := by
    rcases oj.2 with e|e <;> simp [e] at ht <;> tauto
  rcases h with e|e
  · exact orHigh C v c j _ _ oj rb (e ▸ hi)
  · exact orHigh C v c j _ _ (show orForm C j b a from ⟨oj.1,oj.2.symm⟩) rb (e ▸ hi)

lemma rowOut {n m : Nat} {G : Fin n → Fin m → Bool} {C : Circuit} {u : Fin n}
    {i : Fin C.gates.length} {a : Nat}
    (rb : ReadsBack (n+m) C) (rep : Represents G C) (oi : orForm C i u.val a)
    (neg : ∃ c, G u c = false) : C.output ≠ u.val ∧ C.output ≠ n+m+i.val := by
  obtain ⟨c,hc⟩ := neg
  have hi := rowInputHigh C u c
  have hg := orHigh C u c i _ _ oi rb hi
  have ho : signal C u c C.output = false := (rep u c).trans hc
  constructor <;> intro he <;> rw [he] at ho <;> simp_all

lemma rowLow {n m : Nat} {G : Fin n → Fin m → Bool} {C : Circuit} {u v : Fin n} {c : Fin m}
    {i : Fin C.gates.length} {a : Nat} (mon : Monotone2 C) (rb : ReadsBack (n+m) C)
    (rep : Represents G C) (oi : orForm C i u.val a)
    (once : readsIn C (Finset.range C.gates.length) u.val = 1) (out : C.output ≠ u.val)
    (pos : G u c = true) (neg : G v c = false) : signal C v c (n+m+i.val) = false := by
  cases he : signal C v c (n+m+i.val) with
  | false => rfl
  | true =>
    exfalso
    apply saturated mon rb rep pos neg (fun z => z=u.val) rfl out
    intro z _ b hb e
    subst b
    have eqv := uniqueReader once (orMem oi) hb
    subst z
    exact he

lemma rowInjective {n m : Nat} {G : Fin n → Fin m → Bool} {C : Circuit}
    {f : Fin n → Fin C.gates.length} {s : Fin n → Nat}
    (mon : Monotone2 C) (rb : ReadsBack (n+m) C) (rep : Represents G C)
    (forms : ∀ u, orForm C (f u) u.val (s u))
    (once : ∀ u : Fin n, readsIn C (Finset.range C.gates.length) u.val = 1)
    (out : ∀ u : Fin n, C.output ≠ u.val)
    (sep : ∀ {u v}, u ≠ v → ∃ c, G u c = true ∧ G v c = false) : Function.Injective f := by
  intro u v e
  by_contra ne
  obtain ⟨c,hu,hv⟩ := sep ne
  have hlow := rowLow mon rb rep (forms u) (once u) (out u) hu hv
  have hhigh := orHigh C v c (f v) _ _ (forms v) rb (rowInputHigh C v c)
  rw [e,hhigh] at hlow
  contradiction

lemma rowNoRead {n m : Nat} {G : Fin n → Fin m → Bool} {C : Circuit}
    {f : Fin n → Fin C.gates.length} {s : Fin n → Nat}
    (mon : Monotone2 C) (rb : ReadsBack (n+m) C) (rep : Represents G C)
    (forms : ∀ u, orForm C (f u) u.val (s u))
    (once : ∀ u : Fin n, readsIn C (Finset.range C.gates.length) u.val = 1)
    (out : ∀ u : Fin n, C.output ≠ u.val)
    (sep : ∀ {u v}, u ≠ v → ∃ c, G u c = true ∧ G v c = false)
    (u v : Fin n) : n+m+(f u).val ∉ (gateAt C (f v).val).inputs := by
  intro ha
  by_cases e : v = u
  · subst v
    have := rb (f u).val (f u).isLt _ ha
    omega
  obtain ⟨c,hv,hu⟩ := sep e
  have hlow := rowLow mon rb rep (forms v) (once v) (out v) hv hu
  have hhigh := orHigh C u c (f u) _ _ (forms u) rb (rowInputHigh C u c)
  have highV := orHighMem (forms v) rb ha hhigh
  rw [highV] at hlow
  contradiction

lemma rowHasReader {n m : Nat} {G : Fin n → Fin m → Bool} {C : Circuit}
    {u : Fin n} {i : Fin C.gates.length} {a : Nat}
    (mon : Monotone2 C) (rb : ReadsBack (n+m) C) (rep : Represents G C)
    (oi : orForm C i u.val a) (once : readsIn C (Finset.range C.gates.length) u.val = 1)
    (out : C.output ≠ u.val ∧ C.output ≠ n+m+i.val)
    (pos : ∃ c, G u c = true) (nonfull : ∀ c, ∃ v, G v c = false) :
    ∃ r : Fin C.gates.length, n+m+i.val ∈ (gateAt C r.val).inputs := by
  obtain ⟨c,hu⟩ := pos
  obtain ⟨v,hv⟩ := nonfull c
  by_contra no
  apply saturated mon rb rep hu hv (fun z => z=u.val ∨ z=n+m+i.val) (.inl rfl)
    (fun h => h.elim out.1 out.2)
  intro z nz b hb hs
  rcases hs with eu|ei
  · subst b
    have eqv := uniqueReader once (orMem oi) hb
    exact False.elim (nz (.inr (congrArg (fun j : Fin C.gates.length => n+m+j.val) eqv)))
  · subst b
    exact (no ⟨z,hb⟩).elim

lemma rowSecond {n m : Nat} {G : Fin n → Fin m → Bool} {C : Circuit}
    {u v : Fin n} {i j t : Fin C.gates.length} {a b : Nat}
    (mon : Monotone2 C) (rb : ReadsBack (n+m) C) (rep : Represents G C)
    (oi : orForm C i u.val a) (oj : orForm C j v.val b)
    (once : readsIn C (Finset.range C.gates.length) u.val = 1)
    (out : C.output ≠ u.val ∧ C.output ≠ n+m+i.val)
    (sep : ∃ c, G u c = true ∧ G v c = false)
    (ot : orForm C t (n+m+i.val) (n+m+j.val)) :
    ∃ z : Fin C.gates.length, z ≠ t ∧ n+m+i.val ∈ (gateAt C z.val).inputs := by
  obtain ⟨c,hu,hv⟩ := sep
  have hj := orHigh C v c j _ _ oj rb (rowInputHigh C v c)
  have ht := orHigh C v c t _ _ (show orForm C t (n+m+j.val) (n+m+i.val) from ⟨ot.1,ot.2.symm⟩) rb hj
  by_contra no
  apply saturated mon rb rep hu hv (fun z => z=u.val ∨ z=n+m+i.val) (.inl rfl)
    (fun h => h.elim out.1 out.2)
  intro z nz a ha hs
  rcases hs with eu|ei
  · subst a
    have eqv := uniqueReader once (orMem oi) ha
    exact False.elim (nz (.inr (congrArg (fun g : Fin C.gates.length => n+m+g.val) eqv)))
  · subst a
    by_cases zt : z=t
    · subst z; exact ht
    · exact (no ⟨z,zt,ha⟩).elim

end PEqualNP.Outside.L_meta_25489_aux


namespace PEqualNP.Outside.L_meta_25489_aux

def rowReaders {n N : ℕ} (rows : Fin N → Finset (Fin n)) (x : Fin n) : Finset (Fin N) :=
  Finset.univ.filter (fun g => x ∈ rows g)

def needsExtra {n N : ℕ} (rows : Fin N → Finset (Fin n)) (x : Fin n) : Prop :=
  (rowReaders rows x).card = 1 ∧ ∃ g, x ∈ rows g ∧ (rows g).card = 2

theorem countRowGates {n N : ℕ} (first : Fin n → Fin N)
    (rows : Fin N → Finset (Fin n)) (hfirst : Function.Injective first)
    (hprivate : ∀ x, rows (first x) = ∅)
    (hfan : ∀ g, (rows g).card ≤ 2)
    (hlive : ∀ x, (rowReaders rows x).Nonempty)
    (hextra : ∃ extra : {x : Fin n // needsExtra rows x} → Fin N,
      Function.Injective extra ∧ (∀ x, rows (extra x) = ∅) ∧
      ∀ x y, extra x ≠ first y) :
    2 * n ≤ N := by
  classical
  obtain ⟨extra, einj, eempty, ene⟩ := hextra
  let A : Finset (Fin N) := Finset.univ.image first
  let B : Finset (Fin N) := Finset.univ.filter (fun g => (rows g).Nonempty)
  let D : Finset (Fin N) := Finset.univ.image extra
  let U : Finset (Fin n) := Finset.univ.filter (needsExtra rows)
  have aCard : A.card = n := by simp [A, Finset.card_image_of_injective _ hfirst]
  have dCard : D.card = U.card := by
    rw [show D = Finset.univ.image extra from rfl,
      Finset.card_image_of_injective _ einj, Finset.card_univ]
    change Fintype.card {x : Fin n // needsExtra rows x} =
      (Finset.univ.filter (needsExtra rows)).card
    exact Fintype.card_subtype _
  have ab : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro g hA hB
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hA
    have h := (Finset.mem_filter.mp hB).2
    simp [hprivate x] at h
  have ac : Disjoint A D := by
    rw [Finset.disjoint_left]
    intro g hA hD
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hD
    exact ene y x hy
  have bc : Disjoint B D := by
    rw [Finset.disjoint_left]
    intro g hB hD
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hD
    have h := (Finset.mem_filter.mp hB).2
    simp [eempty x] at h
  have budget : n + B.card + U.card ≤ N := by
    have h := Finset.card_le_card (Finset.subset_univ (A ∪ B ∪ D))
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨ac, bc⟩),
      Finset.card_union_of_disjoint ab, aCard, dCard, Finset.card_univ, Fintype.card_fin] at h
    exact h
  let weight : Fin N → ℕ := fun g => if (rows g).card = 1 then 2 else 1
  let charge : Fin n → Fin N → ℕ := fun x g => if x ∈ rows g then weight g else 0
  have col (g : Fin N) : (∑ x, charge x g) ≤ if g ∈ B then 2 else 0 := by
    have sumEq : (∑ x, charge x g) = (rows g).card * weight g := by
      simp [charge, Nat.nsmul_eq_mul]
    rw [sumEq]
    by_cases non : (rows g).Nonempty
    · have mem : g ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, non⟩
      rw [if_pos mem]
      have hu := hfan g
      by_cases one : (rows g).card = 1 <;> simp [weight, one] <;> omega
    · have empty : rows g = ∅ := Finset.not_nonempty_iff_eq_empty.mp non
      simp [empty]
  have row (x : Fin n) : 2 ≤ (∑ g, charge x g) + (if x ∈ U then 1 else 0) := by
    let R := rowReaders rows x
    have lower : R.card ≤ ∑ g, charge x g := by
      calc
        R.card = ∑ g : Fin N, (if g ∈ R then 1 else 0) := by simp
        _ ≤ ∑ g, charge x g := by
          apply Finset.sum_le_sum
          intro g _
          by_cases y : x ∈ rows g
          · have hr : g ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, y⟩
            simp [charge, hr, y, weight] <;> split <;> omega
          · have hr : g ∉ R := by simpa [R, rowReaders] using y
            simp [charge, hr, y]
    by_cases big : 2 ≤ R.card
    · omega
    obtain ⟨g, hg⟩ := hlive x
    have hc := Finset.card_pos.mpr (hlive x)
    change 0 < R.card at hc
    have hone : R.card = 1 := by omega
    have hx : x ∈ rows g := (Finset.mem_filter.mp hg).2
    by_cases two : (rows g).card = 2
    · have u : x ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hone, g, hx, two⟩
      rw [if_pos u]
      omega
    · have hpos := Finset.card_pos.mpr ⟨x, hx⟩
      have hcap := hfan g
      have h1 : (rows g).card = 1 := by omega
      have hin : charge x g ≤ ∑ q, charge x q :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
      have unit : charge x g = 2 := by simp [charge, weight, hx, h1]
      rw [unit] at hin
      omega
  have totalRow := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun x _ => row x)
  have totalCol := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N))) (fun g _ => col g)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul] at totalRow
  rw [Finset.sum_comm] at totalRow
  have sumU : (∑ x : Fin n, if x ∈ U then 1 else 0) = U.card := by simp
  have sumB : (∑ g : Fin N, if g ∈ B then 2 else 0) = B.card * 2 := by
    simp
  rw [sumU] at totalRow
  rw [sumB] at totalCol
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def circuitRows {n : ℕ} (m : ℕ) (C : Circuit) (first : Fin n → Fin C.gates.length)
    (g : Fin C.gates.length) : Finset (Fin n) :=
  Finset.univ.filter (fun x => n + m + (first x).val ∈ (gateAt C g.val).inputs)

@[simp] theorem circuitRows_mem {n m : ℕ} {C : Circuit} {first : Fin n → Fin C.gates.length}
    {g : Fin C.gates.length} {x : Fin n} :
    x ∈ circuitRows m C first g ↔ n + m + (first x).val ∈ (gateAt C g.val).inputs := by
  simp [circuitRows]

theorem countCircuitRows {n m : ℕ} (C : Circuit) (first : Fin n → Fin C.gates.length)
    (inj : Function.Injective first) (mono : Monotone2 C)
    (sep : ∀ x y, n+m+(first x).val ∉ (gateAt C (first y).val).inputs)
    (live : ∀ x, ∃ q : Fin C.gates.length, n+m+(first x).val ∈ (gateAt C q.val).inputs)
    (ext : ∃ extra : {x : Fin n // needsExtra (circuitRows m C first) x} → Fin C.gates.length,
      Function.Injective extra ∧
      (∀ x y, n+m+(first y).val ∉ (gateAt C (extra x).val).inputs) ∧
      ∀ x y, extra x ≠ first y) :
    2 * n ≤ C.size := by
  classical
  apply countRowGates (rows := circuitRows m C first) first inj
  · intro y
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact sep x y (circuitRows_mem.mp hx)
  · intro g
    let val : Fin n → ℕ := fun x => n+m+(first x).val
    have hin : Function.Injective val := by
      intro a b he
      apply inj
      apply Fin.ext
      change n+m+(first a).val = n+m+(first b).val at he
      omega
    have sub : (circuitRows m C first g).image val ⊆ (gateAt C g.val).inputs.toFinset := by
      intro q hq
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
      exact List.mem_toFinset.mpr (circuitRows_mem.mp hx)
    rw [← Finset.card_image_of_injective _ hin]
    have same : gateAt C g.val = C.gates[g.val] := by
      unfold gateAt
      exact List.getD_eq_getElem _ _ g.isLt
    exact (Finset.card_le_card sub).trans ((List.toFinset_card_le _).trans
      (same.symm ▸ (mono _ (List.getElem_mem g.isLt)).2))
  · intro x
    obtain ⟨q,hq⟩ := live x
    exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, circuitRows_mem.mpr hq⟩⟩
  · obtain ⟨extra, hin, hnot, hne⟩ := ext
    refine ⟨extra, hin, ?_, hne⟩
    intro x
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact hnot x y (circuitRows_mem.mp hy)

private theorem twoInBinary {l : List ℕ} {a b : ℕ}
    (len : l.length ≤ 2) (ne : a ≠ b) (ha : a ∈ l) (hb : b ∈ l) :
    l = [a,b] ∨ l = [b,a] := by
  rcases l with _ | ⟨p, _ | ⟨q, _ | ⟨r, l⟩⟩⟩
  · simp at ha
  · simp at ha hb
    exact (ne (ha.trans hb.symm)).elim
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with h|h <;> rcases hb with e|e <;> grind
  · simp at len

theorem needsExtra_data {n m : ℕ} {C : Circuit} {first : Fin n → Fin C.gates.length}
    (inj : Function.Injective first) (mono : Monotone2 C) {x : Fin n}
    (bad : needsExtra (circuitRows m C first) x) :
    ∃ (t : Fin C.gates.length) (y : Fin n), y ≠ x ∧
      (∀ g : Fin C.gates.length, n+m+(first x).val ∈ (gateAt C g.val).inputs → g = t) ∧
      ((gateAt C t.val).inputs = [n+m+(first x).val,n+m+(first y).val] ∨
       (gateAt C t.val).inputs = [n+m+(first y).val,n+m+(first x).val]) := by
  classical
  obtain ⟨one, t, hxt, two⟩ := bad
  obtain ⟨y, hyt, yne⟩ := Finset.exists_mem_ne (s := circuitRows m C first t)
    (by omega) x
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp one
  have eq (g : Fin C.gates.length) (hr : x ∈ circuitRows m C first g) : g = p := by
    have hg : g ∈ rowReaders (circuitRows m C first) x :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩
    simpa only [hp, Finset.mem_singleton] using hg
  refine ⟨t, y, yne, fun g hg => (eq g (circuitRows_mem.mpr hg)).trans (eq t hxt).symm,
    twoInBinary ?_ ?_ (circuitRows_mem.mp hxt) (circuitRows_mem.mp hyt)⟩
  · have same : gateAt C t.val = C.gates[t.val] := by
      unfold gateAt
      exact List.getD_eq_getElem _ _ t.isLt
    rw [same]
    exact (mono _ (List.getElem_mem t.isLt)).2
  · intro e
    apply yne
    apply inj
    apply Fin.ext
    omega

end PEqualNP.Outside.L_meta_25489_aux


namespace PEqualNP.Outside.L_meta_25489_aux

theorem chooseExtras {ι γ α : Type} {P : ι → Prop} {G : ι → α → Bool}
    {profile : γ → α → Bool} {first : ι → γ} {free : γ → ι → Prop}
    (inj : Function.Injective G)
    (available : ∀ x : {i // P i}, ∃ e : γ, (∀ c, profile e c = G x.val c) ∧
      (∀ a, e ≠ first a) ∧ (∀ a, free e a)) :
    ∃ extra : {i // P i} → γ, Function.Injective extra ∧
      (∀ x a, free (extra x) a) ∧ ∀ x a, extra x ≠ first a := by
  classical
  choose extra hprofile hfirst hfree using available
  refine ⟨extra,?_,hfree,hfirst⟩
  intro x y he
  apply Subtype.ext
  apply inj
  funext c
  exact (hprofile x c).symm.trans ((congrArg (fun e => profile e c) he).trans (hprofile y c))

end PEqualNP.Outside.L_meta_25489_aux

namespace PEqualNP.Outside.L_meta_25489_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

private lemma pathClosed {r : ℕ → ℕ → Prop} {a b : ℕ} (p : ℕ → Prop) (ha : p a)
    (closed : ∀ i j, p i → r i j → p j) (path : Relation.ReflTransGen r a b) : p b := by
  induction path with
  | refl => exact ha
  | tail _ step ih => exact closed _ _ ih step

lemma soleSharedValues {n m : ℕ} {G : Fin n → Fin m → Bool} {C : Circuit}
    {x v : Fin n} {i j t : Fin C.gates.length} {a b : ℕ}
    (mon : Monotone2 C) (rb : ReadsBack (n+m) C) (rep : Represents G C)
    (hne : x ≠ v) (hij : i ≠ j) (oi : orForm C i x.val a) (oj : orForm C j v.val b)
    (ux : readsIn C (Finset.range C.gates.length) x.val = 1)
    (uv : readsIn C (Finset.range C.gates.length) v.val = 1)
    (ox : C.output ≠ x.val ∧ C.output ≠ n+m+i.val) (ov : C.output ≠ v.val)
    (sole : ∀ z : Fin C.gates.length, n+m+i.val ∈ (gateAt C z.val).inputs → z = t)
    (htand : (gateAt C t.val).op = GateOp.and)
    (hjt : n+m+j.val ∈ (gateAt C t.val).inputs)
    (nonfull : ∀ c, ∃ w, G w c = false) : ∀ c,
      let col := List.replicate n false ++ List.ofFn (fun z : Fin m => decide (z = c))
      let value := (C.wires col).getD (n+m+j.val) false
      (G x c = true → value = true) ∧ (G v c = true → value = false) := by
  let edge := fun y z : Nat => ∃ g : Fin C.gates.length,
    z = n+m+g.val ∧ y ∈ (gateAt C g.val).inputs
  have ex : ∀ z, edge x.val z → z = n+m+i.val := by
    rintro z ⟨g,rfl,h⟩
    rw [uniqueReader ux (orMem oi) h]
  have ev : ∀ z, edge v.val z → z = n+m+j.val := by
    rintro z ⟨g,rfl,h⟩
    rw [uniqueReader uv (orMem oj) h]
  have ei : ∀ z, edge (n+m+i.val) z → z = n+m+t.val := by
    rintro z ⟨g,rfl,h⟩
    rw [sole g h]
  have inc : ∀ y z, edge y z → y < z := by
    rintro y z ⟨g,rfl,h⟩
    exact rb g.val g.isLt y h
  have hjlt := rb t.val t.isLt _ hjt
  have hneval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have applyCut := cut87 n m G C x v t (n+m+j.val)
    mon rb rep hne htand hjt
  intro c
  apply applyCut <;> clear applyCut
  · rintro ⟨_,_,h⟩
    apply (fun h : C.output=x.val ∨ C.output=n+m+i.val => h.elim ox.1 ox.2)
    apply pathClosed (fun z => z=x.val ∨ z=n+m+i.val) (Or.inl rfl) _ h
    rintro y z (rfl | rfl) ⟨_,hz,e⟩
    · exact Or.inr (ex z e)
    · exact (hz (ei z e)).elim
  · rintro ⟨_,_,h⟩
    apply ov
    apply pathClosed (fun z => z=v.val) rfl _ h
    rintro y z rfl ⟨_,hz,e⟩
    exact (hz (ev z e)).elim
  · intro h
    have hw := pathClosed (r:=edge) (fun z => z=x.val ∨ z=n+m+i.val ∨ n+m+t.val ≤ z)
      (Or.inl rfl) (by
        rintro y z (rfl | rfl | hy) e
        · exact Or.inr (Or.inl (ex z e))
        · exact Or.inr (Or.inr (ei z e).ge)
        · exact Or.inr (Or.inr (le_trans hy (inc _ _ e).le))) h
    change n+m+j.val = x.val ∨ n+m+j.val = n+m+i.val ∨ n+m+t.val ≤ n+m+j.val at hw
    omega
  · exact nonfull c

end PEqualNP.Outside.L_meta_25489_aux

namespace PEqualNP.Outside.L_meta_25489_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
namespace Extra89
open PEqualNP.Outside.L_meta_25489_aux.Trace87

abbrev col {m : Nat} (n : Nat) (c : Fin m) : List Bool :=
  List.replicate n false ++ List.ofFn (fun z : Fin m => decide (z=c))
abbrev val (C : Circuit) (X : List Bool) (z : Nat) := (C.wires X).getD z false
abbrev occ {n : Nat} (C : Circuit) (X : List Bool) (i : Fin C.gates.length) :=
  val C X (n+i.val)

lemma separation {k : Nat} {P Q : Fin (2*k) → Bool}
    (hP : (Finset.univ.filter (fun c => P c = true)).card = k)
    (hQ : (Finset.univ.filter (fun c => Q c = true)).card = k)
    (dis : ∀ c, P c = true → Q c = false) :
    ∀ c, Q c = !P c := by
  classical
  let s := Finset.univ.filter (fun c => P c = true)
  let t := Finset.univ.filter (fun c => Q c = true)
  have sub : s ⊆ tᶜ := by
    intro z hz
    have hp : P z = true := (Finset.mem_filter.mp hz).2
    simpa [t,dis z hp]
  have card : tᶜ.card = k := by
    rw [Finset.card_compl, Fintype.card_fin]
    change t.card = k at hQ
    omega
  have eq : s = tᶜ := Finset.eq_of_subset_of_card_le sub (by simpa [s,card] using hP.ge)
  intro c
  have h : P c = true ↔ Q c = false := by
    have e : c ∈ s ↔ c ∈ tᶜ := by rw [eq]
    simpa [s,t] using e
  cases h1 : P c <;> cases h2 : Q c <;> simp_all

lemma gated {C : Circuit} {N : Nat} (rb : ReadsBack N C) (X : List Bool) (len : X.length=N)
    (z : Fin C.gates.length) :
    val C X (N+z.val) = (gateAt C z.val).op.eval ((gateAt C z.val).inputs.map (val C X)) := by
  rw [hga C z.val z.isLt]
  exact gval C N rb X len z.val z.isLt

lemma orUp {C : Circuit} {N : Nat} (rb : ReadsBack N C) (X : List Bool) (len : X.length=N)
    (z : Fin C.gates.length) (hz : (gateAt C z.val).op=.or) (a : Nat)
    (ha : a ∈ (gateAt C z.val).inputs) (ht : val C X a=true) :
    val C X (N+z.val)=true := by
  rw [gated rb _ len, hz]
  exact any_mem_true _ _ a ha ht

lemma colLe {n m : Nat} {C : Circuit} (mono : Monotone2 C)
    (u : Fin n) (c : Fin m) (i : Nat) :
    val C (col n c) i = true → val C (oneEach u c) i = true := by
  apply mono2 C mono _ _ (by simp [col,oe_len])
  intro j _ hj
  rw [col_get] at hj
  rw [oe_get]
  simpa only [decide_eq_true_eq] using Or.inr (of_decide_eq_true hj : j=n+c.val)

lemma exactExtra {n k : Nat} {G : Fin n → Fin (2*k) → Bool} {C : Circuit}
    (hk : 2 ≤ k) (inj : Function.Injective G)
    (card : ∀ a, (Finset.univ.filter (fun c => G a c = true)).card = k)
    (nonfull : ∀ c, ∃ w : Fin n, G w c = false)
    (mono : Monotone2 C) (rb : ReadsBack (n+2*k) C)
    (f : Fin n → Fin C.gates.length) (s : Fin n → Nat)
    (ors : ∀ a, (gateAt C (f a).val).op=.or ∧
      ((gateAt C (f a).val).inputs=[a.val,s a] ∨ (gateAt C (f a).val).inputs=[s a,a.val]))
    (low : ∀ a b c, G a c = true → G b c = false →
      val C (oneEach b c) (n+2*k+(f a).val)=false)
    (diff : ∀ a b : Fin n, a≠b → ∃ c, G a c=true ∧ G b c=false)
    (x v : Fin n)
    (tells : ∀ c, (G x c=true → val C (col n c) (n+2*k+(f v).val)=true) ∧
      (G v c=true → val C (col n c) (n+2*k+(f v).val)=false)) :
    ∃ e : Fin C.gates.length, n+2*k+e.val=s v ∧
      (∀ c, val C (col n c) (n+2*k+e.val) = G x c) ∧
      (∀ a, e ≠ f a) ∧ (∀ a, n+2*k+(f a).val ∉ (gateAt C e.val).inputs) := by
  classical
  let N := n+2*k
  let w : Fin C.gates.length → Nat := fun a => N+a.val
  have len (c : Fin (2*k)) : (col n c).length=N := by simp [col,N]
  have self (a : Fin n) (c : Fin (2*k)) : val C (oneEach a c) (w (f a))=true := by
    apply orUp rb _ (oe_len _ _) _ (ors a).1 a.val
    · rcases (ors a).2 with eq|eq <;> simp [eq]
    · change (C.gates.foldl stp (oneEach a c)).getD a.val false=true
      rw [pre _ _ _ (by rw [oe_len];omega),oe_get]
      simp
  have columnLow (a : Fin n) (c : Fin (2*k)) (hc : G a c=true) :
      val C (col n c) (w (f a))=false := by
    obtain ⟨b,hb⟩ := nonfull c
    have ll := low a b c hc hb
    cases ht : val C (col n c) (w (f a)) with
    | false => rfl
    | true =>
      have high := colLe mono b c (w (f a)) ht
      change val C (oneEach b c) (w (f a)) = false at ll
      rw [ll] at high
      contradiction
  have dis (c) (hc : G x c=true) : G v c = false := by
    cases hv : G v c with
    | false => rfl
    | true => exact False.elim (Bool.noConfusion ((tells c).1 hc |>.symm.trans ((tells c).2 hv)))
  have complement := separation (card x) (card v) dis
  have sig (c) : val C (col n c) (s v)=G x c := by
    have eq : val C (col n c) (w (f v)) = val C (col n c) (s v) := by
      have z : val C (col n c) v.val = false := by
        change (C.gates.foldl stp (col n c)).getD v.val false=false
        rw [pre _ _ _ (by rw [len]; dsimp [N];omega),col_get]
        simp [show v.val ≠ n+c.val by omega]
      change val C (col n c) (N+(f v).val) = _
      rw [gated rb _ (len c), (ors v).1]
      rcases (ors v).2 with q|q
      · rw [q]
        change (val C (col n c) v.val || (val C (col n c) (s v) || false)) = _
        rw [z]; simp
      · rw [q]
        change (val C (col n c) (s v) || (val C (col n c) v.val || false)) = _
        rw [z]; simp
    rw [← eq]
    cases hx : G x c with
    | true => exact (tells c).1 hx
    | false => exact (tells c).2 (by rw [complement c,hx];rfl)
  have mems : s v ∈ (gateAt C (f v).val).inputs := by
    rcases (ors v).2 with q|q <;> simp [q]
  have lt := rb (f v).val (f v).isLt (s v) mems
  have internal : N ≤ s v := by
    by_contra! hl
    have big : 1 < (Finset.univ.filter (fun c => G x c=true)).card := by rw [card x];omega
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp big
    have one (t : Fin (2*k)) (ht : G x t=true) : s v=n+t.val := by
      have e := (sig t).trans ht
      change (C.gates.foldl stp (col n t)).getD (s v) false=true at e
      rw [pre _ _ _ (by rwa [len]),col_get] at e
      exact of_decide_eq_true e
    have aa := one a (Finset.mem_filter.mp ha).2
    have bb := one b (Finset.mem_filter.mp hb).2
    exact hab (Fin.ext (by omega))
  let e : Fin C.gates.length := ⟨s v-N,by dsimp [N] at internal ⊢; have := (f v).isLt;omega⟩
  have he : w e=s v := by change N + (s v-N) = s v; omega
  have next : w e < w (f v) := by rw [he]; exact lt
  have sourceOR (a : Fin n) (h : ∀ c : Fin (2*k), val C (oneEach a c) (w e)=true) :
      a=v := by
    by_contra hv
    obtain ⟨c,hvc,hac⟩ := diff v a (Ne.symm hv)
    have hfalse := low v a c hvc hac
    have high := orUp rb _ (oe_len a c) _ (ors v).1 (s v) mems (he ▸ h c)
    rw [hfalse] at high
    contradiction
  refine ⟨e,he,fun c => ?_,?_,?_⟩
  · change val C (col n c) (w e)=G x c
    rw [he,sig]
  · intro a h
    have ae : a=v := sourceOR a (fun c => h ▸ self a c)
    subst a
    rw [h] at next
    exact Nat.lt_irrefl _ next
  · intro a read
    change w (f a) ∈ (gateAt C e.val).inputs at read
    have before := rb e.val e.isLt _ read
    change w (f a) < w e at before
    have av : a≠v := by
      intro hv
      subst a
      omega
    have op := (mono _ (List.getElem_mem e.isLt)).1
    rw [← hga C e.val e.isLt] at op
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
    rcases op with hand|hor
    · have disA (c) (hx : G x c=true) : G a c=false := by
        cases hA : G a c with
        | false => rfl
        | true =>
          have high := (he ▸ (sig c).trans hx : val C (col n c) (w e)=true)
          change val C (col n c) (N+e.val)=true at high
          rw [gated rb _ (len c),hand] at high
          have af := all_mem_true _ _ _ read high
          rw [columnLow a c hA] at af
          contradiction
      have matchA := separation (card x) (card a) disA
      apply av
      apply inj
      funext c
      exact (matchA c).trans (complement c).symm
    · apply av
      apply sourceOR a
      intro c
      exact orUp rb _ (oe_len a c) _ hor (w (f a)) read (self a c)

end Extra89
end PEqualNP.Outside.L_meta_25489_aux

open PEqualNP.Outside.L_meta_25489_aux PEqualNP.MetaComplexity.NestedCover PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_25489 : ∀ (n k : ℕ) (G : Fin n → Fin (2 * k) → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit),
  2 ≤ k →
  Function.Injective G →
  (∀ u, (Finset.univ.filter (fun c => G u c = true)).card = k) →
  (∀ c, ∃ v, G v c = false) →
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2 * k) C →
  PEqualNP.Represents.Represents G C →
  (∀ x : Fin n,
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) x.val = 1 ∧
    ∃ (j : Fin C.gates.length) (s : ℕ),
      (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      ((C.gates.get j).inputs = [x.val, s] ∨ (C.gates.get j).inputs = [s, x.val])) →
  2 * n ≤ C.size := by
  intro n k G C hk inj card nonfull mono rb rep unary
  classical
  have form (u : Fin n) : ∃ j : Fin C.gates.length, ∃ s : Nat, orForm C j u.val s := by
    obtain ⟨j,s,hop,his⟩ := (unary u).2
    exact ⟨j,s,by simpa only [List.get_eq_getElem,orForm,gateAt,List.getD_eq_getElem _ _ j.isLt] using And.intro hop his⟩
  choose f s forms using form
  have once (u : Fin n) : readsIn C (Finset.range C.gates.length) u.val = 1 := (unary u).1
  have sep {u v : Fin n} (h : u≠v) := rowSep inj card h
  have out (u : Fin n) := rowOut rb rep (forms u) (rowHasFalse (card u) (by omega))
  have fi := rowInjective mono rb rep forms once (fun u => (out u).1) @sep
  apply countCircuitRows C f fi mono (rowNoRead mono rb rep forms once (fun u => (out u).1) @sep)
    (fun u => rowHasReader mono rb rep (forms u) (once u) (out u) (rowHasTrue (card u) (by omega)) nonfull)
  apply chooseExtras (P:=needsExtra (circuitRows (2*k) C f)) (first:=f) (free:=fun e a => n+2*k+(f a).val ∉ (gateAt C e.val).inputs) (G:=G) (profile:=fun (e : Fin C.gates.length) c => Extra89.val C (Extra89.col n c) (n+2*k+e.val)) inj
  intro x
  obtain ⟨t,y,hy,sole,args⟩ := needsExtra_data fi mono x.property
  have hxy : x.val ≠ y := Ne.symm hy
  have memy : n+2*k+(f y).val ∈ (gateAt C t.val).inputs := by rcases args with a|a <;> simp [a]
  have hop : (gateAt C t.val).op = GateOp.and := by
    have gateEq : gateAt C t.val = C.gates[t.val] := by unfold gateAt;rw [List.getD_eq_getElem _ _ t.isLt]
    have oh := (mono _ (List.getElem_mem t.isLt)).1
    rw [←gateEq] at oh
    rcases oh with ha|ho
    · exact ha
    · obtain ⟨z,ne,mem⟩ := rowSecond mono rb rep (forms x.val) (forms y) (once x.val) (out x.val) (sep hxy) (show orForm C t _ _ from ⟨ho,args⟩)
      exact False.elim (ne (sole z mem))
  have tells := soleSharedValues mono rb rep hxy (fun e => hxy (fi e)) (forms x.val) (forms y) (once x.val) (once y) (out x.val) (out y).1 sole hop memy nonfull
  obtain ⟨e,_,hp,eo,ef⟩ := Extra89.exactExtra hk inj card nonfull mono rb f s forms
    (fun a b c ha hb => rowLow mono rb rep (forms a) (once a) (out a).1 ha hb) (fun a b h=>sep h) x.val y tells
  exact ⟨e,hp,eo,ef⟩

