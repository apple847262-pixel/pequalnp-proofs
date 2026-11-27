import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_25488_aux

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

end PEqualNP.Outside.L_meta_25488_aux
open PEqualNP.Outside.L_meta_25488_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_25488 : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : Fin n) (c : Fin m)
    (i j : Fin C.gates.length) (p q : ℕ),
  let g := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let wire := fun idx : Fin C.gates.length => n + m + idx.val
  let isOr := fun (z : Fin C.gates.length) (a b : ℕ) =>
    (g z.val).op = .or ∧ ((g z.val).inputs = [a, b] ∨ (g z.val).inputs = [b, a])
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents G C →
  u ≠ v → i ≠ j → isOr i u.val p → isOr j v.val q →
  PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length) u.val = 1 →
  C.output ∉ [u.val, wire i] → G u c = true → G v c = false →
  (C.wires (PEqualNP.Represents.oneEach v c)).getD (wire i) false = false ∧
    ∀ t : Fin C.gates.length, isOr t (wire i) (wire j) →
      ∃ h : Fin C.gates.length, h ≠ t ∧ wire i ∈ (g h.val).inputs := by
  intro n m G C u v c i j p q
  dsimp only
  intro mono rb rep huv hij oi oj reads hout gu gv
  change orForm C i u.val p at oi
  change orForm C j v.val q at oj
  have exU : C.output ≠ u.val := fun e => hout (e ▸ List.mem_cons_self ..)
  have exI : C.output ≠ n+m+i.val := fun e => hout (by simp [e])
  have highV : signal C v c v.val = true := by
    change (C.gates.foldl stp (PEqualNP.Represents.oneEach v c)).getD v.val false = true
    rw [pre _ _ _ (by rw [oe_len];omega),oe_get]
    simp
  have highJ := orHigh C v c j _ _ oj rb highV
  constructor
  · change signal C v c (n+m+i.val) = false
    cases hk : signal C v c (n+m+i.val) with
    | false => rfl
    | true =>
      exfalso
      apply saturated mono rb rep gu gv (fun z => z=u.val) rfl exU
      intro z _ a ha eq
      subst a
      have e := uniqueReader reads (orMem oi) ha
      subst z; exact hk
  · intro t ot
    change orForm C t (n+m+i.val) (n+m+j.val) at ot
    have highT := orHigh C v c t _ _ (show orForm C t (n+m+j.val) (n+m+i.val) from ⟨ot.1,ot.2.symm⟩) rb highJ
    by_contra hnone
    apply saturated mono rb rep gu gv (fun z => z=u.val ∨ z=n+m+i.val) (.inl rfl) (fun h => h.elim exU exI)
    intro z nz a ha hs
    rcases hs with eu|ei
    · subst a
      have eq := uniqueReader reads (orMem oi) ha
      exact False.elim (nz (.inr (congrArg (fun g : Fin C.gates.length => n+m+g.val) eq)))
    · subst a
      by_cases zt : z=t
      · subst z; exact highT
      · exact False.elim (hnone ⟨z,zt,ha⟩)
