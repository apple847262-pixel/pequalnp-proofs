import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_372_aux

def suffix {f n : ℕ}
    (rule : (i : Fin n) → (Fin f → Bool) → (Fin i.val → Bool) → Bool)
    (seed : Fin f → Bool) (i : Fin n) : Bool :=
  rule i seed (fun j => suffix rule seed (Fin.castLE (Nat.le_of_lt i.isLt) j))
termination_by i.val
decreasing_by exact j.isLt

def word {f n : ℕ}
    (rule : (i : Fin n) → (Fin f → Bool) → (Fin i.val → Bool) → Bool)
    (seed : Fin f → Bool) : Fin (f+n) → Bool :=
  Fin.addCases seed (suffix rule seed)

theorem prefix_word {f n : ℕ}
    (rule : (i : Fin n) → (Fin f → Bool) → (Fin i.val → Bool) → Bool)
    (seed : Fin f → Bool) :
    (fun a : Fin f => word rule seed (Fin.castAdd n a)) = seed := by
  funext a
  simp [word]

theorem suffix_unique {f n : ℕ}
    (rule : (i : Fin n) → (Fin f → Bool) → (Fin i.val → Bool) → Bool)
    (seed : Fin f → Bool) (z : Fin n → Bool)
    (hz : ∀ i : Fin n, z i = rule i seed (fun j => z (Fin.castLE (Nat.le_of_lt i.isLt) j)))
    (i : Fin n) : z i = suffix rule seed i := by
  rw [hz i, suffix]
  congr 1
  funext j
  exact suffix_unique rule seed z hz (Fin.castLE (Nat.le_of_lt i.isLt) j)
termination_by i.val
decreasing_by exact j.isLt

end PEqualNP.Outside.L_lib_372_aux

open PEqualNP.Outside.L_lib_372_aux in
theorem PEqualNP.Outside.L_lib_372 :
∀ (free forced : ℕ)
  (rule : (i : Fin forced) → (Fin free → Bool) → (Fin i.val → Bool) → Bool),
  let freeBits := fun (word : Fin (free + forced) → Bool) (a : Fin free) =>
    word (Fin.castAdd forced a)
  let passes := fun (word : Fin (free + forced) → Bool) =>
    ∀ i : Fin forced, word (Fin.natAdd free i) =
      rule i (freeBits word)
        (fun j => word (Fin.natAdd free (Fin.castLE (Nat.le_of_lt i.isLt) j)))
  ∃ complete : (Fin free → Bool) ≃ { word // passes word },
    (∀ seed word, freeBits word.val = seed ↔ word = complete seed) ∧
    Nat.card { word // passes word } = 2 ^ free := by
  intro f n rule
  dsimp only
  let prefBits := fun (z : Fin (f+n) → Bool) (a : Fin f) => z (Fin.castAdd n a)
  let P := fun (z : Fin (f+n) → Bool) => ∀ i : Fin n, z (Fin.natAdd f i) =
    rule i (prefBits z) (fun j => z (Fin.natAdd f (Fin.castLE (Nat.le_of_lt i.isLt) j)))
  let build := fun seed : Fin f → Bool => word rule seed
  have pbuild (seed : Fin f → Bool) : P (build seed) := by
    intro i
    change word rule seed (Fin.natAdd f i) =
      rule i (fun a => word rule seed (Fin.castAdd n a))
        (fun j => word rule seed (Fin.natAdd f (Fin.castLE (Nat.le_of_lt i.isLt) j)))
    rw [prefix_word]
    simp only [word, Fin.addCases_right]
    rw [suffix]
  let e : (Fin f → Bool) ≃ {z // P z} := {
    toFun := fun seed => ⟨build seed, pbuild seed⟩
    invFun := fun z => prefBits z.val
    left_inv := fun seed => prefix_word rule seed
    right_inv := by
      intro z
      apply Subtype.ext
      funext t
      refine Fin.addCases (motive := fun i => build (prefBits z.val) i = z.val i) ?_ ?_ t
      · intro a
        exact congrFun (prefix_word rule (prefBits z.val)) a
      · intro i
        change word rule (prefBits z.val) (Fin.natAdd f i) = _
        simp only [word, Fin.addCases_right]
        exact (suffix_unique rule (prefBits z.val) (fun j => z.val (Fin.natAdd f j)) z.property i).symm }
  refine ⟨e, ?_, ?_⟩
  · intro seed z
    change e.symm z = seed ↔ z = e seed
    exact e.symm_apply_eq
  · rw [← Nat.card_congr e]
    simp
