module

public import CORALean.ContSet.Taylm.Float.Operations.AccumTerms
public import CORALean.ContSet.Taylm.Float.Theorems.AccumTermLe

@[expose] public section

/-!
# `Taylm.accumTerms` adds the terms up to its bound

## Inputs
* `L` – term list
* `M` – terms to add
* `t` – point of the box

## Hypotheses
* `ht` – `t` lies in the box `[-1, 1]ⁿ`

## Conclusion
* the polynomial of the result is that of `L` plus that of `M`, up to the bound returned
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The fold from any start: the bound grows by at least what each term costs. -/
private theorem Taylm.aux_foldl
    (F : List (𝕋 × (Fin n → ℕ)) × 𝕋 → 𝕋 × (Fin n → ℕ) → List (𝕋 × (Fin n → ℕ)) × 𝕋)
    (hF : ∀ acc a, F acc a = ((Taylm.accumTerm acc.1 a.1 a.2).1,
      addUp acc.2 (Taylm.accumTerm acc.1 a.1 a.2).2))
    (M L : List (𝕋 × (Fin n → ℕ))) (ε : 𝕋) {t : Vec ℝ n}
    (ht : t ∈ Real.Taylm.box n) : -- --- CONCL ---
    |Real.Taylm.polyOf ((M.foldl F (L, ε)).1.map fun a => (toReal a.1, a.2)) t
        - Real.Taylm.polyOf (L.map fun a => (toReal a.1, a.2)) t
        - Real.Taylm.polyOf (M.map fun a => (toReal a.1, a.2)) t| + toReal ε
      ≤ toReal (M.foldl F (L, ε)).2 := by -- --- PROOF ---
  induction M generalizing L ε with
  | nil => simp
  | cons a M ih =>
    set r := Taylm.accumTerm L a.1 a.2
    have hr := Taylm.accumTerm_le L a.1 a.2 ht
    have hε := add_le_addUp ε r.2
    have hi := ih r.1 (addUp ε r.2)
    rw [List.foldl_cons, hF] at *
    simp only [List.map_cons, Real.Taylm.polyOf_cons] at hi ⊢
    -- the error of this term and the error of the rest, by the triangle inequality
    set R := Real.Taylm.polyOf ((M.foldl F (r.1, addUp ε r.2)).1.map fun a => (toReal a.1, a.2)) t
    set P := Real.Taylm.polyOf (r.1.map fun a => (toReal a.1, a.2)) t
    have htri := abs_add_le (R - P - Real.Taylm.polyOf (M.map fun a => (toReal a.1, a.2)) t)
      (P - Real.Taylm.polyOf (L.map fun a => (toReal a.1, a.2)) t
        - toReal a.1 * Real.Taylm.monomial a.2 t)
    have e : ∀ x y z w v : ℝ, x - y - z + (y - w - v) = x - w - (v + z) := by intros; ring
    rw [e] at htri
    linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.accumTerms_le (L M : List (𝕋 × (Fin n → ℕ))) {t : Vec ℝ n}
    (ht : t ∈ Real.Taylm.box n) : -- --- CONCL ---
    |Real.Taylm.polyOf ((Taylm.accumTerms L M).1.map fun a => (toReal a.1, a.2)) t
        - Real.Taylm.polyOf (L.map fun a => (toReal a.1, a.2)) t
        - Real.Taylm.polyOf (M.map fun a => (toReal a.1, a.2)) t|
      ≤ toReal (Taylm.accumTerms L M).2 := by -- --- PROOF ---
  have := Taylm.aux_foldl _ (fun _ _ => rfl) M L zero ht
  rw [toReal_zero, add_zero] at this
  exact this

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
