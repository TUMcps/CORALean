module

public import CORALean.ContSet.Taylm.Real.Operations.PolyBounds
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Taylm.Real.Operations.TermBounds
public import CORALean.ContSet.Taylm.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.Taylm.Real.Theorems.Basic

@[expose] public section

/-!
# A term list stays in `polyBounds` on the box

## Inputs
* `L` – terms of the polynomial
* `t` – point

## Hypotheses
* `ht` – point lies in the unit box

## Conclusion
* the polynomial's value lies in its bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One term stays in `termBounds` on the box. -/
theorem Taylm.aux_termBounds_mem (a : ℝ × (Fin n → ℕ)) {t : Vec ℝ n}
    (ht : t ∈ Taylm.box n) : -- --- CONCL ---
    (Taylm.termBounds a).inf ≤ a.1 * Taylm.monomial a.2 t ∧
      a.1 * Taylm.monomial a.2 t ≤ (Taylm.termBounds a).sup := by -- --- PROOF ---
  have hm := abs_le.1 (Taylm.abs_monomial_le_one ht a.2)
  unfold Taylm.termBounds
  split_ifs with h0 hev
  · -- degree zero: every exponent is zero, the monomial is one
    have : a.2 = 0 := funext fun k => (Finset.sum_eq_zero_iff.1 h0) k (Finset.mem_univ k)
    simp [this, Taylm.monomial_zero]
  · -- all even: the monomial is in `[0, 1]`
    have hnn : 0 ≤ Taylm.monomial a.2 t :=
      Finset.prod_nonneg fun k _ => (hev k).pow_nonneg _
    constructor
    · rcases le_total a.1 0 with ha | ha
      · rw [min_eq_left ha]; nlinarith
      · rw [min_eq_right ha]; exact mul_nonneg ha hnn
    · rcases le_total a.1 0 with ha | ha
      · rw [max_eq_right ha]; exact mul_nonpos_of_nonpos_of_nonneg ha hnn
      · rw [max_eq_left ha]; nlinarith
  · -- otherwise only `|monomial| ≤ 1` is known
    have := abs_le.1 (show |a.1 * Taylm.monomial a.2 t| ≤ |a.1| by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Taylm.abs_monomial_le_one ht _))
    exact ⟨this.1, this.2⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.polyBounds_mem (L : List (ℝ × (Fin n → ℕ))) {t : Vec ℝ n}
    (ht : t ∈ Taylm.box n) : -- --- CONCL ---
    (Taylm.polyBounds L).inf ≤ Taylm.polyOf L t ∧
      Taylm.polyOf L t ≤ (Taylm.polyBounds L).sup := by -- --- PROOF ---
  induction L with
  | nil => simp [Taylm.polyBounds]
  | cons a L ih =>
    have := Taylm.aux_termBounds_mem a ht
    simp only [Taylm.polyBounds, List.map_cons, List.sum_cons, Taylm.polyOf_cons] at *
    constructor <;> linarith [ih.1, ih.2, this.1, this.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
