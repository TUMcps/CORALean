module

public import CORALean.ContSet.Taylm.Real.Operations.QuadTerms
public import CORALean.ContSet.Taylm.Real.Theorems.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.MonomialSingle
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfAppend
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The quadratic form's terms evaluate to it

Exactly: the double sum is `t ⬝ H t / 2`, the linear terms `-(t ⬝ H x₀ + x₀ ⬝ H t)/2`, and the
constant `x₀ ⬝ H x₀ / 2`.

## Inputs
* `H` – Hessian matrix
* `x0` – expansion point
* `t` – point

## Hypotheses
* none

## Conclusion
* the quadratic form's terms evaluate to the quadratic form
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.polyOf_quadTerms (H : Mat ℝ n n) (x0 t : Vec ℝ n) :
    Taylm.polyOf (Taylm.quadTerms H x0) t = (t - x0) ⬝ᵥ (H *ᵥ (t - x0)) / 2 := by -- --- PROOF ---
  have hflat : ∀ LL : List (List (ℝ × (Fin n → ℕ))),
      Taylm.polyOf LL.flatten t = (LL.map fun L => Taylm.polyOf L t).sum := by
    intro LL
    induction LL with
    | nil => simp
    | cons L LL ih => simp [Taylm.polyOf_append, ih]
  rw [Taylm.quadTerms, Taylm.polyOf_append, Taylm.polyOf_append, hflat, List.map_ofFn,
    List.sum_ofFn, Taylm.polyOf_ofFn]
  simp only [Function.comp_def, Taylm.polyOf_ofFn, Taylm.polyOf_cons, Taylm.polyOf_nil,
    Taylm.monomial_zero, Taylm.monomial_add, Taylm.monomial_single, add_zero, mul_one]
  -- the three parts in matrix form
  have h2 : ∑ i, ∑ j, H i j / 2 * (t i * t j) = t ⬝ᵥ (H *ᵥ t) / 2 := by
    simp only [dotProduct, mulVec, Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h1 : ∑ i, -((H *ᵥ x0) i + (Hᵀ *ᵥ x0) i) / 2 * t i
      = -(t ⬝ᵥ (H *ᵥ x0) + x0 ⬝ᵥ (H *ᵥ t)) / 2 := by
    have : x0 ⬝ᵥ (H *ᵥ t) = t ⬝ᵥ (Hᵀ *ᵥ x0) := by
      rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
    rw [this]
    simp only [dotProduct, ← Finset.sum_add_distrib, neg_div, Finset.sum_div,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2, h1]
  simp only [sub_dotProduct, dotProduct_sub, mulVec_sub]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
