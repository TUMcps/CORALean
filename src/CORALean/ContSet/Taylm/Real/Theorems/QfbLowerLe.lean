module

public import CORALean.ContSet.Taylm.Real.Operations.QfbLower
public import CORALean.ContSet.Taylm.Real.Theorems.BoundsMem
public import CORALean.ContSet.Taylm.Real.Theorems.MinusOuter
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Taylm.Real.Theorems.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.MonomialSingle
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfAppend
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.Ring
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# The quadratic fast bounder is a lower bound

[1, Sec. 3]: for a positive semidefinite `H` and any `x₀`, `Q_{x₀} ≥ 0`, so a lower bound of
`f - Q_{x₀}`, which `T - Q_{x₀}` encloses, is one of `f`.

## Inputs
* `T` – Taylor model
* `f` – enclosed function
* `H` – Hessian matrix
* `x0` – expansion point
* `t` – point

## Hypotheses
* `h` – the model encloses the function
* `hH` – the Hessian is positive semidefinite
* `ht` – point lies in the unit box

## Conclusion
* the quadratic fast bound is at most the function's value

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range Bounders".
      2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The quadratic form's terms evaluate to it. -/
private theorem Taylm.aux_polyOf_quadTerms (H : Mat ℝ n n) (x0 t : Vec ℝ n) : -- --- CONCL ---
    Taylm.polyOf (Taylm.quadTerms H x0) t
      = (t - x0) ⬝ᵥ (H *ᵥ (t - x0)) / 2 := by -- --- PROOF ---
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.qfbLower_le {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) {H : Mat ℝ n n}
    (hH : H.PosSemidef) (x0 : Vec ℝ n) {t : Vec ℝ n} (ht : t ∈ Taylm.box n) : -- --- CONCL ---
    T.qfbLower H x0 ≤ f t := by -- --- PROOF ---
  have hQ : (Taylm.aux_quadForm H x0 T.maxOrder).Encloses
      fun t => (t - x0) ⬝ᵥ (H *ᵥ (t - x0)) / 2 := by
    intro t _
    simp [Taylm.aux_quadForm, Taylm.poly, Taylm.aux_polyOf_quadTerms]
  have hb := Taylm.bounds_mem (Taylm.minus_outer h hQ) ht
  have hq : 0 ≤ (t - x0) ⬝ᵥ (H *ᵥ (t - x0)) / 2 := by
    have := Matrix.PosSemidef.dotProduct_mulVec_nonneg hH (t - x0)
    simp only [star_trivial] at this
    positivity
  simp only [Taylm.qfbLower]
  linarith [hb.1]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
