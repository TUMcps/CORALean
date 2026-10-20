module

public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.Global.EuclideanNorm
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A ball lies in an H-polytope of unit rows iff its radius is below every offset

[1, Eq. 6]: with unit normals `‖aᵢ‖₂ = 1`, the ball `B_r` of radius `r ≥ 0` around the origin
lies in `{x | aᵢᵀx ≤ bᵢ}` iff `bᵢ ≥ r` for every `i`. If so, Cauchy-Schwarz gives
`aᵢᵀx ≤ ‖x‖₂ ≤ r ≤ bᵢ`; if some `bᵢ < r`, the point `r aᵢ` of the ball violates the `i`-th
inequality. So Goffin's test [1, Eq. 5] of whether the shrunken ball `B'` lies in the polyhedron
is the check that `bᵢ ≥ 1/(n√(1+ε))` for all `i`, and a failure names the violated inequality.

## Inputs
* `A` – `q × n` matrix
* `b` – offset vector of length `q`
* `r` – radius

## Hypotheses
* `hA` – `∀ i, ‖A i‖₂ = 1`
* `hr` – `0 ≤ r`

## Conclusion
* [1, Eq. 6]: `B_r ⊆ {A x ≤ b}` iff `r ≤ bᵢ` for every `i`, for unit rows

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {q n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 6]: `B_r ⊆ {A x ≤ b}` iff `r ≤ bᵢ` for every `i`, for unit rows. -/
theorem HPolytope.ball_subset_ineqs_iff (A : Mat ℝ q n) (b : Vec ℝ q) (hA : ∀ i, ‖A i‖₂ = 1)
    {r : ℝ} (hr : 0 ≤ r) :
    (∀ x : Vec ℝ n, ‖x‖₂ ≤ r → x ∈ (HPolytope.ineqs A b).construct)
      ↔ ∀ i, r ≤ b i := by -- --- PROOF ---
  constructor
  · -- the ball point `r aᵢ` meets the `i`-th inequality with equality
    intro h i
    have hmem := HPolytope.mem_ineqs_iff.mp (h (r • A i) (by
      rw [norm₂_smul, hA i, mul_one, abs_of_nonneg hr])) i
    have : (A *ᵥ (r • A i)) i = r * ‖A i‖₂ ^ 2 := by
      show A i ⬝ᵥ (r • A i) = _
      rw [dotProduct_smul, dotProduct_self, smul_eq_mul]
    rw [this, hA i] at hmem
    simpa using hmem
  · -- Cauchy-Schwarz against each unit row
    intro h x hx
    refine HPolytope.mem_ineqs_iff.mpr fun i => ?_
    calc (A *ᵥ x) i = A i ⬝ᵥ x := rfl
      _ ≤ ‖A i‖₂ * ‖x‖₂ := dotProduct_le_norm₂_mul_norm₂ _ _
      _ = ‖x‖₂ := by rw [hA i, one_mul]
      _ ≤ r := hx
      _ ≤ b i := h i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
