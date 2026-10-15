module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.ShapeOfShape
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The printed image description of an ellipse omits the center

[1, Sec. 1.1 (ellipse)] defines
`E(E, s) := {x | (x − s)ᵀ E⁻¹ (x − s) ≤ 1} = {E^(1/2)(x − s) | ‖x‖ ≤ 1}`.
The second set is the unit ball mapped by `x ↦ E^(1/2)(x − s)`, centered at `−E^(1/2) s`,
not at `s`: it is `{s + E^(1/2) x | ‖x‖ ≤ 1}` that equals the first (`mem_ofShape_iff`).
For `n = 1`, `E = 1`, `s = 2` the first set is `[1, 3]` and the second `[−3, −1]`; `3` is in
the first only.

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
open scoped MatrixOrder


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 1.1 (ellipse)]: the printed image form of `E(E, s)` fails at `E = 1`, `s = 2`. -/
theorem Ellipsoid.printed_ellipse_image_counterexample :
    ∃ (Q : Mat ℝ 1 1) (s : Vec ℝ 1), Q.PosDef ∧
      {x : Vec ℝ 1 | (x - s) ⬝ᵥ Q⁻¹ *ᵥ (x - s) ≤ 1}
        ≠ (fun x => (CFC.sqrt Q : Mat ℝ 1 1) *ᵥ (x - s)) ''
          {x : Vec ℝ 1 | ‖x‖₂ ≤ 1} := by -- --- PROOF ---
  refine ⟨1, fun _ => 2, Matrix.PosDef.one, fun h => ?_⟩
  -- the point `3` is in the first set and not in the second
  have h3 : (fun _ => 3 : Vec ℝ 1) ∈ {x : Vec ℝ 1 | (x - fun _ => 2) ⬝ᵥ (1 : Mat ℝ 1 1)⁻¹ *ᵥ
      (x - fun _ => 2) ≤ 1} := by
    simp [dotProduct]
    norm_num
  rw [h] at h3
  obtain ⟨x, hx, hx3⟩ := h3
  have hxx : x 0 = 5 := by
    have := congrFun hx3 0
    simp [CFC.sqrt_one] at this
    linarith
  have : ‖x‖₂ = 5 := by
    simp [norm₂, hxx]
  rw [Set.mem_setOf_eq, this] at hx
  norm_num at hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
