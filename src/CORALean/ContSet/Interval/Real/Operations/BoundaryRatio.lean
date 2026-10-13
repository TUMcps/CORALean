module

public import CORALean.ContSet.Interval.Real.Operations.Radius
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
# `Interval.boundaryRatio`

The scalar of CORA's `@interval/boundaryPoint.m` (bounded case): with `I - startPoint` the box
about the start point, `d = 2 * rad(I)`, `bound = infimum(I) + d .* max(sign(dir), 0)` is the face
of the shifted box that `dir` points to in each coordinate (its supremum if `dir i > 0`, its
infimum otherwise), and `ratio = min(bound ./ dir)` over the coordinates with `dir i ≠ 0`.

The code also drops the infinite ratios (`ratio(~isinf(ratio))`) and sets the coordinates of an
unbounded `I` along `dir` to `Inf`: an interval of this library has real endpoints, so only the
bounded case arises. The non-emptiness and containment checks on `startPoint` and `dir` are
hypotheses of the theorems; here `dir ≠ 0` is what makes the minimum over a non-empty set.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Classical

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ratio` of `boundaryPoint(I, dir, startPoint)`, for a non-zero `dir`. -/
noncomputable def Interval.boundaryRatio (I : Interval (Vec ℝ n)) (dir start : Vec ℝ n)
    (hdir : ∃ i, dir i ≠ 0) : ℝ :=
  let d := fun i => 2 * Interval.radius I i
  let sgn := fun i => if 0 < dir i then (1 : ℝ) else 0
  let bound := fun i => (I.inf i - start i) + d i * sgn i
  (Finset.univ.filter fun i => dir i ≠ 0).inf'
    (by obtain ⟨i, hi⟩ := hdir; exact ⟨i, by simpa using hi⟩) fun i => bound i / dir i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
