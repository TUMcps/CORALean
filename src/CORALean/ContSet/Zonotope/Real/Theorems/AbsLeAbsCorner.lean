module

public import CORALean.ContSet.Zonotope.Real.Operations.Abs
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsLeAbsBound
public import Mathlib.Algebra.BigOperators.Pi

@[expose] public section

/-!
# What `Zonotope.abs` keeps of its input

`abs` is not an enclosure: the zonotope with generators `(1, 1)` and `(1, -1)` contains
`(2, 0)`, whose entrywise absolute value is not on the segment `abs` leaves. What it keeps is the
box corner: the vertex `|c| + Σ |gⱼ|` of `abs Z` (all coefficients `1`) bounds every point's
entrywise absolute value, and `abs` is idempotent and has the same corner.

## Inputs
* `Z` – zonotope
* `x` – point
* `i` – coordinate

## Hypotheses
* `hx` – `x` lies in `Z`

## Conclusion
* coordinate `i` of `x` is below the corner of `abs Z`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point of `Z` has entrywise absolute value below the corner of `abs Z`. -/
theorem Zonotope.abs_le_abs_corner {Z : Zonotope (Vec ℝ n)} {x : Vec ℝ n}
    (hx : x ∈ Z.construct) (i : Fin n) : |x i| ≤ Z.abs.absBound i := by -- --- PROOF ---
  obtain ⟨β, hβ, hxβ⟩ := hx
  have h := Zonotope.abs_le_absBound (Z := Z) (x := x) (β := β) hβ
    (fun i => by rw [hxβ]; simp [Finset.sum_apply, mul_comm]) i
  refine h.trans (le_of_eq ?_)
  simp [Zonotope.abs, Zonotope.absBound]; rfl


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
