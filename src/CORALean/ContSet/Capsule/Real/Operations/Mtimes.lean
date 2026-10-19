module

public import CORALean.ContSet.Capsule.Real.Capsule
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `Capsule.mtimes`

CORA's `@capsule/mtimes.m` maps the center and the generator, `M c` and `M g`, and rescales the
radius. The image of a ball under `M` is an ellipsoid, so the result is an enclosure: the radius is
multiplied by the Frobenius norm `sqrt (∑ᵢⱼ Mᵢⱼ²)`, which is at least the largest singular value and
needs no eigenvalue computation.

CORA scales by `max(eig(M Mᵀ))`, the *square* of the largest singular value, which is too small
whenever that value is under `1`; see `Capsule.mtimes_cora_counterexample` and
`references/coverage/contSet/capsule.md`, row `mtimes`.

## Inputs
* `M` – matrix
* `C` – capsule

## Output
* capsule enclosing `M * C`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Center and generator multiplied by `M`, the radius by the Frobenius norm of `M`, an upper
bound of its operator norm. -/
noncomputable def Capsule.mtimes (M : Mat ℝ m n) (C : Capsule n) : Capsule m :=
  let σ := Real.sqrt (∑ i, ∑ j, M i j ^ 2)
  ⟨M.mulVec C.c, M.mulVec C.g, C.r * σ⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
