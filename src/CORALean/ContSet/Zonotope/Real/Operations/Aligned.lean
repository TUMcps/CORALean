import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.aligned`

[1, Def. 1]: a zonotope *aligned* with `Z` has `Z`'s generators, each scaled by its own
`αᵢ`, around a centre of its own, `([α₁g₁, …, α_N g_N], c)`. Both of [1]'s optimization
problems, (min-out) and (max-in), search over these; the definition asks `αᵢ ∈ [0, 1]`,
which is a hypothesis of the theorems here rather than a field.

## References

* [1] L. Yang and N. Ozay. "Scalable zonotopic under-approximation of backward
      reachable sets for uncertain linear systems". IEEE Control Systems Letters,
      6:1555-1560, 2022.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Def. 1]: `Z`'s generators scaled by `a`, around the centre `c`. -/
def Zonotope.aligned (Z : Zonotope α) (c : α) (a : Fin Z.h → ℝ) : Zonotope α where
  h := Z.h
  c := c
  G := fun i => a i • Z.G i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
