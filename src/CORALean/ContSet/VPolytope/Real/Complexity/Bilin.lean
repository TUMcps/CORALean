import CORALean.ContSet.VPolytope.Real.Operations.Bilin

/-!
# `VPolytope.bilin_k`

`bilin`'s vertex count: every vertex of `P` paired with every vertex of `Q`,
so the count is their product outright, not a sum plus a cross block the way
`Zonotope.bilin_h` is — a vertex description has no linear part to keep
separate from the pairing. `rfl`, since `Operations/Bilin.lean` states `k`
directly. `BilinBigO.lean` puts this in `O`-notation.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.bilin_k (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (P : VPolytope α) (Q : VPolytope β) :
    (VPolytope.bilin f P Q).k = P.k * Q.k := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
