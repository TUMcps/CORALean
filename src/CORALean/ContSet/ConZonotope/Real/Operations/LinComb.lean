module

public import CORALean.ContSet.ConZonotope.Real.Operations.Domain
public import CORALean.ContSet.HPolytope.Real.Operations.HalfScaled

@[expose] public section

/-!
# `ConZonotope.linComb`

The convex hull of the two sets, and exact between two nonempty ones. One fresh
coefficient carries the interpolation parameter, the generator blocks are
concatenated, and each block's coefficients answer to its own constraints *at
the weight the parameter names* — `λ` for the first block and `1 - λ` for the
second, which is `halfScaled` at `t` and at `-t`.

Scaling `domain` rather than `P` is what carries the unit box along with the
constraints: `|βⱼ| ≤ λ` is what makes a block collapse as its weight vanishes,
and without it the hull would be the enclosing zonotope's again.

The blocks are not paired the way a zonotope's are: pairing merges two
coefficients into one, and each block's constraints have to read them apart.

`[1, Thm. 5]` spends `2(h₁ + h₂)` slack coefficients stating `|βⱼ| ≤ λ` as an
equality, which a halfspace description states directly, so the count here is
`h₁ + h₂ + 1`.

## References

* [1] V. Raghuraman and J. P. Koeln. "Set operations and order reductions for
      constrained zonotopes". Automatica, 139:110204, 2022. arXiv:2009.06039.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ConZonotope.linComb (cZ₁ cZ₂ : ConZonotope α) : ConZonotope α where
  h := cZ₁.h + cZ₂.h + 1
  c := (2:ℝ)⁻¹ • (cZ₁.c + cZ₂.c)
  G := Fin.append (Fin.append cZ₁.G cZ₂.G) fun _ : Fin 1 => (2:ℝ)⁻¹ • (cZ₁.c - cZ₂.c)
  P :=
    ((cZ₁.domain.comap ((blockLeft cZ₁.h cZ₂.h).comp (blockLeft (cZ₁.h + cZ₂.h) 1))).halfScaled
        (blockLast (cZ₁.h + cZ₂.h))).intersection
      ((cZ₂.domain.comap ((blockRight cZ₁.h cZ₂.h).comp (blockLeft (cZ₁.h + cZ₂.h) 1))).halfScaled
        (-blockLast (cZ₁.h + cZ₂.h)))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
