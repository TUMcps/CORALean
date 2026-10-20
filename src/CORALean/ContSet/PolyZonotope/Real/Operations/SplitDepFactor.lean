module

public import CORALean.ContSet.PolyZonotope.Real.Operations.GetSubset

@[expose] public section

/-!
# `PolyZonotope.splitDepFactor`

CORA's `@polyZonotope/splitDepFactor`: halve the domain of one dependent factor, `αₖ ∈ [-1, 0]`
and `αₖ ∈ [0, 1]`, and re-express each half over `[-1, 1]` by substituting `αₖ ↦ (αₖ ∓ 1) / 2`.
That substitution is `getSubset` at center `∓1/2` and radius `1/2`; the denoted sets are the
same, and what differs is the order and merging of the generators CORA's closed form emits.
CORA's optional `polyOrd` argument is not modelled: the default is the largest exponent. A
pair, as CORA returns both halves at once. Factor `k` is a position, CORA's `id` an identifier.

## Inputs
* `pZ` – polynomial zonotope
* `k` – factor index

## Output
* pair of polynomial zonotopes for the two halves of that factor
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The halves `αₖ ∈ [-1, 0]` and `αₖ ∈ [0, 1]` of `pZ`, each over the full factor domain. -/
noncomputable def PolyZonotope.splitDepFactor (pZ : PolyZonotope α) (k : Fin pZ.p) :
    PolyZonotope α × PolyZonotope α :=
  (pZ.getSubset k (-(2 : ℝ)⁻¹) (2 : ℝ)⁻¹, pZ.getSubset k (2 : ℝ)⁻¹ (2 : ℝ)⁻¹)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
