module

public import CORALean.ContSet.PolyZonotope.Real.Operations.ExactPlus
public import CORALean.ContSet.PolyZonotope.Real.Operations.Merge
public import CORALean.ContSet.PolyZonotope.Real.Operations.Sort

@[expose] public section

/-!
# `PolyZonotope.sortPlus`

[1, Prop. 3.4]: the sum over one factor list, written down once rather than built up. The
two exponent matrices are laid side by side (`exactPlus`), the columns put back in order
(`sort`), and the shared columns joined (`merge`), which is [1]'s `merge ⟨ĉ, Ĝ(·,K), [], Ê(·,K)⟩`.
[1] takes `m` sorted operands, so that sorting is an `m`-way merge of runs, `O(p ĥ log m)`.
Neither is a hypothesis of the result: `m` operands are this iterated, and the set does not
depend on how the sorting permutation was found.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Hypotheses
* `hp` – both have the same factor count

## Output
* sorted and merged sum

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The sum over a shared factor list, sorted and with shared columns joined. -/
noncomputable def PolyZonotope.sortPlus (pZ₁ pZ₂ : PolyZonotope α) (hp : pZ₁.p = pZ₂.p) :
    PolyZonotope α :=
  (pZ₁.exactPlus pZ₂ hp).sort.merge

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
