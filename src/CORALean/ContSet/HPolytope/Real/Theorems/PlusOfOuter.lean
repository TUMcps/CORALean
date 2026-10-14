module

public import CORALean.ContSet.HPolytope.Real.Operations.Plus
public import CORALean.ContSet.HPolytope.Real.Operations.Basic

@[expose] public section

/-!
# The certified Minkowski sum encloses

One line: `plusOf` is `ofBounds` over directions the caller chose, `ofBounds`
states exactly what its certificates say, and the certificates were composed to
speak about the sum. The work is in `Global.LinProg`, and none of it is repeated
here.

Not exact, and the loss is not in the proof but in the choice of directions —
which is the caller's, and a precision knob rather than a correctness one.

[1, Prop. 4] is the instance at `rows`: `P ⊕ Z` stays inside `P`'s own
halfspaces with each offset raised by `Z`'s support value.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation".
      arXiv:2310.19083, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]
variable {q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.plusOf_outer {P₁ P₂ : HPolytope α} (Aq : Fin q → (α →ₗ[ℝ] ℝ))
    (u₁ : ∀ i, SupportBound P₁.construct (Aq i))
    (u₂ : ∀ i, SupportBound P₂.construct (Aq i)) :
    P₁.construct + P₂.construct ⊆ (HPolytope.plusOf Aq u₁ u₂).construct :=
  HPolytope.subset_ofBounds _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
