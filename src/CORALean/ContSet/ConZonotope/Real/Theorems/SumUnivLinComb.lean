import CORALean.ContSet.ConZonotope.Real.Operations.LinComb

/-!
# Splitting a sum over `linComb`'s generators

`Fin.sum_univ_add` at this operation's generator count, stated through the
projection because that is the form a goal about the result has, and simp will
not rewrite a binder's type. Both directions of the guarantee sum over the
result, so it is not file-local to either.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

theorem ConZonotope.sum_univ_linComb {M : Type} [AddCommMonoid M] {C₁ C₂ : ConZonotope α}
    (f : Fin (C₁.h + C₂.h + 1) → M) :
    ∑ j : Fin (C₁.linComb C₂).h, f j
      = ∑ j, f (Fin.castAdd 1 j) + ∑ j, f (Fin.natAdd (C₁.h + C₂.h) j) :=
  Fin.sum_univ_add f

end CORALean.Real
