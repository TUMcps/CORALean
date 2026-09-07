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


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.sum_univ_linComb {M : Type} [AddCommMonoid M] {cZ₁ cZ₂ : ConZonotope α}
    (f : Fin (cZ₁.h + cZ₂.h + 1) → M) :
    ∑ j : Fin (cZ₁.linComb cZ₂).h, f j
      = ∑ j, f (Fin.castAdd 1 j) + ∑ j, f (Fin.natAdd (cZ₁.h + cZ₂.h) j) :=
  Fin.sum_univ_add f

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
