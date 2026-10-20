module

public import CORALean.ContDynamics.LinearSysDT.Definitions.BackReachSetExistsExact

@[expose] public section

/-!
# The `∃` step is a preimage of a Minkowski *sum*

`{x | ∃ u ∈ U, A x + u ∈ B}` written as `A ⁻¹' (B ⊕ (-U))`, which says the `∃` reading is computed
by `plus`. `backReachSetForallExact`'s step is the same preimage of `B ⊖ U`, and `⊖` is a
guarantee an implementation may only under-approximate while `⊕` is an enclosure it may
over-approximate, so the two readings do not need the same half of an operation. The preimage is
shared; the direction it is used in separates them: `backReachExists_outer` travels along a *left*
inverse with `mtimes_outer`, where `backReachForall_inner` travels along a right inverse and needs
an exact `mtimes`. Stated at the step rather than at the whole run.

## Inputs
* `sys` – system
* `T` – target set
* `U` – input set
* `k` – step

## Hypotheses
* none

## Conclusion
* the next set is the preimage of the sum with the negated input set
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.backReachSetExistsExact_preimage (sys : LinearSysDT 𝕋 n) (T U : S n)
    (k : ℕ) : -- --- CONCL ---
    sys.backReachSetExistsExact T U (k + 1) = mulVecLin (toRealMat sys.A) ⁻¹'
      (sys.backReachSetExistsExact T U k + -construct U) := by -- --- PROOF ---
  ext x
  constructor
  -- the chosen input, moved to the other side of the step
  · rintro ⟨u, hu, hx⟩
    refine ⟨_, hx, -u, Set.neg_mem_neg.mpr hu, ?_⟩
    show toRealMat sys.A *ᵥ x + u + -u = toRealMat sys.A *ᵥ x
    abel
  -- and back: the summand from `-U` is the input, negated
  · rintro ⟨y, hy, w, hw, hxy⟩
    refine ⟨-w, Set.mem_neg.mp hw, ?_⟩
    have : toRealMat sys.A *ᵥ x + -w = y := by
      rw [show toRealMat sys.A *ᵥ x = y + w from hxy.symm]; abel
    rwa [this]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
