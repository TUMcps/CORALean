import CORALean.Specification.STL.Definitions.SampledTime
import CORALean.Specification.STL.Definitions.Pform
import Mathlib.Data.NNReal.Defs

/-!
# What a branch says of a trace

`Holds c b ξ`: `ξ` satisfies `X_c^j (φᵢⱼ ∨ ϱᵢⱼ)` of [1, Lemma 2], unfolded to the window `(jc, jc
+ c)` for the `F(0,c)` and `G(0,c)` and the point `jc` for `ϱᵢⱼ`.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ξ` satisfies the branch: `F(0,c)` or `G(0,c)` on the window, or `ϱᵢⱼ` at `jc`. -/
def STL.Branch.Holds (c : ℝ≥0) (b : STL.Branch X) (ξ : ℝ≥0 → X) : Prop :=
  ((∃ ϱ ∈ b.K, ∃ t, 0 < t ∧ t < c ∧ ϱ.Sat (ξ (t + b.j * c))) ∨
    ∃ ϱ ∈ b.L, ∀ t, 0 < t → t < c → ϱ.Sat (ξ (t + b.j * c))) ∨ b.ϱ.Sat (ξ (b.j * c))


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
