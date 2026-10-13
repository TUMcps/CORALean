import CORALean.ContDynamics.LinearSys.Definitions.VerifyIterFloat
import CORALean.ContSet.HPolytope.Float.Instances
import CORALean.Specification.Specification

/-!
# The specification the float verification decides

`X` satisfies every safe set `G j` and every unsafe set `F j` of [1, Alg. 3], the sets stored as
float halfspace polytopes and read as the real sets they denote.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n r w : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `X` satisfies every safe set `G j` and every unsafe set `F j`. -/
def LinearSys.VerifySpecFloat (G : Fin (r + 1) → HPolytope 𝕋 (Vec 𝕋 n))
    (F : Fin (w + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (X : Set (Vec ℝ n)) : Prop :=
  (∀ j, (Specification.safeSet (G j)).Holds X) ∧ ∀ j, (Specification.unsafeSet (F j)).Holds X

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
