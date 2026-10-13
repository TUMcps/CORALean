module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.OrderTestFloat

@[expose] public section

/-!
# `MatExp.stepTest`, the float test one candidate step passes

The test the step selector of [1] runs at one candidate `r`, at a float representation: `r`
positive, the scaled norm bound `r · nrm` meeting the side condition, and the contribution
`r · expRemainderBound (r · nrm) η` strictly under `ε`. `nrm` is a float upper bound of `‖A‖`.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The float test one candidate step passes at order `η`. -/
def MatExp.stepTest (nrm ε : 𝕋) (η : ℕ) (r : 𝕋) : Bool :=
  ltStrict zero r && le (mulUp r nrm) (half (nsmulDown (η + 2) one))
    && ltStrict (mulUp r (MatExp.expRemainderBound (mulUp r nrm) η)) ε

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
