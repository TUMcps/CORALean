module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBoundFloat

@[expose] public section

/-!
# `MatExp.orderTest`, the float test one order passes

The test the order selector of [1] runs at one candidate `η`, at a float representation: the side
condition `nrm ≤ (η + 2)/2` the float remainder bound needs (`le`, whose `true` is sound) and
the remainder bound `MatExp.expRemainderBound nrm η` strictly under `ε` (`ltStrict`, whose
`true` is sound). `nrm` is a float upper bound of the matrix's norm.

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

/-- The float test one order passes: the side condition `nrm ≤ (η + 2)/2` and the remainder
bound strictly under `ε`. -/
def MatExp.orderTest (nrm ε : 𝕋) (η : ℕ) : Bool :=
  le nrm (half (nsmulDown (η + 2) one)) && ltStrict (MatExp.expRemainderBound nrm η) ε

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
