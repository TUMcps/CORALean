import CORALean.ContDynamics.LinearSys.Operations.AutoTuneSearchFloat

/-!
# `Alg. 2` lines 5-15 in floats: the step size and order

`autoTuneDeltaT` computed in `𝕋`: `Δt_k` and `η_k`, or `none` where `fuel` halvings of
`2·Δt_{k-1}` did not suffice. The tuned pair enters `autoStepFloat`, which re-checks it before
use, so the step is sound at any pair this returns: no soundness theorem is owed.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] lines 5-15: `Δt_k`, `η_k`, or `none` where `fuel` halvings did not suffice. -/
def LinearSys.autoTuneDeltaTFloat (sys : LinearSys 𝕋 n) (eAtk : Interval (Mat 𝕋 n n))
    (H : Zonotope (Vec 𝕋 n)) (ũ : Vec 𝕋 n) (tk tend εmax ζ εaAcc : ℚ) (Δtprev : 𝕋) (ηmax fuel : ℕ)
    (U₀ : Zonotope (Vec 𝕋 n)) : Option (𝕋 × ℕ) :=
  let Δt₀ := addUp Δtprev Δtprev                                          -- 5. Δt_k ← 2Δt_{k-1}
  sys.autoTuneSearchFloat eAtk H ũ tk tend εmax ζ εaAcc ηmax U₀ Δt₀ fuel   -- 6.-15. the repeat

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
