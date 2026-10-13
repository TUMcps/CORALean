import CORALean.ContDynamics.LinearSys.Operations.AutoTuneOrderFloat

/-!
# `Alg. 2` lines 6-15 in floats: the step-size search

[1, Alg. 2]'s `autoTuneSearch` computed in `𝕋`: halve `Δt` from the candidate line 5 doubled to,
recomputing the two admissible shares (eq. 37, eq. 38) at each new candidate in ℚ, until
`autoTuneOrderFloat` finds an `η`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 6-15: halve `Δt` until `autoTuneOrderFloat` finds an `η`, `none` after `fuel`
halvings without one. -/
def LinearSys.autoTuneSearchFloat (sys : LinearSys 𝕋 n) (eAtk : Interval (Mat 𝕋 n n))
    (H : Zonotope (Vec 𝕋 n)) (ũ : Vec 𝕋 n) (tk tend εmax ζ εaAcc : ℚ) (ηmax : ℕ)
    (U₀ : Zonotope (Vec 𝕋 n)) : 𝕋 → ℕ → Option (𝕋 × ℕ)
  | _, 0 => none
  | Δt, k + 1 =>
    let Δt' := half Δt                                                      -- 7. Δt_k ← ½Δt_k
    let t1 := tk + ToRat.toRat Δt'                                          -- t_{k+1}
    let εaτ := t1 / tend * (1 - ζ) * εmax - εaAcc                           -- 14. eq. (37),(36)
    let εnτ := εmax - t1 / tend * ζ * εmax - εaAcc                          -- 14. eq. (38),(34)
    match sys.autoTuneOrderFloat eAtk H ũ U₀ Δt' εaτ εnτ 2 ηmax with
    | some η => some (Δt', η)
    | none => sys.autoTuneSearchFloat eAtk H ũ tk tend εmax ζ εaAcc ηmax U₀ Δt' k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
