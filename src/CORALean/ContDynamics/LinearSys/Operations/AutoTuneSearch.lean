module

public import CORALean.ContDynamics.LinearSys.Operations.AutoTuneOrder

@[expose] public section

/-!
# `Alg. 2` lines 6-15: the step-size sweep

Halve `Δt` from the candidate line 5 doubled to, recomputing the two
admissible shares (eq. 37, eq. 38) at each new candidate, until
`autoTuneOrder` finds an `η`. Neither `Nat.find` nor `Classical.choose`: the
sweep goes through `le` and is a bounded recursion with an explicit `fuel` —
[1]'s own `Δt`-shrink has no stated bound either, so `Option` is what a
caller who runs out gets back.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 6-15: halve `Δt` from the candidate line 5 doubled to, recomputing the two admissible
shares (eq. 37, eq. 38) at each new candidate, until `autoTuneOrder` finds an `η`. -/
noncomputable def LinearSys.autoTuneSearch (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (H : Zonotope (Vec ℝ n)) (ũ : Vec ℝ n) (tk tend εmax ζ εaAcc : ℝ) (ηmax : ℕ)
    (U₀ : Zonotope (Vec ℝ n)) : ℝ → ℕ → Option (ℝ × ℕ)
  | _, 0 => none
  | Δt, k + 1 =>
    let Δt' := Δt / 2                                                       -- 7. Δt_k ← ½Δt_k
    let εaτ := (tk + Δt') / tend * (1 - ζ) * εmax - εaAcc                    -- 14. eq. (37),(36)
    let εnτ := εmax - (tk + Δt') / tend * ζ * εmax - εaAcc                   -- 14. eq. (38),(34)
    match LinearSys.autoTuneOrder sys le H ũ tk U₀ Δt' εaτ εnτ 2 ηmax with
    | some η => some (Δt', η)
    | none => LinearSys.autoTuneSearch sys le H ũ tk tend εmax ζ εaAcc ηmax U₀ Δt' k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
