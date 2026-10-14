module

public import CORALean.ContDynamics.NonlinearSys.Operations.EstimateGainFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.OptDeltatFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.TuneDeltatInitFloat

@[expose] public section

/-!
# `Alg. 2`: tuning of the time step size Δt, in floats

`tuneDeltat` in `𝕋`. Tuning only: the value picks a step size, an order or a gain and no soundness
statement reads it, so every rounding is upward and no theorem is owed. What a run guarantees
holds for whatever this returns. See [1].

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: the optimal time step size `Δt*` and the gain `φ₁` to hand the
next step, and `none` where the first step's search for `Δ` gave out. -/
def tuneDeltatFloat [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ} (prec bis : ℕ)
    (dabs : 𝕋 → Fin n → 𝕋) (rabs : 𝕋 → 𝕋) (ζδ ζΔ ζZ ζP r₀ φ1 Δ Δinit : 𝕋) (s fuel : ℕ) :
    Option (NonlinearSys.TunedStep 𝕋) :=
  if s = 1 then                                                  -- 1. if s = 1 then
    let Δ₀ := Δinit                                              -- 2. initialize Δt
    match tuneDeltatInitFloat dabs ζδ ζΔ Δ₀ fuel with            -- 3.-7. the loop of (32)
    | none => none
    | some ⟨Δ₁, φ₁⟩ =>
      let opt := optDeltatFloat prec bis ζδ ζZ ζP φ₁ r₀ (rabs Δ₁) Δ₁ fuel  -- 8. Δt* by (31)
      some ⟨opt.Δt, φ₁⟩
  else                                                           -- 9. else
    let Δk := divUp (mulUp Δ (subUp ζδ ζΔ)) (subDown ζδ φ1)     -- 10. Δ ← Δ(ζ_δ-ζ_Δ)/(ζ_δ-φ₁)
    let rabs1 := rabs Δk                                         -- 11. R_abs(Δ), and r_abs,1
    let opt := optDeltatFloat prec bis ζδ ζZ ζP φ1 r₀ rabs1 Δk fuel  -- 12. Δt* by (31)
    let rabsk := rabs opt.Δt                                      -- 13. (29)'s r_abs,k, at Δt*
    let φ₁ := estimateGainFloat ζδ (powUp (divUp one ζδ) opt.exponent)  -- 13. φ₁ by (29)
      rabs1 rabsk opt.exponent fuel
    some ⟨opt.Δt, φ₁⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
