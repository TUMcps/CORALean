module

public import CORALean.ContDynamics.NonlinearSys.Definitions.TunedStep
public import CORALean.ContDynamics.NonlinearSys.Operations.EstimateGainFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.OptDeltatFloat
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `Alg. 2`: tuning of the time step size Δt, in floats

`tuneDeltat` in `𝕋`. Tuning only: the value picks a step size, an order or a gain and no soundness
statement reads it, so every rounding is upward and no theorem is owed. What a run guarantees
holds for whatever this returns. See [1].

## Inputs
* `n` – dimension
* `prec` – precision
* `bis` – bisection depth
* `dabs` – box diameter of the abstraction error
* `rabs` – radius of the abstraction error
* `ζδ` – limit gain
* `ζΔ` – gain threshold
* `ζZ` – start-set constant
* `ζP` – second constant
* `r₀` – initial radius
* `φ1` – last step's gain
* `Δ` – last finite horizon
* `Δinit` – initial finite horizon
* `s` – step number
* `fuel` – bound for the search

## Output
* the float step size and the gain for the next step, or none

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `φ(Δt)` of eq. (25): the worst dimension's ratio of the two error widths. -/
def aux_gainMaxFloat {n : ℕ} (d dδ : Fin n → 𝕋) : 𝕋 :=
  (List.finRange n).foldl
    (fun φ i => if le φ (divUp (dδ i) (d i)) then divUp (dδ i) (d i) else φ) zero

/-- Lines 3-7: shrink `Δ` by `ζ_δ` until the gain it yields reaches `ζ_Δ`, and
`none` once `fuel` shrinkings have not. -/
def aux_tuneDeltatInitFloat {n : ℕ} (dabs : 𝕋 → Fin n → 𝕋) (ζδ ζΔ : 𝕋) :
    𝕋 → ℕ → Option (NonlinearSys.TunedStep 𝕋)
  | _, 0 => none
  | Δ, k + 1 =>
    let Δnext := mulUp ζδ Δ                                      -- 4. Δ ← ζ_δ Δ
    let dΔ := dabs Δnext                                         -- 5. d(box(R_abs(Δ)))
    let dδΔ := dabs (mulUp ζδ Δnext)                             -- 5. d(box(R_abs(ζ_δ Δ)))
    let φ1 := aux_gainMaxFloat dΔ dδΔ                                -- 6. φ₁ by (25)
    if le ζΔ φ1 then some ⟨Δnext, φ1⟩                            -- 3. while φ₁ < ζ_Δ
    else aux_tuneDeltatInitFloat dabs ζδ ζΔ Δnext k


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: the optimal time step size `Δt*` and the gain `φ₁` to hand the
next step, and `none` where the first step's search for `Δ` gave out. -/
def tuneDeltatFloat [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ} (prec bis : ℕ)
    (dabs : 𝕋 → Fin n → 𝕋) (rabs : 𝕋 → 𝕋) (ζδ ζΔ ζZ ζP r₀ φ1 Δ Δinit : 𝕋) (s fuel : ℕ) :
    Option (NonlinearSys.TunedStep 𝕋) :=
  -- 1. if s = 1 then
  if s = 1 then
    -- 2. initialize Δt
    let Δ₀ := Δinit
    -- 3.-7. the loop of (32)
    match aux_tuneDeltatInitFloat dabs ζδ ζΔ Δ₀ fuel with
    | none => none
    | some ⟨Δ₁, φ₁⟩ =>
      -- 8. Δt* by (31)
      let opt := optDeltatFloat prec bis ζδ ζZ ζP φ₁ r₀ (rabs Δ₁) Δ₁ fuel
      some ⟨opt.Δt, φ₁⟩
  -- 9. else
  else
    -- 10. Δ ← Δ(ζ_δ-ζ_Δ)/(ζ_δ-φ₁)
    let Δk := divUp (mulUp Δ (subUp ζδ ζΔ)) (subDown ζδ φ1)
    -- 11. R_abs(Δ), and r_abs,1
    let rabs1 := rabs Δk
    -- 12. Δt* by (31)
    let opt := optDeltatFloat prec bis ζδ ζZ ζP φ1 r₀ rabs1 Δk fuel
    -- 13. (29)'s r_abs,k, at Δt*
    let rabsk := rabs opt.Δt
    -- 13. φ₁ by (29)
    let φ₁ := estimateGainFloat ζδ (powUp (divUp one ζδ) opt.exponent)
      rabs1 rabsk opt.exponent fuel
    some ⟨opt.Δt, φ₁⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
