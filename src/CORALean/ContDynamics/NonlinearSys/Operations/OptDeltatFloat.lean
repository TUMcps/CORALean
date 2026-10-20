module

public import CORALean.ContDynamics.NonlinearSys.Definitions.OptStep
public import CORALean.ContDynamics.NonlinearSys.Operations.InterpGainFloat
public import CORALean.Global.Float.FloatOps
public import CORALean.Global.Float.Log
public import CORALean.Global.Float.PowUp
public import CORALean.Global.Float.ToRat

@[expose] public section

/-!
# `optDeltat`: the time step size that balances the two wrapping effects, in floats

`optDeltat` in `𝕋`. Tuning only: the value picks a step size, an order or a gain and no soundness
statement reads it, so every rounding is upward and no theorem is owed. What a run guarantees
holds for whatever this returns. See [1].

## Inputs
* `prec` – precision
* `bis` – bisection depth
* `ζδ` – limit gain
* `ζZ` – start-set constant
* `ζA` – matrix constant
* `φ1` – gain at the horizon
* `r₀` – initial radius
* `rabs` – abstraction radius
* `h` – finite horizon
* `fuel` – bound for the search

## Output
* the float step size and its scaling index

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

/-- Increase `λ'` while the estimate keeps falling, and stop at the first
increase — [1]'s own evaluation of eq. (58). -/
def aux_optDeltatSearchFloat (cost : ℕ → 𝕋) : ℕ → ℕ → ℕ
  | s, 0 => s
  | s, k + 1 => if le (cost (s + 1)) (cost s) then aux_optDeltatSearchFloat cost (s + 1) k else s

/-- Eq. (57): the size `R(t)` is estimated to reach after the finite horizon,
walked in `λ = ζ_δ^{-λ'}` steps. -/
def aux_reachSizeEstimateFloat [SoundFloatArithmetic 𝕋] [ToRat 𝕋] (prec bis : ℕ)
    (ζδ ζZ ζA φ1 r₀ rabs : 𝕋) (scalings : ℕ) : 𝕋 :=
  let rpow := fun (x y : 𝕋) => expUp prec (mulUp y (logUp prec bis x))  -- x ^ y for x > 0
  let lam := powUp (divUp one ζδ) scalings                       -- λ = ζ_δ^{-λ'}
  let N := ⌊ToRat.toRat lam⌋₊                                    -- ⌊λ⌋ whole steps
  let b := subUp lam (nsmulUp N one)                             -- the last incomplete step
  let base := addUp one (addUp ζZ ζZ)                            -- 1 + 2 ζ_Z
  let ζAZ := addUp (sumUp fun (j : Fin N) =>                     -- 53. ζ_{A,Z}(λ)
      let e := addUp b (nsmulUp (j + 1) one)                     -- b + j, j = 1, …, N
      mulUp (rpow base e) (rpow ζA (divUp (subUp e one) lam)))
    (mulUp b (rpow base b))
  let growth := mulUp (mulUp r₀ (rpow base lam)) ζA              -- 57. the start set, propagated
  let gain := (List.range scalings).foldl                        -- 57. ∏ φ(j+1)
    (fun p j => mulUp p (interpGainFloat ζδ φ1 j)) one
  addUp growth (mulUp (mulUp (divUp rabs lam) ζAZ) gain)         -- 57. errors, accumulated


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] line 10: eq. (58)'s optimal time step size, and the `λ'` it was
found at. -/
def optDeltatFloat [SoundFloatArithmetic 𝕋] [ToRat 𝕋] (prec bis : ℕ)
    (ζδ ζZ ζA φ1 r₀ rabs h : 𝕋) (fuel : ℕ) :
    NonlinearSys.OptStep 𝕋 :=
  -- 10. eq. (57): the cost function
  let cost := aux_reachSizeEstimateFloat prec bis ζδ ζZ ζA φ1 r₀ rabs
  -- 10. eq. (58): the argmin over λ'
  let sstar := aux_optDeltatSearchFloat cost 0 fuel
  -- 10. eq. (58): Δt* = h ζ_δ^{λ'}
  ⟨mulUp h (powUp ζδ sstar), sstar⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
