module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBoundFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.InvFactorialBoundsFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Interval.Float.Operations.MatPow
public import CORALean.ContSet.Interval.Float.Operations.PowHi
public import CORALean.ContSet.Interval.Float.Operations.PowLo
public import CORALean.ContSet.Interval.Float.Operations.Smul
public import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Float.Operations.Point
public import CORALean.ContSet.Zonotope.Float.Operations.Recentre
public import CORALean.ContSet.Zonotope.Float.Operations.SumTerms
public import CORALean.Global.Float.PowDown
public import CORALean.Global.Float.PowUp
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# The error between a linear solution and a constant-derivative one, over a floating-point scalar

`LinearSys.trajectoryError`, CORA's `linearSys/trajectoryError` [1] (`E_err` only), at float
zonotopes, one `let` per line of the code:
`T(⊕ᵢ₌₂^η (Aⁱ/i!)(Tⁱ⁻¹ Y ⊕ (Tⁱ⁻¹ − tcⁱ⁻¹) ξ) ⊕ ⊕ᵢ₌₁^η (Aⁱ/(i+1)!)(Tⁱ − tcⁱ) u) ⊕ Ê R₀ ⊕ Ê tmax u
⊕ T (f₁ − f₂)`, `T = [tmin, tmax]`. Every coefficient that rounds is an interval: `Aⁱ` is
`matPow` at the point interval matrix of `A`, `1/i!` is `invFactorialBounds`, the powers of
`tmin` and `tmax` are `powDown`/`powUp` (nonnegative where the enclosure is claimed), those of
`tc`, of either sign, `Interval.powLo`/`Interval.powHi`, and `f₁ − f₂` is a box. A product of an
interval scalar `[a, b]` with a zonotope is the float `mtimesIntervalMat` at `[a, b] I`.

`W` departs from CORA, which computes `|e^{|A|tmax} − ∑ᵢ₌₀^η (|A|tmax)ⁱ/i!|` with a rounded
`expm`: as in `GuardMap.abstractionErrorFloat`, every entry of `W` is `MatExp.expRemainderBound`
at a float bound `nrm` of `‖tmax A‖`, a sound bound on each entry of `e^{Aτ} − ∑ᵢ₌₀^η (Aτ)ⁱ/i!`
for `τ ∈ [0, tmax]` whenever `nrm ≤ (η + 2)/2`; where that float test fails the result is
`none`.

## References

* [1] `contDynamics/@linearSys/trajectoryError.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `E_err = trajectoryError(linsys,f,u,R0,tmin,tmax,tc,order,n)` at floats, `none` where the
float test `‖tmax A‖ ≤ (η + 2)/2` of the remainder bound fails. -/
def LinearSys.trajectoryErrorFloat (sys : LinearSys 𝕋 n) (f₁ f₂ u : Vec 𝕋 n)
    (R₀ : Zonotope (Vec 𝕋 n))
    (tmin tmax tc : 𝕋) (η : ℕ) : Option (Zonotope (Vec 𝕋 n)) :=
  -- `[a, b] * Z` of a float interval and a zonotope, as the interval matrix `[a, b] I`
  let mulI : 𝕋 → 𝕋 → Interval (Mat 𝕋 n n) := fun a b =>
    Interval.smul a b (Interval.point (diagonalBlock fun _ => one))
  let Apow : ℕ → Interval (Mat 𝕋 n n) := fun i =>                -- `A^i`, bracketed
    Interval.matPow (Interval.point sys.A) i
  let M₁ : ℕ → Interval (Mat 𝕋 n n) := fun m =>                  -- `A^(m+2)/(m+2)!`
    Interval.smul (MatExp.invFactorialBounds (m + 2)).inf (MatExp.invFactorialBounds (m + 2)).sup
      (Apow (m + 2))
  let M₂ : ℕ → Interval (Mat 𝕋 n n) := fun m =>                  -- `A^(m+1)/(m+2)!`
    Interval.smul (MatExp.invFactorialBounds (m + 2)).inf (MatExp.invFactorialBounds (m + 2)).sup
      (Apow (m + 1))
  let tLo : ℕ → 𝕋 := fun m => powDown tmin (m + 1)              -- tZono{m+1}, down
  let tHi : ℕ → 𝕋 := fun m => powUp tmax (m + 1)                -- and up
  let dLo : ℕ → 𝕋 := fun m => subDown (tLo m) (Interval.powHi tc (m + 1))  -- tZono{m+1} - tc^(m+1)
  let dHi : ℕ → 𝕋 := fun m => subUp (tHi m) (Interval.powLo tc (m + 1))
  let nrm := MatExp.normUpperBound (Interval.smul tmax tmax (Interval.point sys.A))  -- `‖tmax A‖`
  if le nrm (half (nsmulDown (η + 2) one)) = true then
    let x0 := R₀.c                                                -- x0 = center(R0)
    let x0zono := Zonotope.point x0                               -- x0zono = zonotope(x0)
    let uzono := Zonotope.point u                                 -- uzono = zonotope(u)
    let Y := R₀.recentre                                          -- Y = R0 + (-x0)
    let E_state := Zonotope.sumTerms (fun m =>                    -- for i = 2:order
      Zonotope.mtimesIntervalMat (M₁ m)
        ((Zonotope.mtimesIntervalMat (mulI (tLo m) (tHi m)) Y).plus
          (Zonotope.mtimesIntervalMat (mulI (dLo m) (dHi m)) x0zono))) (η - 1)  -- A^i/i!*(...)
    let E_input := Zonotope.sumTerms (fun m =>                    -- for i = 1:order
      Zonotope.mtimesIntervalMat (M₂ m)
        (Zonotope.mtimesIntervalMat (mulI (dLo m) (dHi m)) uzono)) η  -- A^i/(i+1)!*(...)*uzono
    let E_err := Zonotope.mtimesIntervalMat (mulI tmin tmax) (E_state.plus E_input)  -- tZono{1}*
    let W : Mat 𝕋 n n := fun _ _ => MatExp.expRemainderBound nrm η  -- W, entrywise
    let E : Interval (Mat 𝕋 n n) := ⟨fun j k => neg (W j k), W⟩   -- E = interval(-W,W)
    let fzono := (⟨fun i => subDown (f₁ i) (f₂ i), fun i => subUp (f₁ i) (f₂ i)⟩ :
      Interval (Vec 𝕋 n)).zonotope                                -- zonotope(f{1}-f{2}), a box
    some (((E_err.plus (Zonotope.mtimesIntervalMat E R₀)).plus    -- E_err + E*R0
      (Zonotope.mtimesIntervalMat (Interval.smul tmax tmax E) uzono)).plus  -- + E*tmax*uzono
      (Zonotope.mtimesIntervalMat (mulI tmin tmax) fzono))        -- + tZono{1}*zonotope(f1-f2)
  else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
