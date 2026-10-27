module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdaptiveRemainder
public import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContSet.Zonotope.Real.Operations.Recenter
public import CORALean.ContSet.Zonotope.Real.Operations.ScalarIntervalMul
public import CORALean.ContSet.Zonotope.Real.Operations.SumTerms

@[expose] public section

/-!
# The error between a linear solution and a constant-derivative one

CORA's `linearSys/trajectoryError` [1], `E_err`: the set of `x(t) - y(t)`, `t ∈ [tmin, tmax]`,
where `x` is the solution of `ẋ = Ax + u` from `x₀ ∈ R₀` and `y` the state-dependent constant
flow `y₀ + (Ay₀ + b)t` of [2, Eq. 3] with `b` the input of its `Prop. 1` at the "center time"
`tc`, and the Taylor series of both cut at `η`: [2, Eq. 13],
`T(⊕ᵢ₌₂^η (Aⁱ/i!)(Tⁱ⁻¹ (ξ ⊕ Y) ⊖ tcⁱ⁻¹ ξ) ⊕ ⊕ᵢ₌₁^η (Aⁱ/(i+1)!)(Tⁱ ⊖ tcⁱ) u) ⊕ Ê R₀ ⊕ Ê tmax u`
with `ξ` the center of `R₀`, `Y = R₀ ⊖ ξ`, `T = [tmin, tmax]`, `Ê = [-W, W]`,
`W = |e^{|A|tmax} − ∑ᵢ₌₀^η |A|ⁱtmaxⁱ/i!|`, and the flow correction `T (f₁ − f₂)`. Only `E_err`: the
outputs `c_tilde` and `d_tilde`, which CORA documents as `?`, are not defined here.

## Inputs
* `sys` – linear system
* `f₁` – first constant flow
* `f₂` – second constant flow
* `u` – constant input
* `R₀` – initial zonotope
* `tmin` – start of the time interval
* `tmax` – end of the time interval
* `tc` – expansion time
* `η` – Taylor order

## Output
* zonotope holding the trajectory error

## References

* [1] `contDynamics/@linearSys/trajectoryError.m`
* [2] [M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability
      Analysis of Hybrid Systems". Proceedings of the 15th ACM international conference on Hybrid
      Systems: Computation and Control,
      2012.](../../../../references/2012/althoff-hscc-avoiding-intersection.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `E_err = trajectoryError(linsys,f,u,R0,tmin,tmax,tc,order,n)`, line by line. -/
noncomputable def LinearSys.trajectoryError (sys : LinearSys ℝ n) (f₁ f₂ u : Vec ℝ n)
    (R₀ : Zonotope (Vec ℝ n)) (tmin tmax tc : ℝ) (η : ℕ) : Zonotope (Vec ℝ n) :=
  let x0 := R₀.c                                                     -- x0 = center(R0)
  let x0zono := Zonotope.ofPoint x0                                  -- x0zono = zonotope(x0)
  let uzono := Zonotope.ofPoint u                                    -- uzono = zonotope(u)
  let Y := R₀.recenter                                               -- Y = R0 + (-x0)
  let E_state := Zonotope.sumTerms (fun m =>                         -- for i = 2:order
    Zonotope.mtimes (((Nat.factorial (m + 2) : ℝ)⁻¹) • sys.A ^ (m + 2))
      ((Zonotope.scalarIntervalMul (tmin ^ (m + 1)) (tmax ^ (m + 1)) Y).plus
        (Zonotope.scalarIntervalMul (tmin ^ (m + 1) - tc ^ (m + 1))
          (tmax ^ (m + 1) - tc ^ (m + 1)) x0zono))) (η - 1)         -- A^i/i!*(T^(i-1)*Y + ...*x0)
  let E_input := Zonotope.sumTerms (fun m =>                         -- for i = 1:order
    Zonotope.mtimes (((Nat.factorial (m + 2) : ℝ)⁻¹) • sys.A ^ (m + 1))
      (Zonotope.scalarIntervalMul (tmin ^ (m + 1) - tc ^ (m + 1))
        (tmax ^ (m + 1) - tc ^ (m + 1)) uzono)) η                   -- A^i/(i+1)!*((T^i - tc^i)*u)
  let E_err := Zonotope.scalarIntervalMul tmin tmax (E_state.plus E_input)  -- tZono{1}*E_err
  let E : Interval (Mat ℝ n n) :=                                    -- E = interval(-W,W)
    ⟨fun j k => -|MatExp.expRemainderMat sys.A tmax η j k|,
      fun j k => |MatExp.expRemainderMat sys.A tmax η j k|⟩
  ((E_err.plus (Zonotope.mtimesIntervalMat E R₀)).plus                -- E_err + E*R0
    (Zonotope.mtimesIntervalMat (MatExp.adaptiveRemainder sys.A tmax η) uzono)).plus
    (Zonotope.scalarIntervalMul tmin tmax (Zonotope.ofPoint (f₁ - f₂)))  -- + E*tmax*uzono + T*f

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
