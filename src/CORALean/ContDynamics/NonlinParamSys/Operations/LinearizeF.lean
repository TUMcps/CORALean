module

public import CORALean.ContDynamics.NonlinParamSys.NonlinParamSys
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `NonlinParamSys.linearizeF`

The zonotope `zf` of the constant term of CORA's `nonlinParamSys/linearize` [1], the branch for
uncertain parameters in a box `paramInt` (`isa(params.paramInt,'interval')`): `f(p.x, p.u, p)` over
the box. The dynamics are split as `parametricDynamicFile` does (`derivatives`, `aux_parametric`):
the part without parameters, `f(x, u, 0)`, and for each parameter the difference
`f(x, u, e_i) - f(x, u, 0)` to the unit vector, which is `f_i` in `f = f_0 + ∑ p_i f_i`. The box is
normalized, `f_0 + ∑ c_i f_i` with generators `r_i f_i`. Nothing checks that `f` is affine in `p`;
the split is right only if it is. `linearize` hands its center on as the constant of the system it
returns, a `LinParamSys` holding a vector there, and CORA keeps the zonotope as the constant input.

## Inputs
* `sys` – parametric system
* `xs` – state expansion point
* `us` – input expansion point
* `paramInt` – parameter box

## Output
* the zonotope of the constant term over the parameter box

## References

* [1] `contDynamics/@nonlinParamSys/linearize.m`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The zonotope of the constant term `f(xs, us, p)` over the parameter box `paramInt`. -/
noncomputable def NonlinParamSys.linearizeF (sys : NonlinParamSys n m q) (xs : Vec ℝ n)
    (us : Vec ℝ m) (paramInt : Interval (Vec ℝ q)) : Zonotope (Vec ℝ n) :=
  let c := paramInt.center                                          -- center(params.paramInt)
  let r := paramInt.radius                                          -- rad(params.paramInt)
  let e := fun i : Fin q => (Pi.single i 1 : Vec ℝ q)               -- unitvector(i,numParams)
  let f0 := sys.f xs us 0                                           -- f0_3D(:,:,1)
  let fi := fun i => sys.f xs us (e i) - f0                         -- f0_3D(:,:,i+1)
  ⟨q, f0 + ∑ i, c i • fi i, fun i => r i • fi i⟩                    -- zf

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
