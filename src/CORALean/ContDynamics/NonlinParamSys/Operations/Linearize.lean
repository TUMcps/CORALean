module

public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import CORALean.ContDynamics.NonlinParamSys.Operations.LinearizeF
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.Global.Jacobian

@[expose] public section

/-!
# `NonlinParamSys.linearize`

CORA's `nonlinParamSys/linearize` [1], the branch for uncertain parameters in a box `paramInt`
(`isa(params.paramInt,'interval')`), which hands on a `linParamSys` and the point it expands about.
The result is that `LinParamSys` over matrix zonotopes: `zA` and `zB`, the Jacobians in `x` and `u`
over the parameter box, and as its constant the center of `zf`, the zonotope of the constant term
(`linearizeF`), with `(p.x, p.u, p.p)`. The dynamics are split as `parametricDynamicFile` does
(`aux_parametric`): `f(x, u, 0)` and, per parameter, the difference `f(x, u, e_i) - f(x, u, 0)`; the
box is normalized, `f_0 + ∑ c_i f_i`. Nothing checks that `f` is affine in `p`. The input packaging,
the numeric-`p` branch and `'linRem'` are not carried.

## Inputs
* `sys` – parametric system
* `xs` – state expansion point
* `us` – input expansion point
* `paramInt` – parameter box

## Output
* the linearized system over matrix zonotopes with its expansion point

## References

* [1] `contDynamics/@nonlinParamSys/linearize.m`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The linearization of `sys` about `(xs, us)` over the parameter box `paramInt`: the system over
matrix zonotopes, and `(p.x, p.u, p.p)`. -/
noncomputable def NonlinParamSys.linearize (sys : NonlinParamSys n m q) (xs : Vec ℝ n)
    (us : Vec ℝ m) (paramInt : Interval (Vec ℝ q)) :
    LinParamSys 𝕄𝒵 n × Vec ℝ n × Vec ℝ m × Vec ℝ q :=
  let c := paramInt.center                                          -- center(params.paramInt)
  let r := paramInt.radius                                          -- rad(params.paramInt)
  let e := fun i : Fin q => (Pi.single i 1 : Vec ℝ q)               -- unitvector(i,numParams)
  let zf := sys.linearizeF xs us paramInt                           -- zf
  let A0 := jacobianMat (fun x => sys.f x us 0) xs                  -- A(:,:,1)
  let Ai := fun i => jacobianMat (fun x => sys.f x us (e i)) xs - A0   -- A(:,:,i+1)
  let B0 := jacobianMat (fun u => sys.f xs u 0) us                  -- B(:,:,1)
  let Bi := fun i => jacobianMat (fun u => sys.f xs u (e i)) us - B0   -- B(:,:,i+1)
  let zA : Zonotope (Mat ℝ n n) := ⟨q, A0 + ∑ i, c i • Ai i, fun i => r i • Ai i⟩   -- zA
  let zB : Zonotope (Mat ℝ n m) := ⟨q, B0 + ∑ i, c i • Bi i, fun i => r i • Bi i⟩   -- zB
  (⟨zA, m, zB, zf.c⟩, xs, us, c)                                    -- linsys, p.x, p.u, p.p

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
