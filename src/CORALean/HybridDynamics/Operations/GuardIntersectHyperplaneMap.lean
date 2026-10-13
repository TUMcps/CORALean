import CORALean.HybridDynamics.Definitions.Location
import CORALean.HybridDynamics.Definitions.HitPoint
import CORALean.HybridDynamics.Definitions.HitJacobian
import CORALean.HybridDynamics.Definitions.SdcInput
import CORALean.HybridDynamics.Operations.AbstractionError
import CORALean.HybridDynamics.Operations.HitHessianMatZono
import CORALean.ContSet.ContSet.Operations.ProjectOnHyperplane
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Operations.HalfspaceRange
import CORALean.ContSet.Zonotope.Real.Operations.QuadMapMatZono
import CORALean.ContSet.Zonotope.Real.Operations.ReduceGirard

/-!
# `Location.guardIntersectHyperplaneMap`, the guard mapping of Althoff and Krogh

CORA's `guardIntersect_hyperplaneMap` [1] for `ẋ = Ax + u`, `u ∈ U`, onto `{x | nᵀx = d}`, one
`let` per line: `k ⊕ L(R₀ ⊖ ξ) ⊕ ½[φ̲, φ̄] R_quad ⊕ I (AR₀ ⊕ b) ⊕ E` of [2, Sec. 5.4], `b` of
[2, Prop. 1] at `th = tmax/2`, Girard-reduced and projected onto the normalized hyperplane.
Departures: `ψ_c`, `ψ_g` are the one-factor `−n − τ_c Υᵀ`, `−τ_g Υᵀ` from an interval of `τ =
(d − nᵀx)/Λ(x)`, the reading of [2, Prop. 3] that holds, where CORA encloses `Θ/Λ` coordinatewise
(FINDINGS.md, `Location guardIntersect_hyperplaneMap, coordinatewise ψ`); `err1` and the slices
of `Q⁽ⁱ⁾` as the code means (FINDINGS.md, `... abstraction error and quadratic map`); `none` when
a divisor interval holds `0`. `aux_refinedIntersectionTime`, a second `reach` with the guard's
halfspace as invariant, enters as its outputs `R₀` and `tmax`; the nonlinear branch of
`aux_systemParams` is not modelled.

## References

* [1] `hybridDynamics/@location/guardIntersect_hyperplaneMap.m`
* [2] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {G : ℕ → Type} {L : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `R = guardIntersect_hyperplaneMap(loc,guard,R0,params,options)` at the refined `R₀` and
`tmax`, `η = options.η`. -/
noncomputable def Location.guardIntersectHyperplaneMap (ℓ : Location 𝒵 G L ℝ n) (nv : Vec ℝ n)
    (d : ℝ) (R₀ : Zonotope (Vec ℝ n)) (tmax : ℝ) (η guardOrder zonotopeOrder : ℕ) :
    Option (Zonotope (Vec ℝ n)) :=
  -- `[a, b] * Z` of a real interval and a zonotope, as the interval matrix `[a, b] I`
  let mulI : ℝ → ℝ → Interval (Mat ℝ n n) := fun a b =>
    ⟨Matrix.of fun j k => Interval.mulLo ((1 : Mat ℝ n n) j k) ((1 : Mat ℝ n n) j k) a b,
      Matrix.of fun j k => Interval.mulHi ((1 : Mat ℝ n n) j k) ((1 : Mat ℝ n n) j k) a b⟩
  let A : Mat ℝ n n := ℓ.dynamics.A                                -- [A,U] = aux_systemParams
  let U : Zonotope (Vec ℝ n) := ℓ.U
  let th : ℝ := tmax / 2                                           -- th = tmax/2
  let b : Vec ℝ n := GuardMap.sdcInput A U.c th η R₀.c             -- b = aux_constantFlow
  let R0red := R₀.reduceGirard guardOrder                          -- R0red = reduce(R0,..)
  let R0red_ := R0red.recentre                                     -- R0red_ = R0red - c
  let R0_ := R₀.recentre                                           -- R0_ = R0 - center(R0)
  let err := GuardMap.abstractionError A U R0red th tmax η         -- err = aux_abstractionError
  -- `aux_taylorSeriesParam(guard,A,b,R0red)`
  let x0 := R0red.c                                                -- x0 = center(R0)
  let Υ : Vec ℝ n := nv ᵥ* A                                       -- Upsilon = (n'*A)'
  let flowRed := (Zonotope.mtimes A R0red).plus (Zonotope.ofPoint b)  -- A*R0 + b
  let Λint := flowRed.halfspaceRange nv 0                          -- Lambda_int
  let dint := R0red.halfspaceRange nv d                            -- interval(n'*R0 - d)
  let τlo := Interval.mulLo (-dint.2) (-dint.1) Λint.2⁻¹ Λint.1⁻¹  -- tau = (d - n'R0)/Lambda
  let τhi := Interval.mulHi (-dint.2) (-dint.1) Λint.2⁻¹ Λint.1⁻¹
  let ψc : Vec ℝ n := -nv - ((τlo + τhi) / 2) • Υ                  -- psi_c, one factor
  let ψg : Vec ℝ n := -(((τhi - τlo) / 2) • Υ)                     -- psi_g, one factor
  let φlo := 1 / max (Λint.1 ^ 2) (Λint.2 ^ 2)                     -- phi = 1/Lambda_int^2
  let φhi := 1 / min (Λint.1 ^ 2) (Λint.2 ^ 2)
  let k := GuardMap.hitPoint A b nv d x0                           -- k
  let L := GuardMap.hitJacobian A b nv d x0                        -- L
  let Q := GuardMap.hitHessianMatZono A b nv d R0red ψc ψg         -- Q{i}
  -- `res1 = k + L*R0_ + 0.5*phi*quadMap(R0red_,Q)`
  let Rquad := Zonotope.quadMapMatZono (fun i => (Q i).c)
    (fun (j : Fin (1 + R0red.h + R0red.h)) i => (Q i).G j) R0red_  -- quadMap(R0red_,Q)
  let res1 := ((Zonotope.ofPoint k).plus (Zonotope.mtimes L R0_)).plus
    (Zonotope.mtimesIntervalMat (mulI (φlo / 2) (φhi / 2)) Rquad)
  -- `res2 = aux_mappedSetError(guard,R0,A,b,err)`
  let flowSet := (Zonotope.mtimes A R₀).plus (Zonotope.ofPoint b)  -- flowSet = A*R0 + b
  let numInt := err.halfspaceRange (-nv) 0                         -- interval(-n*err)
  let denInt := flowSet.halfspaceRange nv 0                        -- interval(n*flowSet)
  let Ilo := Interval.mulLo numInt.1 numInt.2 denInt.2⁻¹ denInt.1⁻¹  -- I = num/den
  let Ihi := Interval.mulHi numInt.1 numInt.2 denInt.2⁻¹ denInt.1⁻¹
  let res2 := (Zonotope.mtimesIntervalMat (mulI Ilo Ihi) flowSet).plus err  -- I*flowSet + err
  let R := (res1.plus res2).reduceGirard zonotopeOrder             -- R = reduce(res1 + res2)
  let nrm := Real.sqrt (nv ⬝ᵥ nv)                                  -- normalizeConstraints
  if (0 < Λint.1 ∨ Λint.2 < 0) ∧ (0 < denInt.1 ∨ denInt.2 < 0) then
    some (ContSet.projectOnHyperplane (S := 𝒵) R (nrm⁻¹ • nv) (d / nrm))  -- projectOnHyperplane
  else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
