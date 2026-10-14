module

public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContDynamics.NonlinearSys.Operations.LagrangeRemainder
public import CORALean.ContDynamics.NonlinearSys.Operations.Linearize
public import CORALean.ContSet.Conversion.Real.Interval_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Interval
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Instances
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapMixed
public import CORALean.ContSet.PolyZonotope.Real.Operations.Reduce
public import CORALean.ContSet.Zonotope.Real.Operations.Reduce
public import CORALean.Global.Block

@[expose] public section

/-!
# The candidates `linReach`'s `alg = 'poly'` loop tries

CORA's `linReach` `while` body, its reading of [1, Alg. 1]'s lines 4-10, with
`priv_abstrerr_poly` at `tensorOrder = 3` inlined, one `let` per source line.
`appliedError = 1.1*abstrerr` is boxed as `Verror`, its solution `RallError` widens
the differences `Rdiff`, and `VerrorDyn` bounds over `Rmax` the second-order products
carrying a difference plus the cubic remainder, [1, Sec. 4.1]'s `mu`, `sq` and
`lagrangeRemainder`. `trueError`, with `VerrorStat`, is the next `abstrerr`: candidate
`k + 1` is candidate `k`'s estimate enlarged, the source's schedule, not `1.1ᵏ`.
Candidate `k` is `(Rdiff + RallError, VerrorDyn)`, checked by a certificate, never trusted.

`params.U` is `U` centred at `us`; a Cartesian product lands in `Vec ℝ (n + m)`
through `blockPadLeft`/`blockPadRight`; `interval` is CORA's, `intervalEven`.
Three departures: `Rdiff + RallError` runs `dependent`, so a region names all of it
by `point`; `E` bounds the third derivative over the region as `lagrangeRemainder`
takes it, where CORA re-evaluates the tensor on `totalInt`; and no
`reachSetExplosion` exit, the search's fuel bounding the loop instead.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Candidate `k` of `linReach`'s `alg = 'poly'` loop from the seed `abstrerr`:
`Rdiff + RallError` at the `k`-th applied error, and `VerrorDyn` over it. -/
noncomputable def NonlinearSys.abstrErrPolyCandidates (A : Mat ℝ n n) (xs : Vec ℝ n)
    (us : Vec ℝ m) (H : Fin n → Mat ℝ (n + m) (n + m))
    (E : Fin n → Fin (n + m) → Mat ℝ (n + m) (n + m)) (Δt : ℝ)
    (η errorOrder intermediateOrder : ℕ) (U : PolyZonotope (Vec ℝ m))
    (Rinit Rdiff VerrorStat : PolyZonotope (Vec ℝ n)) (abstrerr : Vec ℝ n) (k : ℕ) :
    PolyZonotope (Vec ℝ n) × PolyZonotope (Vec ℝ n) :=
  -- linReach, before the loop
  let linsys := NonlinearSys.linearize A
  let Rdelta : PolyZonotope (Vec ℝ n) := { Rinit with c := Rinit.c - xs } -- Rinit + (-p.x)
  let paramsU : PolyZonotope (Vec ℝ m) := { U with c := U.c - us }       -- params.U
  let Rdelta' := Rdelta.zonotope.reduce errorOrder                        -- reduce(zonotope(.))
  let Zdelta := (Rdelta'.polyZonotope.map (blockPadLeft n m)).plus
    ((PolyZonotope.ofPoint (0 : Vec ℝ m)).map (blockPadRight n m))        -- cartProd(., Ustat)
  -- linReach, the body of `while perfIndCurr > 1`
  let appliedError : Vec ℝ n := (1.1 : ℝ) • abstrerr                     -- 1.1*abstrerr
  let Verror := (⟨-appliedError, appliedError⟩ : Interval (Vec ℝ n)).polyZonotope
  let RallError := linsys.inputSolution (S := 𝒫𝒵) Δt η Verror       -- particularSolution_...
  let Rdiff' := (Rdiff.plus RallError).dependent                          -- Rdiff+RallError
  let Rmax := Rdelta.plus Rdiff'                                          -- Rdelta+Rdiff+RallError
  -- priv_abstrerr_poly(sys, Rmax, Rdiff+RallError, ...)
  let dx := Rmax.intervalEven                                             -- interval(Rall)
  let du := paramsU.intervalEven                                          -- interval(params.U)
  let dz := ((dx.polyZonotope.map (blockPadLeft n m)).plus
    (du.polyZonotope.map (blockPadRight n m))).zonotope                   -- [dx; du]
  let Rred_diff := Rdiff'.zonotope.reduce errorOrder                      -- reduce(zonotope(Rdiff))
  let Z_diff := (Rred_diff.polyZonotope.map (blockPadLeft n m)).plus
    (paramsU.map (blockPadRight n m))                                     -- cartProd(., params.U)
  -- the three second-order products that carry a difference
  let error_secondOrder_dyn := PolyZonotope.map ((2 : ℝ)⁻¹ • LinearMap.id)
    (((PolyZonotope.quadMapMixed H Zdelta Z_diff).plus
      (PolyZonotope.quadMapMixed H Z_diff Zdelta)).plus (PolyZonotope.quadMap H Z_diff))
  let error_thirdOrder_dyn := (lagrangeRemainder E dz 0).polyZonotope    -- zonotope(1/6*...)
  let VerrorDyn := (error_secondOrder_dyn.plus error_thirdOrder_dyn).reduce intermediateOrder
  let errorIH := VerrorDyn.intervalEven.plus VerrorStat.intervalEven
  let trueError : Vec ℝ n := fun i => max |errorIH.inf i| |errorIH.sup i| -- supremum(abs(.))
  match k with
  | 0 => (Rdiff', VerrorDyn)
  | k + 1 =>                                                               -- abstrerr = trueError
    NonlinearSys.abstrErrPolyCandidates A xs us H E Δt η errorOrder intermediateOrder U Rinit
      Rdiff VerrorStat trueError k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
