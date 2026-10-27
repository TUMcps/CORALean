module

public import CORALean.ContDynamics.LinearSys.Operations.DeltaReach
public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrPolySearch
public import CORALean.ContDynamics.NonlinearSys.Operations.LagrangeRemainder
public import CORALean.ContDynamics.NonlinearSys.Operations.LinInput
public import CORALean.ContDynamics.NonlinearSys.Operations.Linearize
public import CORALean.ContDynamics.NonlinearSys.Operations.PrecompStatError
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_PolyZonotope
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Instances
public import CORALean.ContSet.PolyZonotope.Real.Operations.PadBack
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapMixed
public import CORALean.ContSet.PolyZonotope.Real.Operations.Reduce
public import CORALean.ContSet.Zonotope.Real.Operations.Reduce
public import CORALean.Global.Block

@[expose] public section

/-!
# One step of `linReach` at `alg = 'poly'`, end to end

CORA's `linReach` for [1, Alg. 1], lines 3-10: `aux_deltaReach` for `Rdiff`, `priv_precompStatError`
for `VerrorStat`, and the `while` loop, whose candidates `aux_abstrErrPolyCandidates` computes and
`abstrErrPolySearch` tests. Only what CORA takes as data is supplied: the expansion point, `A`,
`B`, the Hessian `H`, the third-order bound `E`, and the previous step's `abstrerr`. Candidate `k`
is certified by CORA's split of the second-order term, so `W` must cover exactly `VerrorDyn`'s
products carrying `δ` and the cubic remainder. No termination is claimed; `linReachPoly_outer`
says what a `some` means.

## Inputs
* `sys` – system
* `U` – input polynomial zonotope
* `A` – state Jacobian
* `B` – input Jacobian
* `xs` – state expansion point
* `us` – input expansion point
* `H` – Hessian family
* `E` – third-derivative bounds
* `Δt` – step size
* `η` – Taylor terms
* `errorOrder` – order for the error
* `intermediateOrder` – intermediate order
* `Rinit` – start polynomial zonotope
* `abstrerr` – previous abstraction error
* `fuel` – bound for the search

## Output
* the first accepted linearization step, or none

## References

* [1] [M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative Polynomialization
      and Non-Convex Sets". Proceedings of the 16th international conference on Hybrid systems:
      computation and control,
      2013.](../../../../../references/2013/althoff-hscc-conservative-polynomialization.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Candidate `k` of `linReach`'s `alg = 'poly'` loop from the seed `abstrerr`:
`Rdiff + RallError` at the `k`-th applied error, and `VerrorDyn` over it. -/
noncomputable def NonlinearSys.aux_abstrErrPolyCandidates (A : Mat ℝ n n) (xs : Vec ℝ n)
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
    NonlinearSys.aux_abstrErrPolyCandidates A xs us H E Δt η errorOrder intermediateOrder U Rinit
      Rdiff VerrorStat trueError k


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One step of CORA's `linReach` at `alg = 'poly'` from the start set `Rinit`: the
first candidate the certificate accepts, as a `LinStep`, or `none` past `fuel`. -/
noncomputable def NonlinearSys.linReachPoly (sys : NonlinearSys n m)
    (U : PolyZonotope (Vec ℝ m)) (A : Mat ℝ n n) (B : Mat ℝ n m) (xs : Vec ℝ n) (us : Vec ℝ m)
    (H : Fin n → Mat ℝ (n + m) (n + m)) (E : Fin n → Fin (n + m) → Mat ℝ (n + m) (n + m))
    (Δt : ℝ) (η errorOrder intermediateOrder : ℕ) (Rinit : PolyZonotope (Vec ℝ n))
    (abstrerr : Vec ℝ n) (fuel : ℕ) : Option (sys.LinStep (S := 𝒫𝒵) U) :=
  let linsys := NonlinearSys.linearize A                                  -- linearize
  let Ulin := linInput (S := 𝒫𝒵) sys.f A B xs us U (PolyZonotope.ofPoint 0) -- linParams.U
  let Rdiff := (linsys.deltaReach (S := 𝒫𝒵) Δt η Rinit).plus
    (linsys.inputSolution (S := 𝒫𝒵) Δt η Ulin)                           -- aux_deltaReach
  -- priv_precompStatError, at `Ustat = 0`: half the Hessian's state block
  let Rstat := Rinit.dependent
  let Hstat : Fin n → Mat ℝ n n :=
    fun i => (2 : ℝ)⁻¹ • (H i).submatrix (Fin.castAdd m) (Fin.castAdd m)
  let VerrorStat := precompStatError Hstat xs Rstat                       -- 0.5*quadMap(Z,H)
  let cand := NonlinearSys.aux_abstrErrPolyCandidates A xs us H E Δt η errorOrder
    intermediateOrder U Rinit Rdiff VerrorStat abstrerr
  -- the loop: candidate `k` certified over `Rinit ⊞ (Rdiff + RallError)`
  sys.abstrErrPolySearch U A B xs us (fun k => Rstat.plus (cand k).1)
    (fun _ => {a | ∀ j, |a j| ≤ 1}) (fun k => VerrorStat.padBack (cand k).1.p) (fun _ => rfl)
    (fun _ _ ha => ha) (fun k => (cand k).2) fuel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
