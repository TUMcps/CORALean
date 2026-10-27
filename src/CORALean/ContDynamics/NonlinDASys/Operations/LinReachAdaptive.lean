module

public import CORALean.ContDynamics.NonlinDASys.Definitions.AdaptTuning
public import CORALean.ContDynamics.NonlinDASys.Operations.AbstractionErrorAdaptive
public import CORALean.ContDynamics.NonlinDASys.Operations.LinReachAt
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `NonlinDASys.linReachAdaptive`

CORA's `linReach_adaptive` ([1, Alg. 1]) for a start set at the finite horizon `h`: on
the last step one pass at `h`, otherwise a first run at `h` and a second at the step the tuning
`T.tune` chose from it. The heuristics are `AdaptTuning`'s arguments, the tensor order is fixed
at 2, and the extra pass of `timeStepequalHorizon` is not modelled: the second run's sets are
returned.

## Inputs
* `sys` – system
* `T` – tuning heuristics
* `Rstart` – start set
* `U` – input zonotope
* `η` – Taylor order
* `fuelErr` – error loop fuel
* `fuelHalf` – step halving fuel
* `adm_x` – admissible state errors
* `adm_y` – admissible algebraic errors
* `h` – horizon
* `lastStep` – whether this is the last step

## Output
* the accepted pass, or none

## References

* [1] [M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control,
      2014.](../../../../../references/2014/althoff-tac-nonlinear-dae.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix ContSet

variable {n p m q : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- [1, Alg. 1] lines 4-10 at line 3's `taylor`, from `Rd_tk = Rᵈ(t_k)` with step `r`: the error
`L` of the first pass with `L ⊆ L̄`, `L̄` growing to `expFactor` times `L`; `none` after `fuel`. -/
noncomputable def NonlinDASys.aux_errorLoopAdaptive (sys : NonlinDASys n p m)
    (T : NonlinDASys.AdaptTuning n p m q) (taylor : NonlinDASys.LinPoint n p m)
    (Rd_tk : Zonotope (Vec ℝ n)) (U : Zonotope (Vec ℝ m)) (r : ℝ) (η : ℕ) :
    ℕ → Vec ℝ n → Vec ℝ p → Option (NonlinDASys.AbstractionError n p)
  | 0, _, _ => none
  -- 4. `repeat`
  | fuel + 1, adm_x, adm_y =>
    -- 5. `L̄ᵈ`
    let Lbar_d : Zonotope (Vec ℝ n) := Interval.zonotope ⟨-adm_x, adm_x⟩
    -- 5. `L̄ᵃ`
    let Lbar_a : Zonotope (Vec ℝ p) := Interval.zonotope ⟨-adm_y, adm_y⟩
    -- 5. `L̄ = L̄ᵈ ⊕ (-CF⁻¹)L̄ᵃ`
    let Lbar : Zonotope (Vec ℝ n) :=
      Lbar_d.plus (Lbar_a.mtimes (-(taylor.C * taylor.F_inv)))
    -- 6. `Ū`, 7. `Rᵈ(τ_k)`
    let R := NonlinDASys.linReachAt sys { taylor with Verror := Lbar, Verror_y := Lbar_a }
      Rd_tk U r η
    -- 8. `R(τ_k)`, Prop. 2
    let R_τk := R.2.2
    -- 9. `L`, Cor. 1
    let L := NonlinDASys.abstractionErrorAdaptive (taylor.C * taylor.F_inv)
      (T.hess R_τk)
    -- 10. `until L ⊆ L̄`
    if (List.finRange n).all (fun i => T.le (L.errorInt_x i) (adm_x i)) &&
        (List.finRange p).all (fun j => T.le (L.errorInt_y j) (adm_y j)) then
      some L
    else
      -- 5. the next `L̄` from `L`
      sys.aux_errorLoopAdaptive T taylor Rd_tk U r η fuel
        (T.expFactor • L.errorInt_x) (T.expFactor • L.errorInt_y)

/-- One pass at the step `Δt`: the error loop, and the step halved (`options.Δt * 0.5`)
where it did not converge. -/
noncomputable def NonlinDASys.aux_passAdaptive (sys : NonlinDASys n p m)
    (T : NonlinDASys.AdaptTuning n p m q) (L : NonlinDASys.LinPoint n p m)
    (Rstart : Zonotope (Vec ℝ n)) (U : Zonotope (Vec ℝ m)) (η fuelErr : ℕ)
    (adm_x : Vec ℝ n) (adm_y : Vec ℝ p) :
    ℕ → ℝ → Option (NonlinDASys.AdaptPass n p)
  | 0, _ => none
  | k + 1, Δt =>
    match sys.aux_errorLoopAdaptive T L Rstart U Δt η fuelErr adm_x adm_y with
    | some err => some ⟨Δt, err⟩
    | none => sys.aux_passAdaptive T L Rstart U η fuelErr adm_x adm_y k (Δt / 2)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `linReach_adaptive` for the start set `Rstart` at the finite horizon `h`: on the last
step one pass at `h`, otherwise a first run at `h` and a second at the step size `T.tune` chose
from it. -/
noncomputable def NonlinDASys.linReachAdaptive (sys : NonlinDASys n p m)
    (T : NonlinDASys.AdaptTuning n p m q) (Rstart : Zonotope (Vec ℝ n))
    (U : Zonotope (Vec ℝ m)) (η fuelErr fuelHalf : ℕ) (adm_x : Vec ℝ n) (adm_y : Vec ℝ p)
    (h : ℝ) (lastStep : Bool) : Option (NonlinDASys.AdaptPass n p) :=
  let L := T.taylor Rstart                                                 -- priv_linearize
  if lastStep then
    sys.aux_passAdaptive T L Rstart U η fuelErr adm_x adm_y fuelHalf h          -- last step
  else
    match sys.aux_passAdaptive T L Rstart U η fuelErr adm_x adm_y fuelHalf h with  -- run 1
    | none => none
    | some p₁ =>
      sys.aux_passAdaptive T L Rstart U η fuelErr adm_x adm_y fuelHalf (T.tune h p₁)  -- run 2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
