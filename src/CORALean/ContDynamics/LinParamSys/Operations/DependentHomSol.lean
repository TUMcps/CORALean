import CORALean.ContDynamics.LinParamSys.LinParamSys
import CORALean.ContDynamics.LinParamSys.Operations.DependentLowOrder
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosure
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylorTail
import CORALean.ContDynamics.LinearSys.MatExp.Operations.InputIntervalTaylorTail
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainder
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# `LinParamSys.dependentHomSol`, CORA's `priv_dependentHomSol` corrected

The time-point solution after one step `r` when the matrix zonotope `sys.A` (`A_c + Σ pᵢ A_g⁽ⁱ⁾`)
and the constant input `U_c + Σ pᵢ U_G⁽ⁱ⁾` share `pᵢ ∈ [-1, 1]`, in CORA's three parts:
`R_lowOrder`, the orders up to `A²` from the centre `c` of `Rinit`, dependent on `p` and
**corrected** (`dependentLowOrder`); `R_rem`, orders `3 … η` and the remainder past `η`, of the
state at `c` and of the input, independent of `p` (`priv_highOrderMappingMatrix`'s `eI`,
`eI_input`); `R_hom_state`, the exponential on `Rinit - c`.

At `intermediateTerms = 2`: every order of `R_rem` is an interval matrix over the box
`sys.A.interval` (CORA keeps orders up to `intermediateTerms` as matrix zonotopes), so
`eZhigh` and `eZhigh_input` are empty and `R_hom_state`'s exponential is the box's
(`expIntervalEnclosure`), not CORA's mixed `mappingMatrixSet.zono + .int`. Sound, looser than
CORA's above `2`. `η ≥ 2` is what the parts assume.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real ContSet

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `Rhom_tp = priv_dependentHomSol(obj, Rinit, Uconst)`, `Uconst = zonotope(Uc, UG)`
sharing the generators' parameters with `sys.A`, with the corrected `R_lowOrder`. -/
noncomputable def LinParamSys.dependentHomSol (sys : LinParamSys 𝕄𝒵 n) (r : ℝ) (η : ℕ)
    (Rinit : Zonotope (Vec ℝ n)) (Uc : Vec ℝ n) (UG : Fin sys.A.h → Vec ℝ n) :
    Zonotope (Vec ℝ n) :=
  -- obtain required variables
  let Ac := sys.A.c
  let Ag := sys.A.G
  let c := Rinit.c
  let Uconst : Zonotope (Vec ℝ n) := ⟨sys.A.h, Uc, UG⟩
  let Ar : Interval (Mat ℝ n n) := Interval.smul r sys.A.interval          -- `A r`, a box
  let E := MatExp.expRemainderBound Ar.absMax η                            -- `obj.E`
  -- second-order dependent solution (corrected)
  let R_lowOrder := LinParamSys.dependentLowOrder Ac Ag c Uc UG r
  -- higher-order independent solution: orders `3 … η` and `E`, as interval matrices
  let eIhigh_taylor := MatExp.expIntervalTaylorTail Ar η
  let eIhigh : Interval (Mat ℝ n n) :=                                      -- `eI + E`
    { inf := fun i j => eIhigh_taylor.inf i j - E,
      sup := fun i j => eIhigh_taylor.sup i j + E }
  let eIhigh_input := Interval.plus (MatExp.inputIntervalTaylorTail Ar r η)  -- `eI_input + E r`
    (MatExp.intervalInputRemainder sys.A.interval r η)
  -- remaining reachable set
  let R_rem_state : Zonotope (Vec ℝ n) :=
    Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵) eIhigh (Zonotope.ofPoint c)
  let R_rem_input : Zonotope (Vec ℝ n) := Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵) eIhigh_input Uconst
  let R_rem : Zonotope (Vec ℝ n) := R_rem_state ⊞ R_rem_input
  -- state solution without centre
  let Rinit_noCenter : Zonotope (Vec ℝ n) := Rinit ⊞ Zonotope.ofPoint (-c)
  let R_hom_state : Zonotope (Vec ℝ n) :=
    Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵) (MatExp.expIntervalEnclosure Ar η) Rinit_noCenter
  -- final solution
  R_hom_state ⊞ R_lowOrder ⊞ R_rem

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
