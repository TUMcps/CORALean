module

public import CORALean.ContDynamics.NonlinDASys.NonlinDASys
public import CORALean.ContSet.Zonotope.Real.Operations.QuadMap
public import CORALean.ContSet.Zonotope.Real.Operations.AbsBound
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `NonlinDASys.compLocalErrorCora`

The linearization error of one subsystem of CORA's compositional option, as
`private/priv_linError_mixed_noInt_comp.m` computes it (ll. 94-159, reached from `linReach.m` ll.
91-99 when `options` has the field `index`). The subsystem's Hessians `Hf`, `Hg`, split into
midpoint and radius, act on the zonotope `R_xyu` of its `(x, y, u)` (`Rsub`, `Rsub_y_cor +
Rsub_y_add`, `Usub`), and the algebraic error enters through `Csub * pinv(Fsub)` of the
*subsystem's own* `Csub`, `Fsub` (l. 150-152), not the block of the full system's `C F⁻¹`. As in
`linErrorCora`, the radius `dz_abs` is `R_xyu.absBound` and the `reduce` before `quadMap` (l. 104)
is left out.

# CORA's compositional linearization error ignores the coupling of the subsystems

`NonlinDASys.compLocalErrorCora` (`priv_linError_mixed_noInt_comp`, `options.index`) for
`ẋ₁ = y₁`, `0 = y₁ - y₂` (subsystem 1, `u = y₂`) and `ẋ₂ = y₂`, `0 = y₂ - x₂²` (subsystem 2),
linearized at `0` (`F = [[1, -1], [0, 1]]`, `C = I`, `D = 0`; see
`NonlinDASys.compositional_local_error_counterexample`). Subsystem 1's functions are linear, so
its Hessians are `0` and CORA's set `error{1}` is `{0}` for every `R_xyu` and whatever `Csub`,
`Fsub`: the sign of `CFsub_inv` is immaterial, this is not the sign issue. The true error of
`ẋ₁` at the consistent point `x₂ = 1`, `y = (1, 1)` is `1`: `f₁ = y₁ = 1` against the
linearization's `0`. Component 1 of `errorTotal` comes from `error{1}` alone (`index{2}.X'` has
a zero first row), so CORA's set misses it.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's local error set is zero while the true error is one

## References

* [1] [M. Althoff. "Formal and Compositional Analysis of Power Systems using Reachable Sets". IEEE
      Transactions on Power Systems,
      2014.](../../../../../references/2014/althoff-tps-power-systems.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {nx ny nz : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `error{iSys}` of `priv_linError_mixed_noInt_comp` (ll. 126-159) for one subsystem,
[1, Sec. V-B]. -/
noncomputable def NonlinDASys.compLocalErrorCora (Hf_mid Hf_rad : Fin nx → Mat ℝ nz nz)
    (Hg_mid Hg_rad : Fin ny → Mat ℝ nz nz) (Csub : Mat ℝ nx ny) (Fsub : Mat ℝ ny ny)
    (R_xyu : Zonotope (Vec ℝ nz)) : Zonotope (Vec ℝ nx) :=
  let dz_abs : Vec ℝ nz := R_xyu.absBound
  -- l. 126: `error_y_mid = 0.5*quadMap_parallel(R_xyu, Hg_mid)`
  let error_y_mid : Zonotope (Vec ℝ ny) :=
    ⟨(R_xyu.quadMap Hg_mid).h, (1 / 2 : ℝ) • (R_xyu.quadMap Hg_mid).c,
      fun j => (1 / 2 : ℝ) • (R_xyu.quadMap Hg_mid).G j⟩
  -- ll. 129-131: `error_y_rad(i,1) = 0.5*dz_abs'*Hg_rad{i}*dz_abs`
  let error_y_rad : Vec ℝ ny := fun i => (1 / 2 : ℝ) * (dz_abs ⬝ᵥ (Hg_rad i *ᵥ dz_abs))
  -- l. 134: `error_y_rad_zono = zonotope(interval(-error_y_rad, error_y_rad))`
  let error_y_rad_zono : Zonotope (Vec ℝ ny) := Interval.zonotope ⟨-error_y_rad, error_y_rad⟩
  -- l. 139: `error_x_mid = 0.5*quadMap_parallel(R_xyu, Hf_mid)`
  let error_x_mid : Zonotope (Vec ℝ nx) :=
    ⟨(R_xyu.quadMap Hf_mid).h, (1 / 2 : ℝ) • (R_xyu.quadMap Hf_mid).c,
      fun j => (1 / 2 : ℝ) • (R_xyu.quadMap Hf_mid).G j⟩
  -- ll. 142-146: `error_x_rad`, `error_x_rad_zono`
  let error_x_rad : Vec ℝ nx := fun i => (1 / 2 : ℝ) * (dz_abs ⬝ᵥ (Hf_rad i *ᵥ dz_abs))
  let error_x_rad_zono : Zonotope (Vec ℝ nx) := Interval.zonotope ⟨-error_x_rad, error_x_rad⟩
  -- ll. 151-152: `Fsub_inv = pinv(Fsub)`, `CFsub_inv = Csub*Fsub_inv`
  let Fsub_inv : Mat ℝ ny ny := Fsub⁻¹
  let CFsub_inv : Mat ℝ nx ny := Csub * Fsub_inv
  -- ll. 155-157: `error_mid = zonotope(Z_err_x_mid + Z_err_x_add_mid)`
  let error_mid : Zonotope (Vec ℝ nx) :=
    ⟨error_x_mid.h, error_x_mid.c + CFsub_inv *ᵥ error_y_mid.c,
      fun j => error_x_mid.G j + CFsub_inv *ᵥ error_y_mid.G j⟩
  -- l. 158: `error_rad = error_x_rad_zono + CFsub_inv*error_y_rad_zono`
  let error_rad : Zonotope (Vec ℝ nx) :=
    error_x_rad_zono.plus (error_y_rad_zono.mtimes CFsub_inv)
  -- l. 159: `error{iSys} = error_mid + error_rad`
  error_mid.plus error_rad

end CORALean

namespace CORALean

open CORALean.Real Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. V-B]: subsystem 1 (`Hf = Hg = 0`): every point of CORA's error set is `0`, whatever
`R_xyu`, `Csub`, `Fsub`; the true error of `ẋ₁` at `x₂ = 1`, `y = (1, 1)` (consistent: `g = 0`)
is `1`. -/
theorem NonlinDASys.compLocalErrorCora_counterexample : -- --- CONCL ---
    (∀ (Csub Fsub : Mat ℝ 1 1) (R_xyu : Zonotope (Vec ℝ 3)),
      ∀ e ∈ (NonlinDASys.compLocalErrorCora (fun _ => 0) (fun _ => 0) (fun _ => 0)
        (fun _ => 0) Csub Fsub R_xyu).construct, e = 0) ∧
    -- true error of `ẋ₁ = y₁` at `x₂ = 1`, `y = (1, 1)`: `f₁ - (w₁ + Ã₁ Δx)` with `w = 0`, `Ã = 0`
    ((![1, 1] : Fin 2 → ℝ) 0 - 0 = 1 ∧
      (![(1 : ℝ), 1] 0 - ![1, 1] 1 = 0 ∧ ![(1 : ℝ), 1] 1 - (1 : ℝ) ^ 2 = 0)) := by -- --- PROOF ---
  refine ⟨fun Csub Fsub R e he => ?_, by simp, by simp, by simp⟩
  obtain ⟨β, -, rfl⟩ := he
  ext i
  fin_cases i
  simp [NonlinDASys.compLocalErrorCora, Zonotope.quadMap, Zonotope.plus, Zonotope.mtimes,
    Interval.zonotope, ← Pi.zero_def, dotProduct, mulVec, Fin.append, Fin.addCases]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
