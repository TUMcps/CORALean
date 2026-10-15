module

public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# `LinearSys.standardRtiCora`: the input curvature `C_input` is not propagated

`oneStep` returns `Hti = enclose(X, Htp) + C_state` without the curvature `C_input = G*u` of the
constant input, which `Rti = Hti + PU + C_input` adds at the end (`oneStep.m` l. 84-88). The loop
of `priv_reach_standard.m` (the branch without `uTransVec`) propagates only the hull part,
`Hti = eAdt * Hti + Pu` (l. 102-103), and adds the step-1 box again, unrotated and unscaled, at
every step: `Rti = Hti + PU + C_input` (l. 117). A time-interval solution of `ẋ = Ax + u` over the
second step is `e^{AΔt}` applied to the first, curvature included, so the box has to be mapped by
`e^{AΔt}`. `priv_reach_wrappingfree.m` (l. 115-116, 124) does the same. `priv_reach_fromStart.m`
(l. 99) and `priv_reach_decomp.m` (l. 107) take `Rti = Hti + PU` and drop `C_input` for `k >= 2`
(they read the sixth output `Pu_0` of `oneStep`, not the eighth). The `uTransVec` branch of
`standard` calls `affineSolution` with a fresh `C_input = G*u(:,k)` per step and is not affected.

Modelled in `ℝⁿ` for `R0 = {0}`, `U = {0}`: `e` is `e^{AΔt}` (a map), `Pu` the constant-input
solution of the first step, `C` the box `C_input`. The time-interval hull of step 1 is the segment
`[0, Pu]` (`enclose({0}, {Pu})`, `C_state = F * {0} = {0}`). Read from the source, not run; the
`x₁`-extent below is also reproduced numerically in `ℝ²` (see
`references/coverage/contDynamics/linearSys.md`, row `reach`).

# CORA's `reach` with `linAlg = 'standard'` misses a state of the second step

A chain of three integrators, `A = [0 1 0; 0 0 1; 0 0 0]`, `c = (0, 0, 1)`, `R0 = {0}`, `U = {0}`,
`timeStep = 1`, `taylorTerms = 2`, `tFinal = 2` (`A³ = 0`, so `E = 0`): `x(t) = (t³/6, t²/2, t)`,
`e = I + A + A²/2`, `Pu = x(1) = (1/6, 1/2, 1)`, and with `G = -A/8 - (√3/27) A²` (the factors
`(η^{-η/(η-1)} - η^{-1/(η-1)}) Δt^η / η!` for `η = 2, 3`) the box is `G u = ([-√3/27, 0],
[-1/8, 0], {0})`, which is exactly the deviation of the first step's curve from its chord. The
second step's set is the segment `e [0, Pu] + Pu` plus the same box, and at the height `x₃ = 3/2`
the segment point is `(3/4, 5/4, 3/2)`. The state `x(3/2) = (9/16, 9/8, 3/2)` lies `3/16` below it
in `x₁`, and the box reaches down to `-√3/27` only, with `√3/27 < 3/16`: the state is outside.
Mapped by `e` the box would be `([-√3/27 - 1/8, 0], [-1/8, 0], {0})`, whose lower end `-0.189`
covers it. Without `C_input` (`fromStart`, `decomp`) the same state is outside as well.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise


-- The model: CORA's code as printed, kept only to be refuted.
/-- `Hti` of step `k + 1`: the segment `[0, Pu]` of `oneStep` for `k = 0`, then
`Hti = eAdt * Hti + Pu`. -/
def LinearSys.standardHtiCora {n : Nat} (e : (Fin n → ℝ) → (Fin n → ℝ)) (Pu : Fin n → ℝ) :
    Nat → Set (Fin n → ℝ)
  | 0 => segment ℝ 0 Pu
  | k + 1 => (fun x => e x + Pu) '' LinearSys.standardHtiCora e Pu k

-- The model: CORA's code as printed, kept only to be refuted.
/-- `Rti = Hti + PU + C_input` of step `k + 1`, with `PU = 0` (the numeric zero for `U = {0}`):
the box `C` is added as computed for step 1. -/
def LinearSys.standardRtiCora {n : Nat} (e : (Fin n → ℝ) → (Fin n → ℝ)) (Pu : Fin n → ℝ)
    (C : Set (Fin n → ℝ)) (k : Nat) : Set (Fin n → ℝ) :=
  LinearSys.standardHtiCora e Pu k + C

/-- `e^{AΔt} = I + A + A²/2` of the integrator chain, `Δt = 1`. -/
noncomputable def LinearSys.chainE (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![x 0 + x 1 + x 2 / 2, x 1 + x 2, x 2]

/-- `Pu = x(1)` of the chain under `u = (0, 0, 1)` (`particularSolution_constant`, `E = 0`). -/
noncomputable def LinearSys.chainPu : Fin 3 → ℝ := ![1 / 6, 1 / 2, 1]

/-- `C_input = G u` for `taylorTerms = 2`: `G = -A/8 - (√3/27) A²`, `u = (0, 0, 1)`. -/
noncomputable def LinearSys.chainC : Set (Fin 3 → ℝ) :=
  {b | -(Real.sqrt 3 / 27) ≤ b 0 ∧ b 0 ≤ 0 ∧ -(1 / 8) ≤ b 1 ∧ b 1 ≤ 0 ∧ b 2 = 0}

/-- `x(t) = (t³/6, t²/2, t)` solves `ẋ = A x + c` for the chain, `x(0) = 0`. -/
theorem LinearSys.chain_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => (![s ^ 3 / 6, s ^ 2 / 2, s] : Fin 3 → ℝ))
      ![t ^ 2 / 2, t, 1] t := by -- --- PROOF ---
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · exact ((hasDerivAt_pow 3 t).div_const 6).congr_deriv (by norm_num; ring)
  · exact ((hasDerivAt_pow 2 t).div_const 2).congr_deriv (by norm_num)
  · exact hasDerivAt_id' t


-- =======================================  MAIN THEOREM  ======================================= --

/-- `x(3/2)`, a state of the second step, is outside `Rti` of the second step. -/
theorem LinearSys.standardRtiCora_counterexample :
    (![9 / 16, 9 / 8, 3 / 2] : Fin 3 → ℝ) =
        (fun s : ℝ => (![s ^ 3 / 6, s ^ 2 / 2, s] : Fin 3 → ℝ)) (3 / 2) ∧
      (![9 / 16, 9 / 8, 3 / 2] : Fin 3 → ℝ) ∉ LinearSys.standardRtiCora LinearSys.chainE
        LinearSys.chainPu LinearSys.chainC 1 := by -- --- PROOF ---
  refine ⟨by ext i; fin_cases i <;> simp <;> norm_num, ?_⟩
  rintro ⟨y, hy, b, hb, hsum⟩
  simp only [LinearSys.standardHtiCora] at hy
  obtain ⟨x, ⟨a, c, ha, hc, hac, rfl⟩, rfl⟩ := hy
  obtain ⟨hb0, hb0', hb1, hb1', hb2⟩ := hb
  have h0 := congrFun hsum 0
  have h2 := congrFun hsum 2
  simp [LinearSys.chainE, LinearSys.chainPu] at h0 h2
  have hs : Real.sqrt 3 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

/-- Without the box, the set of the second step in `fromStart` and `decomp` (`PU = Pu`) is
`standardHtiCora ... 1`, which misses `x(3/2)` too. -/
theorem LinearSys.decompRtiCora_counterexample :
    (![9 / 16, 9 / 8, 3 / 2] : Fin 3 → ℝ) ∉
      LinearSys.standardHtiCora LinearSys.chainE LinearSys.chainPu 1 := by -- --- PROOF ---
  intro hy
  simp only [LinearSys.standardHtiCora] at hy
  obtain ⟨x, ⟨a, c, ha, hc, hac, rfl⟩, hx⟩ := hy
  have h0 := congrFun hx 0
  have h2 := congrFun hx 2
  simp [LinearSys.chainE, LinearSys.chainPu] at h0 h2
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
