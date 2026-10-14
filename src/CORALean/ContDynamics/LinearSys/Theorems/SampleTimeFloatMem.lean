module

public import CORALean.ContDynamics.LinearSys.Operations.SampleTimeFloat
public import CORALean.Global.Float.SoundFloatArithmetic
public import Mathlib.Algebra.CharP.Defs

@[expose] public section

/-!
# `sampleTimeFloat` brackets `k Δt`

By strong induction on `k`: `k = 2 ⌊k/2⌋ + (k mod 2)`, and doubling and adding
`Δt` are sums, which `addDown_le_add`/`add_le_addUp` bound outward at any sign.
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.sampleTimeFloat_mem (Δt : 𝕋) (k : ℕ) :
    toReal (LinearSys.sampleTimeFloat Δt k).inf ≤ k * toReal Δt
      ∧ k * toReal Δt ≤ toReal (LinearSys.sampleTimeFloat Δt k).sup := by -- --- PROOF ---
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero => rw [LinearSys.sampleTimeFloat]; simp [toReal_zero]
    | succ k =>
      obtain ⟨hlo, hhi⟩ := ih ((k + 1) / 2) (by omega)
      set m := (k + 1) / 2
      set h := LinearSys.sampleTimeFloat Δt m
      have hd1 := addDown_le_add h.inf h.inf
      have hd2 := add_le_addUp h.sup h.sup
      rw [LinearSys.sampleTimeFloat]
      -- `k + 1` is `2m` or `2m + 1`
      split_ifs with hk
      · have hkm : ((k + 1 : ℕ) : ℝ) = 2 * m := by
          have : k + 1 = 2 * m := by omega
          rw [this]; push_cast; ring
        rw [hkm]
        exact ⟨by linarith, by linarith⟩
      · have hkm : ((k + 1 : ℕ) : ℝ) = 2 * m + 1 := by
          have : k + 1 = 2 * m + 1 := by omega
          rw [this]; push_cast; ring
        rw [hkm]
        have h3 := addDown_le_add (addDown h.inf h.inf) Δt
        have h4 := add_le_addUp (addUp h.sup h.sup) Δt
        exact ⟨by linarith, by linarith⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
