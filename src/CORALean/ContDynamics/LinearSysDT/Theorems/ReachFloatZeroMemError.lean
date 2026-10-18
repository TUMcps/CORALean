module

public import CORALean.ContDynamics.LinearSysDT.Operations.Reach
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
public import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Theorems.ZeroMemMtimesError
public import CORALean.ContSet.Zonotope.Float.Theorems.ZeroMemPlusError

@[expose] public section

/-!
# A float run's own error box always brackets the origin

What `mtimesBox`, `plusBox` and `reduceGirardBox` in `reachErrorFloat` are
read against: `mtimes` and `plus` each keep `0` in the box they hand back
(`zero_mem_mtimes_error`, `zero_mem_plus_error`), given it in what they are
handed, and `reduce`'s error box is untouched — `reduceGirard`'s `E` is
literally the operand's own, in either branch — so it costs nothing to carry
forward. `R₀` and `U` bracketing `0` is the one hypothesis a caller supplies;
everything downstream inherits it by induction.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A float run's error box always brackets `0`, given its two inputs do. -/
theorem LinearSysDT.reachFloat_zero_mem_error (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o)
    {R₀ U : Zonotope (Vec 𝕋 n)} (hR₀ : (0 : Vec ℝ n) ∈ R₀.I_error.construct)
    (hU : (0 : Vec ℝ n) ∈ U.I_error.construct) (k : ℕ) : -- --- STMT ---
    (0 : Vec ℝ n) ∈
      (sys.reach (S := 𝒵[𝕋]) ⟨R₀, U, 0, k⟩
        ⟨o, ho⟩).I_error.construct := by -- --- PROOF ---
  induction k with
  | zero => exact hR₀
  | succ k ih =>
    set Rk := sys.reach (S := 𝒵[𝕋]) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ with hRk
    have hstep : sys.reach (S := 𝒵[𝕋]) ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩
        = Zonotope.reduceGirard ((Zonotope.mtimes sys.A Rk).plus U) o := by
      show Reduce.reduce (Plus.plus
        (Mtimes.mtimes (S := 𝒵[𝕋]) sys.A Rk) U) o = _
      simp only [Mtimes.mtimes, Plus.plus, Reduce.reduce, Zonotope.materialise_eq,
        Zonotope.reduce]
    -- each operation keeps `0` in the error box
    rw [hstep]
    have hM : (0 : Vec ℝ n) ∈ (Zonotope.mtimes sys.A Rk).I_error.construct :=
      Zonotope.zero_mem_mtimes_error ih
    have hW : (0 : Vec ℝ n) ∈ ((Zonotope.mtimes sys.A Rk).plus U).I_error.construct :=
      Zonotope.zero_mem_plus_error hM hU
    show (0 : Vec ℝ n) ∈
        (Zonotope.reduceGirard ((Zonotope.mtimes sys.A Rk).plus U) o).I_error.construct
    unfold Zonotope.reduceGirard
    split_ifs with hlt
    · exact hW
    · exact hW

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
