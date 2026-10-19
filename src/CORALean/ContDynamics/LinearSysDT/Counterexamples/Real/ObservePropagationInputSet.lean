module

public import CORALean.ContDynamics.LinearSysDT.Operations.ObservePropagation
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
public import CORALean.ContDynamics.LinearSysDT.Operations.Canonical

@[expose] public section

/-!
# CORA's observers drop the input set `U`

`observe` validates `params.U` (`config_contDynamics_observe`, l. 40) and `postProcessing`
skips the split of `u` into `U` and `uTransVec` for `observe` (l. 53), so `params.U` reaches
`executeObserver` and no observer reads it: the strip-based ones predict with
`post(sys, Rnext, params.uTransVec(:,k))` (`observe_stripBased`, l. 61; `nonlinearSysDT/post`
sets `params.U` to the origin, l. 34), the others with `B*params.uTransVec(:,k)` alone
(`priv_observe_intersectionFree`, l. 53; `CZN_A`, l. 54; `CZN_B`, l. 76; `interval`, l. 62).
Here `A = B = C = 1`, `R0 = {0}`, `W = V = {0}`, `u = 0` and `U = [-1, 1]`: the input `1 ∈ U`
moves the state to `x₁ = 1`, and the next set of `observePropagation` (`PRad-E`, `Nom-G`,
`FRad-C`) is `{0}` at every gain, which misses it. Read from the source, not run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The input `1` of `U = [-1, 1]` takes `x₀ = 0` to `x₁ = 1`, and `x₁` is not in the observer's
next set, at every gain and order. -/
theorem LinearSysDT.observePropagation_input_set_counterexample
    (gain : Zonotope (Vec ℝ 1) → Mat ℝ 1 1) (order : ℕ) : -- --- CONCL ---
    let sys : LinearSysDT ℝ 1 := LinearSysDT.canonical 1
    let U : Zonotope (Vec ℝ 1) := ⟨1, 0, fun _ _ => 1⟩  -- `params.U`
    let ũ : Vec ℝ 1 := fun _ => 1  -- the input drawn from `U`
    let x : ℕ → Vec ℝ 1 := fun k _ => k
    let R₀ : Zonotope (Vec ℝ 1) := Zonotope.ofPoint (x 0)
    let y : ℕ → Vec ℝ 1 := fun k => (1 : Mat ℝ 1 1) *ᵥ x k  -- `C = 1`, `v = 0`
    x 0 ∈ R₀.construct ∧ ũ ∈ U.construct ∧ x 1 = sys.A *ᵥ x 0 + sys.B *ᵥ (0 + ũ) ∧
      x 1 ∉ (sys.observePropagation gain order (Zonotope.ofPoint 0) R₀ (Zonotope.ofPoint 0)
        (fun _ => 0) y 1).construct := by -- --- PROOF ---
  intro sys U ũ x R₀ y
  refine ⟨Zonotope.mem_ofPoint _, ⟨fun _ => 1, fun _ => by norm_num, ?_⟩, ?_, ?_⟩
  · funext i
    simp [U, ũ]
  · funext i
    simp [x, ũ, sys]
  · rintro ⟨β, -, hx⟩
    have h0 := congrFun hx 0
    simp [LinearSysDT.observePropagation, Zonotope.reduce, Zonotope.reduceGirard,
      Zonotope.plus, Zonotope.mtimes, Zonotope.ofPoint, R₀, y, x] at h0
    simp only [show (fun _ : Fin 1 => (0 : ℝ)) = 0 from rfl, Matrix.mulVec_zero] at h0
    norm_num at h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
