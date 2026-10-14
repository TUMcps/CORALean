module

public import CORALean.ContDynamics.LinearSysDT.Operations.ObservePropagation
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
public import CORALean.ContDynamics.LinearSysDT.Operations.Canonical

@[expose] public section

/-!
# CORA's set-propagation observers drop the state offset `c`

`linearSysDT` documents `x(k+1) = A x(k) + B u(k) + c + E w(k)`, and its `post` and `simulate`
add `c`, but `priv_observe_intersectionFree` (l. 53-54, behind `PRad-E` and `Nom-G`) and
`priv_observe_intersectionFreeAdaptive` (l. 68-69, `FRad-C`) propagate
`(A - L C) S + B u + L y - L V + W` without it, as do `priv_observe_CZN_A` (l. 54) and
`priv_observe_CZN_B` (l. 76). Here `A = 1`, `c = 1`, `C = 1`, `R0 = {0}`, `W = {0}`,
`V = {0}`, `u = 0`: the true state is `x₀ = 0`, `x₁ = 1`, the output `y₀ = 0`, and the
observer's next set is `{(1 - L) 0 + L 0} = {0}` at every gain `L`, which misses `x₁`.
`LinearSysDT.observePropagation` is CORA's step as printed; `sys.c` has no place in it. Read
from the source, not run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- With the offset `c = 1`, the run `x₀ = 0`, `x₁ = 1` starts in `R0 = {0}` and meets its
output, and `x₁` is not in the observer's next set, at every gain and order. -/
theorem LinearSysDT.observePropagation_state_offset_counterexample
    (gain : Zonotope (Vec ℝ 1) → Mat ℝ 1 1) (order : ℕ) :
    let sys : LinearSysDT ℝ 1 := LinearSysDT.canonical 1
    let c : Vec ℝ 1 := fun _ => 1  -- `linsysDT.c`
    let x : ℕ → Vec ℝ 1 := fun k _ => k
    let R₀ : Zonotope (Vec ℝ 1) := Zonotope.ofPoint (x 0)
    let y : ℕ → Vec ℝ 1 := fun k => (1 : Mat ℝ 1 1) *ᵥ x k  -- `C = 1`, `v = 0`
    x 0 ∈ R₀.construct ∧ x 1 = sys.A *ᵥ x 0 + 0 + c ∧
      x 1 ∉ (sys.observePropagation 1 gain order (Zonotope.ofPoint 0) R₀ (Zonotope.ofPoint 0)
        (fun _ => 0) y 1).construct := by -- --- PROOF ---
  intro sys c x R₀ y
  refine ⟨Zonotope.mem_ofPoint _, ?_, ?_⟩
  · funext i
    simp [x, c, sys]
  · rintro ⟨β, -, hx⟩
    have h0 := congrFun hx 0
    simp [LinearSysDT.observePropagation, Zonotope.reduce, Zonotope.reduceGirard,
      Zonotope.plus, Zonotope.mtimes, Zonotope.ofPoint, R₀, y, x] at h0
    simp only [show (fun _ : Fin 1 => (0 : ℝ)) = 0 from rfl, Matrix.mulVec_zero] at h0
    norm_num at h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
