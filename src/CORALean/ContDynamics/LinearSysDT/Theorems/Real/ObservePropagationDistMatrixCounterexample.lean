import CORALean.ContDynamics.LinearSysDT.Operations.ObservePropagation
import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff

/-!
# CORA's observers drop the disturbance matrix `E`

`linearSysDT` documents `x(k+1) = A x(k) + B u(k) + c + E w(k)` with `w ∈ params.W`, checks
`dim(params.W)` against the columns of `E` (`checkDynParameterParams`, `eqdists`), and its
`simulate` adds `E w`; CORA's examples set `E = eye(dim(params.W))`. The observers add
`params.W` itself: `observe_stripBased`, l. 63; `priv_observe_intersectionFree`, l. 54;
`intersectionFreeAdaptive`, l. 69; `interval`, l. 48; `CZN_A`, l. 54; `CZN_B`, l. 76; and
the gains take `generators(params.W)` as `E`. Here `A = C = 1`, `E = 2`, `W = [-1, 1]`,
`R0 = V = {0}`, `u = 0`: `w = 1` moves the state to `x₁ = 2`, and the next set of
`observePropagation` (`PRad-E`, `Nom-G`, `FRad-C`) is `[-1, 1]` at every gain, which misses
it. `F` and `params.V` are dropped alike. Read from the source, not run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `E = 2`, the disturbance `w = 1` of `W = [-1, 1]` takes `x₀ = 0` to `x₁ = 2`, and `x₁`
is not in the observer's next set, at every gain and every positive order. -/
theorem LinearSysDT.observePropagation_dist_matrix_counterexample
    (gain : Zonotope (Vec ℝ 1) → Mat ℝ 1 1) (order : ℕ) (horder : 0 < order) :
    let sys : LinearSysDT ℝ 1 := ⟨1⟩
    let E : Mat ℝ 1 1 := 2  -- `linsysDT.E`
    let W : Zonotope (Vec ℝ 1) := ⟨1, 0, fun _ _ => 1⟩  -- `params.W`
    let w : Vec ℝ 1 := fun _ => 1
    let x : ℕ → Vec ℝ 1 := fun k _ => 2 * k
    let R₀ : Zonotope (Vec ℝ 1) := Zonotope.ofPoint (x 0)
    let y : ℕ → Vec ℝ 1 := fun k => (1 : Mat ℝ 1 1) *ᵥ x k  -- `C = 1`, `v = 0`
    x 0 ∈ R₀.construct ∧ w ∈ W.construct ∧ x 1 = sys.A *ᵥ x 0 + 0 + E *ᵥ w ∧
      x 1 ∉ (sys.observePropagation 1 gain order W R₀ (Zonotope.ofPoint 0)
        (fun _ => 0) y 1).construct := by -- --- PROOF ---
  intro sys E W w x R₀ y
  refine ⟨Zonotope.mem_ofPoint _, ⟨fun _ => 1, fun _ => by norm_num, ?_⟩, ?_, ?_⟩
  · funext i
    simp [W, w]
  · funext i
    simp [x, w, sys, E]
  · -- the order is met, so `reduce` returns the step's set unchanged
    simp only [LinearSysDT.observePropagation, Zonotope.reduce, Zonotope.reduceGirard]
    rw [dif_neg (by simp only [Zonotope.plus, Zonotope.mtimes, Zonotope.ofPoint, W, R₀]; omega)]
    rintro ⟨β, hβ, hx⟩
    have h0 := congrFun hx 0
    have hb := hβ ⟨0, by simp [Zonotope.plus, Zonotope.mtimes, Zonotope.ofPoint, W, R₀]⟩
    simp [Zonotope.plus, Zonotope.mtimes, Zonotope.ofPoint, R₀, y, x, W] at h0
    simp only [show (fun _ : Fin 1 => (0 : ℝ)) = 0 from rfl, Matrix.mulVec_zero] at h0
    -- the one generator is `W`'s, so `x₁ = 2 = β₀` with `|β₀| ≤ 1`
    rw [show (0 : Fin (0 + 0 + 1)) = Fin.natAdd (0 + 0) (0 : Fin 1) from rfl,
      Fin.append_right] at h0
    simp at h0
    have h2 : (2 : ℝ) ≤ 1 := by rw [h0]; exact (abs_le.mp hb).2
    norm_num at h2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
