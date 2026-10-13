import CORALean.ContDynamics.LinearSysDT.Operations.ObservePropagation
import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff

/-!
# CORA's observers drop the output offset `k` and the feedthrough `D u`

`linearSysDT` documents `y(k) = C x(k) + D u(k) + k + F v(k)`, and its `simulate` adds `D u`
and `k`, but every observer reads the measurement as `C x` plus noise: the strips
`|C_i x - y_i| ≤ σ_i` (`priv_observe_intersectionMethod_I`, l. 50; `_II`, l. 45;
`ESO_A`, l. 61, 82; `ESO_B`, l. 56, 76; `CZN_B`, l. 67, 89), the set `y - V` met through `C`
(`CZN_A`, l. 45, 58), and the corrections `L y` and `L (y - C x)`
(`priv_observe_intersectionFree`, l. 54; `intersectionFreeAdaptive`, l. 69; `interval`, l. 63;
`ESO_C`, l. 68; `ESO_D`, l. 69). Here `A = C = 1`, `k = 1`, `R0 = W = V = {0}`, `u = 0`: the
state stays at `0`, the output is `y₀ = 1`, and the next set of `observePropagation` (`PRad-E`,
`Nom-G`, `FRad-C`) is `{L}`, which misses `x₁ = 0` at every gain `L ≠ 0`; `D u` enters
`y` the same way. Read from the source, not run.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- With the output offset `k = 1`, the run `x ≡ 0` starts in `R0 = {0}` and has the output
`y₀ = 1`, and `x₁` is not in the observer's next set at any nonzero gain, at every order. -/
theorem LinearSysDT.observePropagation_output_offset_counterexample
    (gain : Zonotope (Vec ℝ 1) → Mat ℝ 1 1) (order : ℕ) :
    let sys : LinearSysDT ℝ 1 := ⟨1⟩
    let kOut : Vec ℝ 1 := fun _ => 1  -- `linsysDT.k`
    let x : ℕ → Vec ℝ 1 := fun _ _ => 0
    let R₀ : Zonotope (Vec ℝ 1) := Zonotope.ofPoint (x 0)
    let y : ℕ → Vec ℝ 1 := fun k => (1 : Mat ℝ 1 1) *ᵥ x k + kOut  -- `C = 1`, `v = 0`
    gain R₀ ≠ 0 →
    x 0 ∈ R₀.construct ∧ x 1 = sys.A *ᵥ x 0 + 0 ∧
      x 1 ∉ (sys.observePropagation 1 gain order (Zonotope.ofPoint 0) R₀ (Zonotope.ofPoint 0)
        (fun _ => 0) y 1).construct := by -- --- PROOF ---
  intro sys kOut x R₀ y hL
  refine ⟨Zonotope.mem_ofPoint _, ?_, ?_⟩
  · funext i
    simp [x, show (fun _ : Fin 1 => (0 : ℝ)) = 0 from rfl]
  · rintro ⟨β, -, hx⟩
    have h0 := congrFun hx 0
    simp [LinearSysDT.observePropagation, Zonotope.reduce, Zonotope.reduceGirard,
      Zonotope.plus, Zonotope.mtimes, Zonotope.ofPoint, R₀, y, x, kOut] at h0
    simp only [show (fun _ : Fin 1 => (0 : ℝ)) = 0 from rfl, Matrix.mulVec_zero] at h0
    apply hL
    ext i j
    fin_cases i; fin_cases j
    simp only [R₀, x, Zonotope.ofPoint, show (fun _ : Fin 1 => (0 : ℝ)) = 0 from rfl]
    simpa [Matrix.mulVec, dotProduct] using h0.symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
