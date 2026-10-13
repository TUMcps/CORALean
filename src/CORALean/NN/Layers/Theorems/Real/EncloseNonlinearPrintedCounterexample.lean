import CORALean.NN.Layers.Definitions.EncloseNonlinearPrinted
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi

/-!
# Alg. 1 as printed does not enclose the image

[1, Alg. 1] with lines 6 and 7 as printed, at `ϕ(x) = x + 1` on the box `[-1, 1]`, `H = ⟨0, [1]⟩`:
the secant slope is `1` and `e = ē = 1`, so the output is `⟨2, [1, 0]⟩ = [1, 3]`, which misses
`ϕ(-1) = 0`. The enclosure with the midpoint added once is `approxErrorRelaxation`.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem encloseNonlinearPrinted_counterexample :
    ∃ H : Zonotope (Vec ℝ 1), ∃ x ∈ H.construct,
      (fun _ : Fin 1 => (fun t : ℝ => t + 1) (x 0)) ∉
        (encloseNonlinearPrinted (fun t => t + 1) H).construct := by -- --- PROOF ---
  let H : Zonotope (Vec ℝ 1) := ⟨1, 0, fun _ _ => 1⟩
  have hl : H.c 0 - ∑ j, |H.G j 0| = -1 := by simp [H]
  have hu : H.c 0 + ∑ j, |H.G j 0| = 1 := by simp [H]
  -- the secant slope is 1, so `ϕ - p` is the constant 1 and `e = ē = 1`
  have hm : secantSlope (fun t : ℝ => t + 1) (-1) 1 = 1 := by norm_num [secantSlope]
  have he : approxErrorLow (fun t : ℝ => t + 1) (fun x => 1 * x) (-1) 1 = 1 := by
    have : (fun x : ℝ => (x + 1) - 1 * x) = fun _ => 1 := by funext x; ring
    simp [approxErrorLow]
  have he' : approxErrorUp (fun t : ℝ => t + 1) (fun x => 1 * x) (-1) 1 = 1 := by
    have : (fun x : ℝ => (x + 1) - 1 * x) = fun _ => 1 := by funext x; ring
    simp [approxErrorUp]
  refine ⟨H, fun _ => -1, ⟨fun _ => -1, fun _ => by simp, by ext i; simp [H]⟩, ?_⟩
  rintro ⟨β, hβ, h⟩
  have h0 := congrFun h 0
  simp only [encloseNonlinearPrinted, hl, hu, hm, he, he'] at h0
  -- the point is `2 + β₀ · 1 + β₁ · 0`, at least `1`
  have h1 := hβ (Fin.castAdd 1 (0 : Fin 1))
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply] at h0
  erw [Fin.sum_univ_two] at h0
  simp [H, Fin.append, Fin.addCases, abs_le] at h0 h1
  nlinarith [h1.1, h1.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
