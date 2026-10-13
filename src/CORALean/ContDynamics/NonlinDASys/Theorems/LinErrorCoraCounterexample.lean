module

public import CORALean.ContDynamics.NonlinDASys.Operations.LinErrorCora
public import CORALean.ContDynamics.NonlinDASys.Theorems.LinErrorOuter

@[expose] public section

/-!
# CORA's `nonlinDASys` linearization error misses the error

`NonlinDASys.linErrorCora`, CORA's `error_mid + error_rad` with `+ CF_inv` on the algebraic part,
against [1, Cor. 1] (`NonlinDASys.linError`) with `- CF⁻¹`. The system `ẋ = y`, `0 = y - x²`
(index 1, `F = 1`), linearized at `z* = 0`: `A = 0`, `C = 1`, `D = 0`, so `C F⁻¹ = 1`, and the
Hessians are `Hᵈ = 0` and `Hᵃ = -2` in the `x` direction, nothing in `y` (the deviation
zonotope is taken over `x` alone, `R^z_Δ = [-1, 1]`). On the constraint `y = x²`, so `ẋ = x²`
while the linearization gives `0`: the error at `x = 1` is `1`. [1, Cor. 1] holds it, `½ (σ -
CF⁻¹φ) = ½ (0 - (-2)) = 1`; CORA's set is `½ (0 + (-2) [0, 1]) = [-1, 0]` and does not.

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- The linearization error `½ (σ - CF⁻¹φ) = 1` of `ẋ = y`, `0 = y - x²` at `z* = 0`, `ν = 1`,
lies in [1, Cor. 1]'s set and not in CORA's. -/
theorem NonlinDASys.linErrorCora_counterexample :
    (1 / 2 : ℝ) • ((fun _ : Fin 1 => (![1] : Vec ℝ 1) ⬝ᵥ ((0 : Mat ℝ 1 1) *ᵥ ![1]))
        - (1 : Mat ℝ 1 1) *ᵥ (fun _ : Fin 1 => (![1] : Vec ℝ 1) ⬝ᵥ (!![-2] *ᵥ ![1])))
      ∈ (NonlinDASys.linError (p := 1) (q := 1) 0 0 (fun _ => !![-2]) 0 1
          ⟨1, 0, fun _ => ![1]⟩).construct ∧
    (1 / 2 : ℝ) • ((fun _ : Fin 1 => (![1] : Vec ℝ 1) ⬝ᵥ ((0 : Mat ℝ 1 1) *ᵥ ![1]))
        - (1 : Mat ℝ 1 1) *ᵥ (fun _ : Fin 1 => (![1] : Vec ℝ 1) ⬝ᵥ (!![-2] *ᵥ ![1])))
      ∉ (NonlinDASys.linErrorCora (p := 1) (q := 1) 0 0 (fun _ => !![-2]) 0 1
          ⟨1, 0, fun _ => ![1]⟩).construct := by -- --- PROOF ---
  refine ⟨NonlinDASys.linError_outer _ _ _ _ _ _ (by simp) (by simp)
    ⟨fun _ => 1, fun _ => by simp, by funext i; fin_cases i; simp⟩, ?_⟩
  -- the error is `1`
  have hP : (1 / 2 : ℝ) • ((fun _ : Fin 1 => (![1] : Vec ℝ 1) ⬝ᵥ ((0 : Mat ℝ 1 1) *ᵥ ![1]))
      - (1 : Mat ℝ 1 1) *ᵥ (fun _ : Fin 1 => (![1] : Vec ℝ 1) ⬝ᵥ (!![-2] *ᵥ ![1])))
      = fun _ => 1 := by
    funext i
    simp [dotProduct, mulVec]
  rw [hP]
  -- every point of CORA's set has its coordinate at most `0`
  rintro ⟨β, hβ, hx⟩
  change _ = _ + ∑ j : Fin 5, β j • _ at hx
  have h0 := congrFun hx 0
  simp [NonlinDASys.linErrorCora, Zonotope.quadMap, Zonotope.plus, Zonotope.mtimes,
    Interval.zonotope, Zonotope.absBound, Fin.sum_univ_succ, dotProduct, mulVec, Fin.append,
    Fin.addCases] at h0
  have hb := abs_le.mp (hβ (1 : Fin 5))
  -- the pair generator of a one-generator zonotope is `0`
  split_ifs at h0 with hc
  · exact absurd hc (by
      rw [Subsingleton.elim (finProdFinEquiv.symm (0 : Fin (1 * 1))).2
        (finProdFinEquiv.symm (0 : Fin (1 * 1))).1]
      exact lt_irrefl _)
  · linarith [hb.1, hb.2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
