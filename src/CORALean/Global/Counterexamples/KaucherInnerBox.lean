module

public import CORALean.Global.KaucherInner
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

/-!
# The box of the component-wise inner ranges is not inside the reachable set

[1, Eq. 18], Step 3 of [1, Alg. 1], calls `pro ]z[` an inner approximation of the set of
solutions; what [1, Thm. 1] gives is one component at a time (`kaucherInnerStep_inner`),
and the box of the components is not inside the set. For the time-`1` flow
`φ(x) = ((x₀ + x₁)/2, (x₁ - x₀)/2)` of a linear system (a rotation by `π/4` scaled by
`1/√2`) on `[-1, 1]²`, with `z̃₀ = 0` and exact enclosures, both components of (18) are
`[-1, 1]`, while the reachable set is the diamond `|y₀| + |y₁| ≤ 1`: `(1, 1)` is not
reached. CORA's `priv_reachInnerProjection` stores that box as its inner approximation
(read from the source, not run).

## Inputs
* none

## Hypotheses
* none

## Conclusion
* both components are the unit interval but their box is not in the reachable set

## References

* [1] E. Goubault and S. Putot. "Forward Inner-Approximated Reachability of Non-Linear
      Continuous Systems". In Proc. of the 20th International Conference on Hybrid Systems:
      Computation and Control (HSCC), pp. 1-10, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- Both components of (18) are `[-1, 1]` for the rotated flow, and their box is not in its
image. -/
theorem kaucherInnerStep_box_counterexample : -- --- CONCL ---
    let φ : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun x => ![(x 0 + x 1) / 2, (x 1 - x 0) / 2]
    let J : Mat ℝ 2 2 := !![1 / 2, 1 / 2; -1 / 2, 1 / 2]
    let s := kaucherInnerStep (fun _ => 0) (fun _ => 0) J J (fun _ => -1) (fun _ => 1)
      (fun _ => 0)
    (∀ i, s i = (1, -1)) ∧ ¬ Icc (fun i => (s i).2) (fun i => (s i).1)
      ⊆ φ '' Icc (fun _ => -1) (fun _ => 1) := by -- --- PROOF ---
  intro φ J s
  have hs : ∀ i, s i = (1, -1) := by
    intro i
    fin_cases i <;> norm_num [s, J, kaucherInnerStep, kaucherMulDualZ, Fin.sum_univ_two]
  refine ⟨hs, fun hsub => ?_⟩
  -- `(1, 1)` would need `x₁ = 2`
  obtain ⟨x, hx, hφx⟩ := hsub (show (fun _ => (1 : ℝ)) ∈ Icc (fun i => (s i).2) (fun i => (s i).1)
    from ⟨fun i => by simp only [hs i]; norm_num, fun i => by simp only [hs i]; norm_num⟩)
  have h0 := congrFun hφx 0
  have h1 := congrFun hφx 1
  have hx1 := hx.2 1
  simp [φ] at h0 h1 hx1
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
