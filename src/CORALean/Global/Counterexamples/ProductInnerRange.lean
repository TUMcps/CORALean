module

public import CORALean.Global.Tensor
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Interval.Set.Pi
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.Fin

@[expose] public section

/-!
# Per-component inner ranges sharing an existential input are no inner box

[1, Thm. 3] combines per-component AE extensions into a box inside the image only when
each input is existential in exactly one component (`π` a map from inputs to outputs).
For `f(x) = (x₀, x₀ + x₁/100)` on `[-1, 1]²` both components reach their intervals with
`x₀` existential — `[-1, 1]` and `[-0.99, 0.99]`, [1, Thm. 2] with `x₁` universal — but
the box of the two is not in the image: `(1, -0.99)` would need `x₁ = -199`. CORA's
`priv_reachInnerParallelotope` (`aux_innerApprox`) picks the existential input per
component independently and returns this box; `f` is the time-`1` flow of a linear
system, and the Jacobian center has condition number over `100`, so CORA skips the
preconditioning (read from the source, not run).

## References

* [1] E. Goubault and S. Putot. "Robust Under-Approximations and Application to
      Reachability of Non-Linear Control Systems With Disturbances". IEEE Control Systems
      Letters, 4(4):928-933, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set


-- =======================================  MAIN THEOREM  ======================================= --

/-- Each component's interval is inside its own range, their box is not inside the image. -/
theorem prod_inner_ranges_not_subset_image : -- --- CONCL ---
    let f : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun x => ![x 0, x 0 + x 1 / 100]
    let box : Set (Fin 2 → ℝ) := Icc (fun _ => -1) (fun _ => 1)
    Icc (-1) 1 ⊆ (fun x => f x 0) '' box ∧ Icc (-99 / 100) (99 / 100) ⊆ (fun x => f x 1) '' box ∧
      ¬ Icc ![-1, -99 / 100] ![1, 99 / 100] ⊆ f '' box := by -- --- PROOF ---
  intro f box
  refine ⟨fun z hz => ⟨![z, 0], ?_, by simp [f]⟩, fun z hz => ⟨![z, 0], ?_, by simp [f]⟩, ?_⟩
  · exact ⟨fun j => by fin_cases j <;> simp [hz.1], fun j => by fin_cases j <;> simp [hz.2]⟩
  · exact ⟨fun j => by fin_cases j <;> simp; linarith [hz.1],
      fun j => by fin_cases j <;> simp; linarith [hz.2]⟩
  -- `(1, -0.99)`: the first component forces `x₀ = 1`, the second then `x₁ = -199`
  · intro hsub
    obtain ⟨x, hx, hfx⟩ := hsub (show ![(1 : ℝ), -99 / 100] ∈ Icc ![-1, -99 / 100] ![1, 99 / 100]
      from ⟨fun j => by fin_cases j <;> norm_num, fun j => by fin_cases j <;> norm_num⟩)
    have h0 := congrFun hfx 0
    have h1 := congrFun hfx 1
    have hx1 := hx.1 1
    simp [f] at h0 h1 hx1
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
