module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Boxing generators by their signed row sums loses the enclosure

[1, Remark 2] reduces `⟨0, H_k⟩` to `[H⁺, H⁻]`, keeping the `q - n_x` largest columns as `H⁺`
and replacing the rest by the diagonal `H⁻_{i,i} = Σ_j H̃_{i,j}`, and claims `⟨0, H_k⟩ ⊆ ⟨0, H̄_k⟩`.
Without absolute values the row sum can cancel: `H = [1  -1]` in one dimension, `q = n_x = 1`,
gives `H⁻ = 0`, and `⟨0, [0]⟩ = {0}` misses `2 = 1·1 + (-1)·(-1)`. With `|H̃_{i,j}|`, the
interval hull of the boxed columns, the inclusion holds at every split (`Zonotope.reduceBy_outer`).

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduce_rowSum_counterexample :
    let Z : Zonotope (Vec ℝ 1) := ⟨2, 0, ![fun _ => 1, fun _ => -1]⟩
    let Zred : Zonotope (Vec ℝ 1) := ⟨1, 0, fun _ i => ∑ l, Z.G l i⟩
    ¬ Z.construct ⊆ Zred.construct := by -- --- PROOF ---
  intro Z Zred hsub
  -- `2 ∈ Z`, at the coefficients `(1, -1)`
  have hmem : (fun _ => 2 : Vec ℝ 1) ∈ Z.construct :=
    ⟨![1, -1], ⟨fun j => by fin_cases j <;> simp, by
      funext i; simp [Z, Fin.sum_univ_two]; norm_num⟩⟩
  -- but the reduced zonotope is `{0}`
  obtain ⟨β, -, hβ⟩ := hsub hmem
  have := congrFun hβ 0
  simp [Zred, Z, Fin.sum_univ_two] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
