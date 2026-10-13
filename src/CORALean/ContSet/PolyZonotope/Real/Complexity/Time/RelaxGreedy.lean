module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxGreedy
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.RelaxExpMulti
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Prod

@[expose] public section

/-!
# `PolyZonotope.relaxGreedyCost`

Asserted, not proved, as the proof of [1, Thm. 2 (complexity)] counts it, for `h` dependent
generators, `q` independent ones, `n` dimensions and `p` factors. The graph of [1, Def. 5] checks
`h²` pairs at `p` factors each; its greedy subgraph is `h²` comparisons; the loop runs at most `h`
times, a node being processed once, each round updating the subgraph in `h` and applying [1, Thm. 1]
in `(h + q) n + h p`. The `(h + q) n` is moving the generators, which the model of
`Global/Cost.lean` does not charge; the paper's count is kept.

`Operations/RelaxGreedy.lean` searches for the leaf in `h²` per round instead of walking the tree,
so its own cost is not this one.

## [1, Thm. 2 (complexity)]: the greedy relaxation is `O((h + q) h n + h² p)`

The proof's arithmetic read off `relaxGreedyCost`: the count is `2 h² p + 2 h² + (h + q) h n`,
at most `4 ((h + q) h n + h² p)` once there is a factor (`p ≥ 1`). `IsBigO` along all four
sizes growing, as the theorem states it.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and Its
      Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What [1, Alg. 2] costs on `h` dependent and `q` independent generators, `n` dimensions and
`p` factors: the graph, its greedy subgraph, and `h` rounds of an update and a relaxation. -/
def PolyZonotope.relaxGreedyCost (h q n p : ℕ) : Cost :=
  ⟨h ^ 2 * p⟩ + ⟨h ^ 2⟩ + h • (⟨h⟩ + ⟨(h + q) * n + h * p⟩)


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The count itself, at most four times the bound, from `p = 1` on. -/
theorem aux_relaxGreedyCost_ops_le (h q n p : ℕ) (hp : 1 ≤ p) :
    (PolyZonotope.relaxGreedyCost h q n p).ops
      ≤ 4 * ((h + q) * h * n + h ^ 2 * p) := by -- --- PROOF ---
  simp only [PolyZonotope.relaxGreedyCost, Cost.ops_add, Cost.ops_smul]
  have h1 : h ^ 2 ≤ h ^ 2 * p := Nat.le_mul_of_pos_right _ hp
  have h2 : h * (h + ((h + q) * n + h * p)) = h ^ 2 + (h + q) * h * n + h ^ 2 * p := by ring
  rw [h2]
  linarith [h1, Nat.zero_le ((h + q) * h * n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 2 (complexity)]: `Alg. 2` is `O((h + q) h n + h² p)`. -/
theorem PolyZonotope.relaxGreedyCost_isBigO :
    (fun x : ℕ × ℕ × ℕ × ℕ => ((PolyZonotope.relaxGreedyCost x.1 x.2.1 x.2.2.1 x.2.2.2).ops : ℝ))
      =O[Filter.atTop]
        fun x : ℕ × ℕ × ℕ × ℕ =>
          (((x.1 + x.2.1) * x.1 * x.2.2.1 + x.1 ^ 2 * x.2.2.2 : ℕ) : ℝ) := by -- --- PROOF ---
  apply Asymptotics.IsBigO.of_bound 4
  filter_upwards [Filter.eventually_ge_atTop ((0, 0, 0, 1) : ℕ × ℕ × ℕ × ℕ)] with x hx
  have hp : 1 ≤ x.2.2.2 := hx.2.2.2
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact_mod_cast aux_relaxGreedyCost_ops_le x.1 x.2.1 x.2.2.1 x.2.2.2 hp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
