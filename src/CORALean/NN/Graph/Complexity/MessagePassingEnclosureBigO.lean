import CORALean.Global.Mathlib
import CORALean.NN.Graph.Complexity.MessagePassingEnclosure

/-!
# `GNN.messagePassingEnclosure`'s count is `O(m³)` in the uncertain edges

[1, Prop. 4] in its own notation. Not a bare arithmetic fact about the cubic in
`MessagePassingEnclosure.lean`, but one tied to the enclosure through a family
of edge sets growing with `m`, the node count and the relaxation held fixed —
which is what puts the node count in the constant and leaves the growth to the
edges, as [1, Thm. 1] then composes it.

`Asymptotics.IsBigO.of_bound` closes it: it asks for domination by a fixed
constant `∀ᶠ x in l`, and `messagePassingEnclosure_h_le` is that constant from
one uncertain edge upwards.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The enclosure of [1, Prop. 4] grows cubically in the number of uncertain
edges, at a fixed graph size. -/
theorem GNN.messagePassingEnclosure_h_isBigO (R : Relaxation invSqrt) (A : Mat ℝ N N)
    (U : ∀ m : ℕ, Fin m → Fin N × Fin N) :
    (fun m : ℕ => (((GNN.messagePassingEnclosure R A (U m)).h : ℕ) : ℝ))
      =O[Filter.atTop] fun m : ℕ => (m : ℝ) ^ 3 := by -- --- PROOF ---
  apply Asymptotics.IsBigO.of_bound ((((N + 2) * (N + 2) + 1) * (N + 2) : ℕ) : ℝ)
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  -- the bound is a statement about naturals, so the cast is the last step
  have h := GNN.messagePassingEnclosure_h_le R A (U m) hm
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact_mod_cast h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
