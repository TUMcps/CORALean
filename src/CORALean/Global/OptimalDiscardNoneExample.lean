module

public import CORALean.Global.OptimalDiscardLe
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Fin

@[expose] public section

/-!
# Algorithm A* can have nothing to return

[1, Thm. 2], [1, Alg. A*]: on four constraints of the one-variable program `min z` subject to
`z ≥ 0` and `z ≥ c_t` with `c = (1, 0, 0, 0)`, whose value `w(F)` is `1` if `F` holds constraint `0`
and `0` otherwise, the value only grows with the constraints and every problem is non-degenerate
(`w(sc(F)) = w(F)`). Only constraint `0` is ever a support constraint, so `discardTree` is empty at
level `2` and `optimalDiscard` returns `none` for `k = 2 < N - d = 3`, though the two constraints
`{1, 2}` have the least possible value, `0`. The printed theorem takes it for granted that every
problem of the tree has a support constraint; `optimalDiscard_le` makes it a hypothesis.

## References

* [1] M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica, 45(2):382-392, 2009.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem optimalDiscard_none_example :
    let w : Finset (Fin 4) → ℕ := fun F => if (0 : Fin 4) ∈ F then 1 else 0
    (∀ G H : Finset (Fin 4), G ⊆ H → w G ≤ w H) ∧
    (∀ G : Finset (Fin 4), w (supportConstraints w G).toFinset = w G) ∧
    optimalDiscard w Finset.univ 2 = none ∧
    ∃ F : Finset (Fin 4), F.card = 2 ∧ w F = 0 := by
  intro w
  exact ⟨of_decide_eq_true rfl, of_decide_eq_true rfl, of_decide_eq_true rfl,
    {1, 2}, of_decide_eq_true rfl, of_decide_eq_true rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
