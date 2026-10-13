import Mathlib.Data.List.Range
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Basic

/-!
# `supportConstraints`

[1, Def. 3], the support constraints of a problem `P` with constraints `F`: the constraints whose
removal lowers the optimal value, `w(P_l) < w(P)`. The problem is its value function `w`, the
optimal value of Problem 1 for each set `F ⊆ {1, …, N}` of constraints, as in [1, Alg. A*]
(`w(F)`). They are listed in increasing order, the order of the paper's `sc_l(F)`, `l = 1, …,
|sc(F)|`.
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

variable {N : ℕ} {β : Type} [LinearOrder β]


-- =====================================  MAIN DEFINITION  ====================================== --

def supportConstraints (w : Finset (Fin N) → β) (F : Finset (Fin N)) : List (Fin N) :=
  (List.finRange N).filter fun l => decide (l ∈ F ∧ w (F.erase l) < w F)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
