module

public import CORALean.Global.SupportConstraints

@[expose] public section

/-!
# `discardTree`

The tree of problems of [1, Alg. A*], level by level: the root is the full constraint set `D`, and
each problem at level `i` has a child for each of its support constraints, the problem without it.
Step 1 of the algorithm, `D^{M_{i+1}}_{N-i-1} := D^h_{N-i} - sc_l(D^h_{N-i})` for `h = 1, …, M_i`
and `l = 1, …, |sc(D^h_{N-i})|`, as a list, so that `M_i` is its length; a problem reached by two
removal orders appears twice.
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

def discardTree (w : Finset (Fin N) → β) (D : Finset (Fin N)) : ℕ → List (Finset (Fin N))
  | 0 => [D]                                                              -- D¹_N := D_N, M₀ := 1
  | i + 1 => (discardTree w D i).flatMap fun F =>                         -- Step 1, level i + 1
      (supportConstraints w F).map F.erase

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
