module

public import CORALean.HybridDynamics.Definitions.IdentHA

@[expose] public section

/-!
# The invariants of the identified automaton

[1, Sec. 3.3]: a leaf's invariant is the polytope of the inequalities along its path in the
decision tree, the right branch's `aᵀx ≥ b` written `-aᵀx ≤ -b`; `regions` lists them, one
per leaf, left before right.
Over ℝ, with no float layer: it states what the automaton is, for [1, Thm. 1]; CORA's
`priv_identify_decisionTree2automaton` also bloats the invariants by `1e-3`, not modelled.

## References

* [1] N. Kochdumper, M. A. Foughali, P. Habermehl and E. Asarin. "Robust Identification of
      Hybrid Automata from Noisy Data". In Proc. of the 28th ACM International Conference on
      Hybrid Systems: Computation and Control (HSCC), pp. 1-11, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 3.3]: the constraints along the path to each leaf. -/
def IdentHA.SplitTree.regions : IdentHA.SplitTree n → List (List (Vec ℝ n × ℝ))
  | .leaf => [[]]
  | .node a b l r => (l.regions.map ((a, b) :: ·)) ++ (r.regions.map ((-a, -b) :: ·))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
