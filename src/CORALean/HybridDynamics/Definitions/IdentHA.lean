module

public import CORALean.Global.Tensor
public import CORALean.HybridDynamics.Operations.IdentPolytope
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The identified automaton's sets and its decision tree

[1, Def. 2]: a polytope `⟨C, d⟩_P = {x | C x ≤ d}`, written as its list of rows `(cᵢ, dᵢ)`
(`IdentPolytope`);
[1, Def. 3]: a constrained hyperplane `⟨a, b, C, d⟩_H = {x | aᵀx = b ∧ C x ≤ d}`. A
`SplitTree` is the decision tree of the paper's second step, with only what [1, Sec. 3.3]
reads off it: each inner node splits by a hyperplane, `aᵀx ≤ b` left and `≥ b` right; the
library of partitions and the criteria that chose the splits are the learning's.

## Inputs
* `a` – hyperplane normal
* `b` – hyperplane offset
* `cs` – polytope rows

## Output
* points on the hyperplane inside the polytope

## References

* [1] N. Kochdumper, M. A. Foughali, P. Habermehl and E. Asarin. "Robust Identification of
      Hybrid Automata from Noisy Data". In Proc. of the 28th ACM International Conference on
      Hybrid Systems: Computation and Control (HSCC), pp. 1-11, 2025.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Def. 3]: `{x | aᵀx = b ∧ C x ≤ d}`. -/
def IdentHA.conHyperplane (a : Vec ℝ n) (b : ℝ) (cs : List (Vec ℝ n × ℝ)) : Set (Vec ℝ n) :=
  {x | a ⬝ᵥ x = b ∧ x ∈ (IdentHA.polytope cs).construct}

/-- A decision tree of hyperplane splits: left `aᵀx ≤ b`, right `aᵀx ≥ b`. -/
inductive IdentHA.SplitTree (n : ℕ) where
  | leaf : IdentHA.SplitTree n
  | node (a : Vec ℝ n) (b : ℝ) (left right : IdentHA.SplitTree n) : IdentHA.SplitTree n

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
