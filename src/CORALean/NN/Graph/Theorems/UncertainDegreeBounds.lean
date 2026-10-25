module

public import CORALean.NN.Graph.Operations.Degree
public import CORALean.NN.Graph.Operations.DegreeSup
public import CORALean.NN.Graph.Theorems.DegreeAtEq
public import CORALean.NN.Graph.Theorems.Basic
public import CORALean.NN.Graph.Theorems.OneLeDegree

@[expose] public section

/-!
# The uncertain degree is bracketed, and never below `1`

Three bounds in one statement, because they are read together: the degree of a node at any
admissible choice of edge weights sits between `degree` and `degreeSup`, and `degree` is itself at
least `1`. The lower bound of `1` matters beyond arithmetic: [1] encloses `D̃^(-1/2)` over the
interval the other two bounds give, and an enclosure of `x ↦ x^(-1/2)` is total only away from zero;
the self-loop of `Ã = A + I` puts the whole interval at `1` or above (`GNN.one_le_degree`). The
other two are the edges: a weight of at least `0` on a nonnegative edge only adds, and a weight of
at most `1` adds at most `edgeDegree`.

## Inputs
* `A` – adjacency matrix
* `U` – uncertain edges
* `lam` – weights of the uncertain edges
* `j` – node

## Hypotheses
* `hlam` – edge weights lie in the unit interval
* `hA` – adjacency entries are nonnegative

## Conclusion
* the degree is at least one and lies between the fixed and maximal degrees

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The degree of an uncertain graph is bracketed by the two ends, and the lower
end is at least `1`. -/
theorem GNN.degreeAt_bounds (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N) (lam : Fin m → ℝ)
    (hlam : ∀ e, 0 ≤ lam e ∧ lam e ≤ 1) (hA : ∀ a b, 0 ≤ A a b) (j : Fin N) : -- --- CONCL ---
    1 ≤ GNN.degree A j ∧ GNN.degree A j ≤ GNN.degreeAt A U lam j
      ∧ GNN.degreeAt A U lam j ≤ GNN.degreeSup A U j := by -- --- PROOF ---
  rw [GNN.degreeAt_eq, GNN.degreeSup, GNN.edgeDegree]
  -- the self-loop already puts the lower end at `1`, which is `one_le_degree`
  refine ⟨GNN.one_le_degree A hA j, ?_, ?_⟩
  · -- a nonnegative weight on a nonnegative edge can only raise a degree
    have h : 0 ≤ ∑ e, ∑ i, lam e * GNN.edgeMat (U e) i j :=
      Finset.sum_nonneg fun e _ => Finset.sum_nonneg fun i _ =>
        mul_nonneg (hlam e).1 (GNN.edgeMat_nonneg (U e) i j)
    linarith
  · -- and a weight of at most `1` raises it by at most that edge's column sum
    have h : ∑ e, ∑ i, lam e * GNN.edgeMat (U e) i j ≤ ∑ e, ∑ i, GNN.edgeMat (U e) i j :=
      Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun i _ =>
        mul_le_of_le_one_left (GNN.edgeMat_nonneg (U e) i j) (hlam e).2
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
