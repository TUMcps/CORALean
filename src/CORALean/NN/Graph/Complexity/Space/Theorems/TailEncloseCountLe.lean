module

public import CORALean.NN.Graph.Operations.TailEnclose

@[expose] public section

/-!
# The enclosed tail's count

[1, Alg. 1], lines 11 to 14, and [1, Thm. 1 (generators)]'s `(κ - 2κ') n_max`: a linear layer leaves
the number of generators alone and the enclosure of an activation adds at most its neurons ([1,
Prop. 1]). If layer `t` adds at most `e t`, the tail adds at most `∑ e t`.

## Inputs
* `T` – number of tail layers

## Hypotheses
* none

## Conclusion
* the tail adds at most the sum of what its layers add

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- The tail's generators, dependent and independent, grow by at most the sum of what its layers
add. -/
theorem GNN.tailEnclose_count_le (T : ℕ) : -- --- CONCL ---
    ∀ (d : ℕ → ℕ) (f : ∀ t, PolyZonotope (Vec ℝ (d t)) → PolyZonotope (Vec ℝ (d (t + 1))))
      (e : ℕ → ℕ) (_ : ∀ t S, (f t S).h + (f t S).q ≤ S.h + S.q + e t)
      (S : PolyZonotope (Vec ℝ (d 0))),
      (GNN.tailEnclose T d f S).h + (GNN.tailEnclose T d f S).q
        ≤ S.h + S.q + ∑ t ∈ Finset.range T, e t := by -- --- PROOF ---
  induction T with
  | zero => intro d f e he S; simp [GNN.tailEnclose]
  | succ T ih =>
    intro d f e he S
    have h1 := ih (fun t => d (t + 1)) (fun t => f (t + 1)) (fun t => e (t + 1))
      (fun t => he (t + 1)) (f 0 S)
    have h2 := he 0 S
    rw [Finset.sum_range_succ']
    show (GNN.tailEnclose T (fun t => d (t + 1)) (fun t => f (t + 1)) (f 0 S)).h
      + (GNN.tailEnclose T (fun t => d (t + 1)) (fun t => f (t + 1)) (f 0 S)).q ≤ _
    omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
