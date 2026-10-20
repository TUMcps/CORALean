module

public import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialIdentE
public import CORALean.NN.Graph.Operations.AdjAt
public import CORALean.NN.Graph.Operations.UncertainAdj
public import CORALean.NN.Graph.Theorems.SmulEdgeHalf

@[expose] public section

/-!
# The uncertain adjacency is exactly the adjacencies the edges allow

[1]'s uncertain graph structure as an equality and not an enclosure: every adjacency obtained by
weighting the uncertain edges anywhere between `0` and `1` is a point of `uncertainAdj`, and every
point of `uncertainAdj` is one such adjacency, because the edges are put in as factors, one each.
Both inclusions are the same affine change of variable, `λ = (1 + α)/2` coming back and `α = 2λ - 1`
going out. `monomial_identE` collapses each monomial to its own factor, so no exponent ever enters;
the independent block is empty and takes no part.

## Inputs
* `A` – adjacency matrix
* `U` – uncertain edges

## Hypotheses
* none

## Conclusion
* the set is exactly the adjacencies at all admissible edge weights

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open PolyZonotope

variable {N m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1]'s uncertain adjacency loses nothing: its factors are the edge weights,
rescaled to the unit interval around zero. -/
theorem GNN.uncertainAdj_exact (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N) :
    (fun lam => GNN.adjAt A U lam) '' {lam | ∀ e, 0 ≤ lam e ∧ lam e ≤ 1}
      = (GNN.uncertainAdj A U).construct := by -- --- PROOF ---
  -- one adjacency written at the factors producing it, which is both inclusions
  have hpt : ∀ (lam a : Fin m → ℝ) (b : Fin (GNN.uncertainAdj A U).q → ℝ),
      (∀ e, lam e = (1 + a e) / 2) →
      GNN.adjAt A U lam = (GNN.uncertainAdj A U).c
          + ∑ i, monomial (GNN.uncertainAdj A U).E a i • (GNN.uncertainAdj A U).G i
          + ∑ j, b j • (GNN.uncertainAdj A U).GI j := by
    intro lam a b hla
    have hlam : lam = fun e => (1 + a e) / 2 := funext hla
    subst hlam
    -- the independent block is empty, so it contributes nothing
    have hb : ∑ j, b j • (GNN.uncertainAdj A U).GI j = (0 : Mat ℝ N N) :=
      Finset.sum_eq_zero fun j _ => j.elim0
    rw [hb, add_zero]
    show A + ∑ e, ((1 + a e) / 2) • GNN.edgeMat (U e)
        = (A + ∑ e, (1/2 : ℝ) • GNN.edgeMat (U e))
          + ∑ e, monomial (identE m) a e • ((1/2 : ℝ) • GNN.edgeMat (U e))
    -- each generator is scaled by its own factor, so the two sums merge
    simp only [monomial_identE]
    rw [add_assoc, ← Finset.sum_add_distrib]
    exact congrArg (A + ·) (Finset.sum_congr rfl fun e _ =>
      GNN.smul_edge_half (a e) (GNN.edgeMat (U e)))
  apply Set.eq_of_subset_of_subset
  -- out: a weight `λ` is the factor `2λ - 1`, and its bounds are that factor's
  · rintro _ ⟨lam, hlam, rfl⟩
    refine ⟨fun e => 2 * lam e - 1, fun _ => 0, fun k => ?_, fun _ => ?_, ?_⟩
    · rw [abs_le]
      exact ⟨by linarith [(hlam k).1], by linarith [(hlam k).2]⟩
    · rw [abs_zero]
      exact zero_le_one
    · exact hpt lam _ _ fun e => by ring
  -- back: a factor `α` is the weight `(1 + α)/2`, which the same bounds give
  · rintro x ⟨a, b, ha, _, hx⟩
    refine ⟨fun e => (1 + a e) / 2, fun e => ?_, ?_⟩
    · have h := abs_le.mp (ha e)
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · rw [hx]
      exact hpt _ a b fun e => rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
