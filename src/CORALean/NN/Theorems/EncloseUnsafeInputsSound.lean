module

public import CORALean.NN.Theorems.EncloseUnsafeInputsOuter

@[expose] public section

/-!
# Verifying or falsifying the refined input set decides the original

[1, Cor. 1]: with `X|_{C≤d}` the refinement of [1, Prop. 2], `Φ(X|_{C≤d}) ∩ U = ∅` iff
`Φ(X) ∩ U = ∅`, and some `x ∈ X|_{C≤d}` has `Φ(x) ∈ U` iff some `x ∈ X` has. Both directions
follow from `{x ∈ X | Φ(x) ∈ U} ⊆ X|_{C≤d} ⊆ X` alone, so it needs what that needs: the
approximation errors bound each layer pointwise (`SetBasedNet.IsRelaxationOf`).

## Inputs
* `N` – set-based network
* `Φ` – the function it encloses
* `X` – input zonotope
* `A` – unsafe-set matrix
* `b` – unsafe-set offset

## Hypotheses
* `hN` – `N` relaxes `Φ` with pointwise approximation errors

## Conclusion
* safety and falsification of `X|_{C≤d}` are those of `X`

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for Neural
      Network Verification". International Conference on Learning Representations, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n k p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Cor. 1]: the refined input set is safe, or falsifiable, exactly when `X` is. -/
theorem SetBasedNet.encloseUnsafeInputs_sound {N : SetBasedNet n k} {Φ : Vec ℝ n → Vec ℝ k}
    (hN : N.IsRelaxationOf Φ) (X : Zonotope (Vec ℝ n)) (A : Mat ℝ p k)
    (b : Vec ℝ p) : -- --- CONCL ---
    (Φ '' (N.encloseUnsafeInputs X A b).construct ∩ (HPolytope.ineqs A b).construct = ∅ ↔
      Φ '' X.construct ∩ (HPolytope.ineqs A b).construct = ∅) ∧
    ((∃ x ∈ (N.encloseUnsafeInputs X A b).construct, Φ x ∈ (HPolytope.ineqs A b).construct) ↔
      ∃ x ∈ X.construct, Φ x ∈ (HPolytope.ineqs A b).construct) := by -- --- PROOF ---
  obtain ⟨hunsafe, hsub⟩ := N.encloseUnsafeInputs_outer hN X A b
  -- every unsafe input of `X` is in `X|_{C≤d}`, and `X|_{C≤d} ⊆ X`
  have hex : (∃ x ∈ (N.encloseUnsafeInputs X A b).construct,
      Φ x ∈ (HPolytope.ineqs A b).construct) ↔
      ∃ x ∈ X.construct, Φ x ∈ (HPolytope.ineqs A b).construct :=
    ⟨fun ⟨x, hx, hU⟩ => ⟨x, hsub hx, hU⟩, fun ⟨x, hx, hU⟩ => ⟨x, hunsafe ⟨hx, hU⟩, hU⟩⟩
  refine ⟨?_, hex⟩
  simp only [Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, Set.mem_image]
  constructor
  · rintro h y ⟨⟨x, hx, rfl⟩, hU⟩
    exact h (Φ x) ⟨⟨x, hunsafe ⟨hx, hU⟩, rfl⟩, hU⟩
  · rintro h y ⟨⟨x, hx, rfl⟩, hU⟩
    exact h (Φ x) ⟨⟨x, hsub hx, rfl⟩, hU⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
