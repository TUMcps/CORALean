module

public import CORALean.ContSet.PolyZonotope.Real.Operations.IsExpEdgeAt
public import CORALean.ContSet.PolyZonotope.Real.Theorems.RelaxExpEvenOuter

@[expose] public section

/-!
# An edge of the generator graph recenters

What `[1, Def. 5]` is for, and the only thing soundness asks of a selection rule.
`relaxExpEven_outer` wants three facts the drift's one-sidedness rests on, and `[1, Thm. 1]`
states only one; an edge supplies two (the columns agree off `k₀`, the exponent there falls) and
turns the third, evenness of the survivor's exponent, into evenness of the relaxed column
alone: equal parity to an even exponent is even, and `E_{k₀,j} = 0` is even outright. CORA gates
the halving on exactly this pair of tests. The relaxed column's evenness stays a hypothesis.

## Inputs
* `pZ` – polynomial zonotope
* `part` – split with two selected generators
* `η` – exponent threshold
* `k₀` – factor index

## Hypotheses
* `hedge` – the pair is a relaxable edge at that factor
* `heven` – first generator has even exponents

## Conclusion
* the set is contained in the result

## References

* [1] [T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and Its Applications
      in Formal Neural Network Verification". Proceedings of the AAAI Conference on Artificial
      Intelligence, 2024.](../../../../../../references/2024/ladner-aaai-exponent-relaxation.md)
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Merging along an edge of the generator graph over-approximates with the
center shifted, given that the relaxed column is even. -/
theorem PolyZonotope.relaxExpEven_outer_of_edge (pZ : PolyZonotope α)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) {η : ℕ} {k₀ : Fin pZ.p}
    (hedge : PolyZonotope.IsExpEdgeAt pZ.E η k₀ (part.right 0) (part.right 1))
    (heven : ∀ k, Even (pZ.E k (part.right 0))) : -- --- CONCL ---
    pZ.construct ⊆ (pZ.relaxExpEven part k₀).construct := by -- --- PROOF ---
  obtain ⟨hsim, hpar, -, hlt⟩ := hedge
  -- the survivor's exponent is even: matching the parity of an even one, or zero
  have hevenj : Even (pZ.E k₀ (part.right 1)) := by
    rcases hpar with hpar | hpar
    · refine Nat.even_iff.mpr ?_
      rw [← hpar]
      exact Nat.even_iff.mp (heven k₀)
    · exact Nat.even_iff.mpr (by rw [hpar])
  exact pZ.relaxExpEven_outer part k₀ hsim heven hevenj (le_of_lt hlt)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
