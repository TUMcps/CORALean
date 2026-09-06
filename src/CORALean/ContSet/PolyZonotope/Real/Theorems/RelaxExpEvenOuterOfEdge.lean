import CORALean.ContSet.PolyZonotope.Real.Operations.ExpEdgeAt
import CORALean.ContSet.PolyZonotope.Real.Theorems.RelaxExpEvenOuter

/-!
# An edge of the generator graph recentres

What `[1, Def. 5]` is for, and the only thing soundness ever asks of a selection
rule. `relaxExpEven_outer` wants three facts the drift's one-sidedness rests on,
and `[1, Thm. 1]` states only one of them; an edge supplies two — the columns
agree off `k₀`, and the exponent there falls — and turns the third, evenness of
the survivor's exponent, into evenness of the relaxed column alone.

That last step is the parity condition doing its second job: equal parity to an
even exponent is even, and the alternative `E_{k₀,j} = 0` is even outright. CORA
gates the halving on exactly this pair of tests, one in the graph and one at the
merge, which is how the hypothesis went missing from `[1, Thm. 1]` on paper.

The evenness of the relaxed column stays a hypothesis: it is a fact about the
whole column, which no edge of `[1, Def. 5]` reads.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Merging along an edge of the generator graph over-approximates with the
centre shifted, given that the relaxed column is even. -/
theorem PolyZonotope.relaxExpEven_outer_of_edge (PZ : PolyZonotope α)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) {η : ℕ} {k₀ : Fin PZ.p}
    (hedge : PolyZonotope.ExpEdgeAt PZ.E η k₀ (part.right 0) (part.right 1))
    (heven : ∀ k, Even (PZ.E k (part.right 0))) :
    PZ.construct ⊆ (PZ.relaxExpEven part k₀).construct := by
  obtain ⟨hsim, hpar, -, hlt⟩ := hedge
  -- the survivor's exponent is even: matching the parity of an even one, or zero
  have hevenj : Even (PZ.E k₀ (part.right 1)) := by
    rcases hpar with hpar | hpar
    · refine Nat.even_iff.mpr ?_
      rw [← hpar]
      exact Nat.even_iff.mp (heven k₀)
    · exact Nat.even_iff.mpr (by rw [hpar])
  exact PZ.relaxExpEven_outer part k₀ hsim heven hevenj (le_of_lt hlt)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
