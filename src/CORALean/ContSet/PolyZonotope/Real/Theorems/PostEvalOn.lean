import CORALean.ContSet.PolyZonotope.Real.Operations.PostBox
import CORALean.ContSet.PolyZonotope.Real.Theorems.MtimesEvalOn
import CORALean.ContSet.PolyZonotope.Real.Theorems.PlusEvalOn
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceEvalOn

/-!
# [1, Lemma 4]: the post operator preserves dependencies

[1, (19)] at the post operator of its Alg. 1 — lines 11 and 12, propagate, add
the step's inputs and abstraction errors, reduce — over polynomial zonotopes:
what the operator reaches from a parameterized subset of `X` lies inside the
evaluation of what it reaches from all of `X`.

[1] proves this by reading the operator as `A(R) ⊕ B(R, Ψ)` and appealing to
properties it asserts of its primitives and never proves. Here each of the three
is discharged: `mtimes_evalOn` is the propagation, exactly; `plus_evalOn` is
[1, (23)], with the added set free in its own fresh factors rather than assumed
to have none; and `reduce_evalOn` is the reduction, which [1]'s Table 1 leaves
out altogether.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 4]: one post step of `X` evaluated at `B`, propagated and widened
by `U`, lies inside the step's own result evaluated at `postBox`. -/
theorem PolyZonotope.post_evalOn (M : Mat ℝ n n) (X U : PolyZonotope (Vec ℝ n)) (o : ℕ)
    {B : Set (Fin X.p → ℝ)} (hB : ∀ a ∈ B, ∀ k, |a k| ≤ 1) :
    (M *ᵥ ·) '' X.evalOn B + U.construct
      ⊆ (((PolyZonotope.mtimes M X).plus U).reduce o).evalOn
        (PolyZonotope.postBox M X U o B) := by -- --- PROOF ---
  have hplus : (M *ᵥ ·) '' X.evalOn B + U.construct
      ⊆ ((PolyZonotope.mtimes M X).plus U).evalOn
        (PolyZonotope.plusBox (PolyZonotope.mtimes M X) U B) := by
    rw [← PolyZonotope.mtimes_evalOn]
    exact PolyZonotope.plus_evalOn _ _ _
  -- the reduction, whose sub-box is what `postBox` composes onto `plus`'s
  refine hplus.trans (PolyZonotope.reduce_evalOn _ o ?_)
  rintro a ⟨ha₁, ha₂⟩
  exact Fin.addCases (fun k => hB _ ha₁ k) (fun k => ha₂ k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
