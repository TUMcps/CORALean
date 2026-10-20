module

public import CORALean.ContSet.VPolytope.Real.VPolytope
public import Mathlib.Analysis.Convex.Combination

@[expose] public section

/-!
# Moving the vertices moves the hull no further

If every vertex is displaced by something a convex set `D` admits, the hull of
the displaced ones sits inside the hull of the originals widened by `D` — the
displacement of a combination being the same combination of the displacements,
and `D` closed under that.

What a float layer owes when it stores rounded vertices, and the only fact about
vertex descriptions it needs.

## Inputs
* `k` – number of vertices
* `V` – vertices
* `W` – perturbed vertices
* `D` – convex set of perturbations

## Hypotheses
* `hD` – `D` convex
* `h` – each `V l - W l` lies in `D`

## Conclusion
* the hull of `V` lies in the hull of `W` plus `D`
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.construct_subset_add {k : ℕ} (V W : Fin k → α) {D : Set α}
    (hD : Convex ℝ D) (h : ∀ l, V l - W l ∈ D) : -- --- CONCL ---
    (VPolytope.mk k V).construct ⊆ (VPolytope.mk k W).construct + D := by -- --- PROOF ---
  rintro _ ⟨β, hβ, hsum, rfl⟩
  refine ⟨∑ l, β l • W l, ⟨β, hβ, hsum, rfl⟩, ∑ l, β l • (V l - W l), ?_, ?_⟩
  · exact hD.sum_mem (fun l _ => hβ l) hsum fun l _ => h l
  · -- membership in a set sum leaves a redex, which `rw` will not match
    show (∑ l, β l • W l) + ∑ l, β l • (V l - W l) = ∑ l, β l • V l
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [← smul_add, add_sub_cancel]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
