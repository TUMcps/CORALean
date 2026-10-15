module

public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeStarSetRowsIff
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A halfspace description as a star set

Exact: the star set whose generators are the identity, whose rows are the polytope's and whose
factor box is any certified box around the polytope denotes the polytope. The box only supplies the
bounds a star set must carry, and every point of the polytope is inside it.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.starSet_exact (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) :
    (P.starSet up lo).construct = P.construct := by -- --- PROOF ---
  ext x
  constructor
  · -- the identity generators make the factors the point itself
    rintro ⟨α, -, hrows, hxα⟩
    have hx : x = α := funext fun i => by simp [hxα i, HPolytope.starSet]
    exact hx ▸ (HPolytope.starRows_iff P α).mp hrows
  · intro hx
    refine ⟨x, fun k => ⟨?_, (up k).le x hx⟩, (HPolytope.starRows_iff P x).mpr hx,
      fun i => by simp [HPolytope.starSet]⟩
    have := (lo k).le x hx
    simp only [LinearMap.neg_apply, LinearMap.coe_proj, Function.eval] at this
    show -(lo k).val ≤ x k
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
