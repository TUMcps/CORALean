module

public import CORALean.ContSet.VPolytope.Real.Operations.LeOfForallLe
public import CORALean.Global.LinProg.LinProg
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# A vertex description answers a linear program without solving one

The maximum over a finite vertex list is the support value, attained rather
than merely approached. This is the reason the two representations are kept
apart, and the reason the conversion between them is cheap in exactly one
direction.

The value [1, Def. 3] gives the vertex form, `max_i ℓᵀvᵢ`, as a certificate;
`Theorems.SupportBoundAttained` is where it becomes that paper's equality.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Noncomputable only in the supremum: over a finite vertex list the value is a
maximum, and the float layer computes it as one. -/
noncomputable def VPolytope.supportBound (P : VPolytope α) (c : α →ₗ[ℝ] ℝ) :
    SupportBound P.construct c where
  val := ⨆ l, c (P.V l)
  -- the function spelt out: `le_ciSup` cannot guess it from the goal
  le _ hx := P.le_of_forall_le c
    (fun l => le_ciSup (f := fun l => c (P.V l)) (Set.finite_range _).bddAbove l) hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
