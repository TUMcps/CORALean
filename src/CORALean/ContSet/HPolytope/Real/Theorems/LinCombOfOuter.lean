module

public import CORALean.ContSet.HPolytope.Real.Operations.LinComb
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic

@[expose] public section

/-!
# The certified convex combination encloses

The same line as `plusOf_outer` at a different composition of certificates:
`ofBounds` says exactly what the bounds handed to it say, and the bounds were
composed to speak about the segments between the two sets.

The enclosure claimed by [1, Eq. 31].

## Inputs
* `P₁` – H-polytope
* `P₂` – H-polytope
* `Aq` – family indexed by `Fin q`
* `u₁` – a support bound of `P₁.construct` along each row
* `u₂` – a support bound of `P₂.construct` along each row

## Hypotheses
* none

## Conclusion
* the certified convex combination encloses
## References

* [1] [M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". Proceedings of the 11th Int. Workshop on Applied Verification for
      Continuous and Hybrid Systems,
      2024.](../../../../../../references/2024/wetzlinger-arch-polyhedral-operations.md)
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]
variable {q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.linCombOf_outer {P₁ P₂ : HPolytope α} (Aq : Fin q → (α →ₗ[ℝ] ℝ))
    (u₁ : ∀ i, SupportBound P₁.construct (Aq i))
    (u₂ : ∀ i, SupportBound P₂.construct (Aq i)) :
    Set.linComb P₁.construct P₂.construct ⊆ (HPolytope.linCombOf Aq u₁ u₂).construct :=
  HPolytope.subset_ofBounds _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
