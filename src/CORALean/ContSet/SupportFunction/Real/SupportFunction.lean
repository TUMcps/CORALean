module

public import CORALean.ContSet.ContSet.Definitions.SupportFunc

@[expose] public section

/-!
# Support functions: the representation

A set held as its support function `h(ℓ) = sup {ℓ x | x ∈ S}` [1, Sec. 2.1.4.9] over the linear
functionals `ℓ`, the set being what every functional allows: `{x | ∀ ℓ, ℓ x ≤ h ℓ}`. `h` takes
values in the extended reals, `+∞` for a functional the set is unbounded in and `-∞` everywhere for
the empty set, so every closed convex set has one, and the sets denoted are exactly the closed
convex ones (`SupportFunction.ofSet_exact`). Over any real module. A function on all functionals is
nothing finite to store, so there is no `Float/` layer: what an algorithm computes of a support
function is its value in a direction, `SupportBound`, and every conversion needing one asks for it
as a certificate.

## References

* [1] [M. Althoff, N. Kochdumper, T. Ladner, M. Perschl and M. Wetzlinger. "CORA Manual (v2026)".
      Technische Universität München, 2026.](../../../../../references/2026/althoff-cora-manual.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ========================================  MAIN TYPE  ========================================= --

/-- A support function: the extended-real supremum `h` of each linear functional over the set. -/
structure SupportFunction (α : Type) [AddCommGroup α] [Module ℝ α] where
  h : (α →ₗ[ℝ] ℝ) → EReal

/-- The points the support function allows under every functional. -/
def SupportFunction.construct (S : SupportFunction α) : Set α :=
  {x | ∀ ℓ : α →ₗ[ℝ] ℝ, (ℓ x : EReal) ≤ S.h ℓ}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
