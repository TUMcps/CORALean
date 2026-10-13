import CORALean.ContSet.HPolytope.Real.Instances
import CORALean.ContSet.HPolytope.Real.Operations.Fullspace
import CORALean.ContSet.HPolytope.Real.Operations.OfBounds

/-!
# A halfspace description that sums, and a solver nothing trusts

`HPolytope` now instantiates `Plus` and `LinComb`, which it could not while its
bounds had to come from the caller. `Simplex` proposes the weighting,
`supportBound` checks it, and the checked weighting is what `ofBoundsOpt` turns
into a row.

The last two examples are the point of the design. A direction the solver cannot
answer — the whole space has one in every non-zero direction — leaves the row
out rather than the operation, so `plus` is total on a type that admits
unbounded sets. And a bound is a `SupportBound`, which cannot be written down
without its proof: a solver returning nonsense loses rows and can win none.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


namespace CORALean.Real

open Pointwise ContSet


/-- The Minkowski sum lands, on the two operands' own rows. -/
example {n : ℕ} (P₁ P₂ : HPolytope (Vec ℝ n)) :
    construct P₁ + construct P₂ ⊆ construct (P₁ ⊞ P₂) :=
  Plus.plus_outer P₁ P₂

/-- And `linComb`, on the same rows and the same certificates. -/
example {n : ℕ} (P₁ P₂ : HPolytope (Vec ℝ n)) :
    segments (construct P₁) (construct P₂) ⊆ construct (LinComb.linComb P₁ P₂) :=
  LinComb.linComb_outer P₁ P₂

/-- The whole space is unbounded in every non-zero direction, so every row of
this sum is one the solver declined — and the sum is still a description. -/
example {n : ℕ} :
    construct (HPolytope.fullspace (Vec ℝ n)) + construct (HPolytope.fullspace (Vec ℝ n))
      ⊆ construct (HPolytope.fullspace (Vec ℝ n) ⊞ HPolytope.fullspace (Vec ℝ n)) :=
  Plus.plus_outer _ _

/-- A solver answering nothing at all still encloses. What it costs is every
row, which is precision; there is no answer it could give that costs soundness. -/
example {n q : ℕ} {S : Set (Vec ℝ n)} (Aq : Fin q → (Vec ℝ n →ₗ[ℝ] ℝ)) :
    S ⊆ (HPolytope.ofBoundsOpt (S := S) Aq fun _ => none).construct :=
  HPolytope.subset_ofBoundsOpt (S := S) Aq _

end CORALean.Real

