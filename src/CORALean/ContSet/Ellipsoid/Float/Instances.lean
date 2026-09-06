import CORALean.ContSet.Ellipsoid.Float.Theorems.PlusOuter
import CORALean.ContSet.Ellipsoid.Float.Theorems.MtimesOuter

/-!
# What `Ellipsoid` instantiates

`Mtimes` by instance search, and `Plus` once a caller has named the two
scalings — the same pair of classes as over ℝ, and for the same reasons. An
ellipsoid is closed under a linear image and under nothing else the interface
names, and every enclosure of a sum, a combination or a reduction carries a free
parameter.

`ContSet` is not among them: `InflatedContSet` supplies it, which is what makes
this the same interface as over ℝ.

`plusInstance` is the exact layer's, with the parameter it really has: two
floats and the certificate `1/s₁² + 1/s₂² ≤ 1` rather than one real `l`. That
widens the family — `l`'s derived pair meets the condition with equality, so the
pairs `l` reaches are a proper subset of the admissible ones — which is the
reverse of the usual direction between the layers. It is a `def` and not an
`instance` for the same reason as over ℝ.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   03-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ========================================  INSTANCES  ========================================= --

/-- `Plus` at two scalings the caller chooses, together with the inequality that
makes them sound. Deliberately not an `instance`, as over ℝ. -/
@[reducible] def Ellipsoid.plusInstance {s₁ s₂ : 𝕋}
    (hne₁ : toReal s₁ ≠ 0) (hne₂ : toReal s₂ ≠ 0)
    (hs : 1 / toReal s₁ ^ 2 + 1 / toReal s₂ ^ 2 ≤ 1) :
    ∀ n, Plus (Ellipsoid 𝕋 n) (Vec ℝ n) := fun _ =>
  { plus := fun E₁ E₂ => (Ellipsoid.plus s₁ s₂ E₁ E₂).materialise
    plus_outer := fun E₁ E₂ => by
      rw [Ellipsoid.materialise_eq]
      exact Ellipsoid.plus_outer s₁ s₂ E₁ E₂ hne₁ hne₂ hs }

instance : Mtimes (Mat 𝕋) (Ellipsoid 𝕋) where
  mtimes M E := (Ellipsoid.mtimes M E).materialise
  mtimes_outer M E := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton, Ellipsoid.materialise_eq]
    exact Ellipsoid.mtimes_outer M E

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
