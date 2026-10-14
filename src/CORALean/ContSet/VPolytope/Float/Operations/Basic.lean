module

public import CORALean.ContSet.Interval.Float.Operations.BoundNegProj
public import CORALean.ContSet.Interval.Float.Operations.BoundProj
public import CORALean.ContSet.VPolytope.Float.Operations.NominalBoundNegProj
public import CORALean.ContSet.VPolytope.Float.Operations.NominalBoundProj
public import CORALean.ContSet.VPolytope.Float.VPolytope

@[expose] public section

/-!
# `ContSet/VPolytope/Float/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ===================================  `VPolytope.bordered`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A float vertex matrix `V` (`n × k`) with a row of ones appended: `[V; 1ᵀ]`, `(n + 1) × k`. Its
right inverse reaches, besides the points near the vertices' mean, the weights' sum, which is
what a convex combination fixes at one. -/
def VPolytope.bordered (P : VPolytope (Vec 𝕋 n)) : Mat 𝕋 (n + 1) P.k := fun i j =>
  if h : i.val < n then P.V j ⟨i.val, h⟩ else one

end CORALean.Float


namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =================================  `VPolytope.boundNegProj`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- The nominal bound and the error box's own, added. -/
def VPolytope.boundNegProj (P : VPolytope (Vec 𝕋 n)) (j : Fin n) :
    FloatBound 𝕋 P.construct (-LinearMap.proj j) :=
  InflatedContSet.boundOfParts (P.nominalBoundNegProj j) (P.I_error.boundNegProj j)


-- ==================================  `VPolytope.boundProj`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- The nominal bound and the error box's own, added. -/
def VPolytope.boundProj (P : VPolytope (Vec 𝕋 n)) (j : Fin n) :
    FloatBound 𝕋 P.construct (LinearMap.proj j) :=
  InflatedContSet.boundOfParts (P.nominalBoundProj j) (P.I_error.boundProj j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
