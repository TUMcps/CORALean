module

public import CORALean.ContSet.Conversion.Float.Zonotope_to_VPolytope
public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.ProbZonotope.Float.ProbZonotope
public import CORALean.ContSet.Zonotope.Float.Operations.Abs
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.ContSet.Zonotope.Float.Operations.Project
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirard

@[expose] public section

/-!
# `ContSet/ProbZonotope/Float/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ====================================  `ProbZonotope.abs`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- CORA's `abs(probZ)`: the mean zonotope becomes the float `Zonotope.abs` of itself (centre column
and generators in absolute value, exact) and the covariance interval is kept. As at the real
layer this is a different set of laws, not an enclosure of the input's. -/
def ProbZonotope.abs (P : ProbZonotope 𝕋 n) : ProbZonotope 𝕋 n :=
  ⟨P.Z.abs, P.cov⟩

end CORALean.Float


-- ===================================  `ProbZonotope.mean`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The zonotope of possible means: the stored mean zonotope. -/
def ProbZonotope.mean (P : ProbZonotope 𝕋 n) : Zonotope (Vec 𝕋 n) := P.Z
end CORALean.Float


-- ==================================  `ProbZonotope.mtimes`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable {m : ℕ}

/-- `(M Z, M Σ Mᵀ)`: the float zonotope image and the interval-matrix product of the covariance with
the point matrices `M` and `Mᵀ`. -/
def ProbZonotope.mtimes (M : Mat 𝕋 m n) (P : ProbZonotope 𝕋 n) : ProbZonotope 𝕋 m :=
  ⟨Zonotope.mtimes M P.Z,
    Interval.matMul (Interval.matMul (Interval.point M) P.cov) (Interval.point M.transpose)⟩
end CORALean.Float


-- ===============================  `ProbZonotope.ofGenerators`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable {q : ℕ}

/-- CORA's `probZonotope(Z, g)`: the mean zonotope `Z` and the covariance `g gᵀ`, as an
interval-matrix product of the point matrices `g` and `gᵀ`. -/
def ProbZonotope.ofGenerators (Z : Zonotope (Vec 𝕋 n)) (g : Mat 𝕋 n q) : ProbZonotope 𝕋 n :=
  ⟨Z, Interval.matMul (Interval.point g) (Interval.point g.transpose)⟩
end CORALean.Float


-- ===================================  `ProbZonotope.plus`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- `(Z₁ ⊕ Z₂, Σ₁ + Σ₂)`: the float zonotope sum and the interval-matrix sum of the covariances. -/
def ProbZonotope.plus (P₁ P₂ : ProbZonotope 𝕋 n) : ProbZonotope 𝕋 n :=
  ⟨P₁.Z.plus P₂.Z, Interval.matPlus P₁.cov P₂.cov⟩
end CORALean.Float


-- ==================================  `ProbZonotope.project`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable {m : ℕ}

/-- `Z(dims, :)` and `cov(dims, dims)`: the float zonotope projection and the submatrix of the
covariance interval, exact. -/
def ProbZonotope.project (P : ProbZonotope 𝕋 n) (dims : Fin m → Fin n) : ProbZonotope 𝕋 m :=
  ⟨P.Z.project dims,
    ⟨fun i j => P.cov.inf (dims i) (dims j), fun i j => P.cov.sup (dims i) (dims j)⟩⟩
end CORALean.Float


-- ===============================  `ProbZonotope.reduceGirard`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- CORA's `reduce(P, 'girard', o)`: the mean zonotope reduced by `Zonotope.reduceGirard` and the
covariance kept. -/
def ProbZonotope.reduceGirard (P : ProbZonotope 𝕋 n) (o : ℕ) : ProbZonotope 𝕋 n :=
  ⟨P.Z.reduceGirard o, P.cov⟩
end CORALean.Float


-- =================================  `ProbZonotope.vPolytope`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- CORA's `polytope(zonotope(probZ.Z))`: the corner polytope of the mean zonotope; the covariance
plays no part. -/
def ProbZonotope.vPolytope (P : ProbZonotope 𝕋 n) : VPolytope (Vec 𝕋 n) := P.Z.vPolytope
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
