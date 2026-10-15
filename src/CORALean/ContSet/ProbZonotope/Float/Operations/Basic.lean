module

public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_VPolytope
public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.ProbZonotope.Float.ProbZonotope
public import CORALean.ContSet.Zonotope.Float.Operations.Abs
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.ContSet.Zonotope.Float.Operations.Project
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirard
public import CORALean.Global.Float.Sqrt
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# `ContSet/ProbZonotope/Float/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n q m : ℕ}


-- ====================================  `ProbZonotope.abs`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `abs(probZ)`: the mean zonotope becomes the float `Zonotope.abs` of itself (center column
and generators in absolute value, exact) and the covariance interval is kept. As at the real
layer this is a different set of laws, not an enclosure of the input's. -/
def ProbZonotope.abs (P : ProbZonotope 𝕋 n) : ProbZonotope 𝕋 n :=
  ⟨P.Z.abs, P.cov⟩


-- =============================  `ProbZonotope.confidenceRadius`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `m √(n Σᵢᵢ)`, rounded up, at the covariance interval's upper diagonal: the reach of `m g β`,
`g` the covariance's square root and `β` in the unit cube, in coordinate `i`. -/
def ProbZonotope.confidenceRadius (p : ℕ) (P : ProbZonotope 𝕋 n) (m : 𝕋) : Vec 𝕋 n :=
  fun i => mulUp m (sqrtUp p (nsmulUp n (maximum zero (P.cov.sup i i))))


-- ===================================  `ProbZonotope.mean`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The zonotope of possible means: the stored mean zonotope. -/
def ProbZonotope.mean (P : ProbZonotope 𝕋 n) : Zonotope (Vec 𝕋 n) := P.Z


-- ==================================  `ProbZonotope.mtimes`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `(M Z, M Σ Mᵀ)`: the float zonotope image and the interval-matrix product of the covariance with
the point matrices `M` and `Mᵀ`. -/
def ProbZonotope.mtimes (M : Mat 𝕋 m n) (P : ProbZonotope 𝕋 n) : ProbZonotope 𝕋 m :=
  ⟨Zonotope.mtimes M P.Z,
    Interval.matMul (Interval.matMul (Interval.point M) P.cov) (Interval.point M.transpose)⟩


-- ===============================  `ProbZonotope.ofGenerators`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `probZonotope(Z, g)`: the mean zonotope `Z` and the covariance `g gᵀ`, as an
interval-matrix product of the point matrices `g` and `gᵀ`. -/
def ProbZonotope.ofGenerators (Z : Zonotope (Vec 𝕋 n)) (g : Mat 𝕋 n q) : ProbZonotope 𝕋 n :=
  ⟨Z, Interval.matMul (Interval.point g) (Interval.point g.transpose)⟩


-- ===================================  `ProbZonotope.plus`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `(Z₁ ⊕ Z₂, Σ₁ + Σ₂)`: the float zonotope sum and the interval-matrix sum of the covariances. -/
def ProbZonotope.plus (P₁ P₂ : ProbZonotope 𝕋 n) : ProbZonotope 𝕋 n :=
  ⟨P₁.Z.plus P₂.Z, Interval.matPlus P₁.cov P₂.cov⟩


-- ==================================  `ProbZonotope.project`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Z(dims, :)` and `cov(dims, dims)`: the float zonotope projection and the submatrix of the
covariance interval, exact. -/
def ProbZonotope.project (P : ProbZonotope 𝕋 n) (dims : Fin m → Fin n) : ProbZonotope 𝕋 m :=
  ⟨P.Z.project dims,
    ⟨fun i j => P.cov.inf (dims i) (dims j), fun i j => P.cov.sup (dims i) (dims j)⟩⟩


-- ===============================  `ProbZonotope.reduceGirard`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `reduce(P, 'girard', o)`: the mean zonotope reduced by `Zonotope.reduceGirard` and the
covariance kept. -/
def ProbZonotope.reduceGirard (P : ProbZonotope 𝕋 n) (o : ℕ) : ProbZonotope 𝕋 n :=
  ⟨P.Z.reduceGirard o, P.cov⟩


-- =================================  `ProbZonotope.vPolytope`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `polytope(zonotope(probZ.Z))`: the corner polytope of the mean zonotope; the covariance
plays no part. -/
def ProbZonotope.vPolytope (P : ProbZonotope 𝕋 n) : VPolytope (Vec 𝕋 n) := P.Z.vPolytope


-- =================================  `ProbZonotope.zonotope`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The mean zonotope plus the box `[-ρ, ρ]` of `confidenceRadius`, as diagonal generators. -/
def ProbZonotope.zonotope (p : ℕ) (P : ProbZonotope 𝕋 n) (m : 𝕋) : Zonotope (Vec 𝕋 n) :=
  P.Z.plus (Interval.zonotope ⟨(-(P.confidenceRadius p m)), P.confidenceRadius p m⟩)


-- =================================  `ProbZonotope.interval`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `interval(probZ)`: the interval hull of the confidence zonotope. -/
def ProbZonotope.interval (p : ℕ) (P : ProbZonotope 𝕋 n) (m : 𝕋) : Interval (Vec 𝕋 n) :=
  (P.zonotope p m).interval

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
