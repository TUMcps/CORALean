module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Zonotope.Float.Operations.Point
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `ContSet/Zonotope/Float/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ==================================  `Zonotope.errorRadius`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The box radius, rounded up; halving is exact, so only the difference rounds. -/
def Zonotope.errorRadius (Z : Zonotope (Vec 𝕋 n)) : Vec 𝕋 n :=
  fun i => half (subUp (Z.E.sup i) (Z.E.inf i))

end CORALean.Float


-- ================================  `Zonotope.generatorError`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n h : ℕ}

/-- What generators known only to within `G` entrywise cost: coefficients range over
`[-1, 1]`, so a row sums with no cancellation. The generator counterpart of
`Interval.residual`, and the box every operation that rounds `G` pays into. -/
def Zonotope.generatorError (G : Mat 𝕋 n h) : Interval (Vec 𝕋 n) := Interval.symmetric (radius G)

end CORALean.Float


-- ====================================  `Zonotope.origin`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The point `0` as a zonotope with no generators, the centre stored as `zero`
and the error box at zero, as `Interval.origin` is for a box. -/
def Zonotope.origin (n : ℕ) : Zonotope (Vec 𝕋 n) := Zonotope.point fun _ => zero

end CORALean.Float


-- ====================================  `Zonotope.pointHi`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- An upper end of `c + G β` for a coefficient vector `β`, each entry rounded upward. -/
def Zonotope.pointHi (Z : Zonotope (Vec 𝕋 n)) (β : Vec 𝕋 Z.h) : Vec 𝕋 n := fun i =>
  addUp (Z.c i) (dotUp (fun j => Z.G j i) β)

end CORALean.Float


-- ====================================  `Zonotope.pointLo`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- A lower end of `c + G β` for a coefficient vector `β`, each entry rounded downward. -/
def Zonotope.pointLo (Z : Zonotope (Vec 𝕋 n)) (β : Vec 𝕋 Z.h) : Vec 𝕋 n := fun i =>
  addDown (Z.c i) (dotDown (fun j => Z.G j i) β)

end CORALean.Float


-- ===================================  `Zonotope.pointMat`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   09-October-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}

/-- A stored matrix as a matrix zonotope: no generators, and the zero box, since nothing
was rounded. The exact layer's `Zonotope.ofPoint`, which `discretizeMatZonotope` feeds
the system matrix through. -/
def Zonotope.pointMat (A : Mat 𝕋 m n) : Zonotope (Mat 𝕋 m n) :=
  ⟨0, A, Fin.elim0, Interval.point fun _ _ => zero⟩

end CORALean.Float


-- ====================================  `Zonotope.shiftUp`  ==================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The box midpoint added to the centre, rounded up — the other side of the gap
`shiftDown` leaves for `absorbError` to store. -/
def Zonotope.shiftUp (Z : Zonotope (Vec 𝕋 n)) : Vec 𝕋 n :=
  fun i => addUp (Z.c i) (half (addUp (Z.E.inf i) (Z.E.sup i)))

end CORALean.Float


-- ====================================  `Zonotope.stBeta`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The approximate coefficients of the centres, `H (c₁ - c₂ - e₂)`, with `e₂` the lower corner of
the second error box. -/
def Zonotope.stBeta (Z₂ Z₁ : Zonotope (Vec 𝕋 n)) (H : Mat 𝕋 Z₂.h n) : Vec 𝕋 Z₂.h :=
  fun k => dotDown (H k) fun l => subDown (subDown (Z₁.c l) (Z₂.c l)) (Z₂.E.inf l)

end CORALean.Float


-- ====================================  `Zonotope.stGamma`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The approximate coefficients of the generators, `H G₁`. -/
def Zonotope.stGamma (Z₂ Z₁ : Zonotope (Vec 𝕋 n)) (H : Mat 𝕋 Z₂.h n) : Mat 𝕋 Z₂.h Z₁.h :=
  fun k j => dotDown (H k) (Z₁.G j)

end CORALean.Float


-- ====================================  `Zonotope.stUsed`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- What the two kinds of coefficient use of the unit budget, rounded up. -/
def Zonotope.stUsed (Z₂ Z₁ : Zonotope (Vec 𝕋 n)) (H : Mat 𝕋 Z₂.h n) (k : Fin Z₂.h) : 𝕋 :=
  addUp (absolute (Z₂.stBeta Z₁ H k)) (sumUp fun j => absolute (Z₂.stGamma Z₁ H k j))

end CORALean.Float


-- ====================================  `Zonotope.stDelta`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- Half of the budget's slack, rounded down: the size of correction the box may use. -/
def Zonotope.stDelta (Z₂ Z₁ : Zonotope (Vec 𝕋 n)) (H : Mat 𝕋 Z₂.h n) : 𝕋 :=
  half (subDown one (maximumOver (Z₂.stUsed Z₁ H)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
