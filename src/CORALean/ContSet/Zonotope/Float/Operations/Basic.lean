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


namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n h : ℕ}


-- ==================================  `Zonotope.errorRadius`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- The box radius, rounded up; halving is exact, so only the difference rounds. -/
def Zonotope.errorRadius (Z : Zonotope (Vec 𝕋 n)) : Vec 𝕋 n :=
  fun i => half (subUp (Z.I_error.sup i) (Z.I_error.inf i))


-- ================================  `Zonotope.generatorError`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---

/-- What generators known only to within `G` entrywise cost: coefficients range over
`[-1, 1]`, so a row sums with no cancellation. The generator counterpart of
`Interval.residual`, and the box every operation that rounds `G` pays into. -/
def Zonotope.generatorError (G : Mat 𝕋 n h) : Interval (Vec 𝕋 n) := Interval.symmetric (radius G)


-- ====================================  `Zonotope.origin`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The point `0` as a zonotope with no generators, the centre stored as `zero`
and the error box at zero, as `Interval.origin` is for a box. -/
def Zonotope.origin (n : ℕ) : Zonotope (Vec 𝕋 n) := Zonotope.point fun _ => zero


-- ====================================  `Zonotope.pointHi`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An upper end of `c + G β` for a coefficient vector `β`, each entry rounded upward. -/
def Zonotope.pointHi (Z : Zonotope (Vec 𝕋 n)) (β : Vec 𝕋 Z.h) : Vec 𝕋 n := fun i =>
  addUp (Z.c i) (dotUp (fun j => Z.G j i) β)


-- ====================================  `Zonotope.pointLo`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A lower end of `c + G β` for a coefficient vector `β`, each entry rounded downward. -/
def Zonotope.pointLo (Z : Zonotope (Vec 𝕋 n)) (β : Vec 𝕋 Z.h) : Vec 𝕋 n := fun i =>
  addDown (Z.c i) (dotDown (fun j => Z.G j i) β)


-- ===================================  `Zonotope.pointMat`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   09-October-2026
-- Reviewed:      ---

/-- A stored matrix as a matrix zonotope: no generators, and the zero box, since nothing
was rounded. The exact layer's `Zonotope.ofPoint`, which `discretizeMatZonotope` feeds
the system matrix through. -/
def Zonotope.pointMat (A : Mat 𝕋 m n) : Zonotope (Mat 𝕋 m n) :=
  ⟨0, A, Fin.elim0, Interval.point fun _ _ => zero⟩


-- ====================================  `Zonotope.shiftUp`  ==================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- The box midpoint added to the centre, rounded up — the other side of the gap
`shiftDown` leaves for `absorbError` to store. -/
def Zonotope.shiftUp (Z : Zonotope (Vec 𝕋 n)) : Vec 𝕋 n :=
  fun i => addUp (Z.c i) (half (addUp (Z.I_error.inf i) (Z.I_error.sup i)))


-- ====================================  `Zonotope.stBeta`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- β of CORA's `'approx:st'` test (Sadraddini-Tedrake; `containsZonotope`), with `c₁ - c₂ = G₂ β`:
`H (c₁ - c₂ - e₂)` rounded down, `H` the proposed inverse of `G₂`, `e₂` the lower corner of
`Z₂`'s error box. -/
def Zonotope.stBeta (Z₂ Z₁ : Zonotope (Vec 𝕋 n)) (H : Mat 𝕋 Z₂.h n) : Vec 𝕋 Z₂.h :=
  fun k => dotDown (H k) fun l => subDown (subDown (Z₁.c l) (Z₂.c l)) (Z₂.I_error.inf l)


-- ====================================  `Zonotope.stGamma`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Γ of the `'approx:st'` containment test `Z₁ ⊆ Z₂` (Sadraddini and Tedrake, see
`containsZonotope`), the matrix with `G₁ = G₂ Γ`: here `H G₁` rounded down, `H` the proposed
inverse of `G₂`. `st` is CORA's name for the test (S. and T.). -/
def Zonotope.stGamma (Z₂ Z₁ : Zonotope (Vec 𝕋 n)) (H : Mat 𝕋 Z₂.h n) : Mat 𝕋 Z₂.h Z₁.h :=
  fun k j => dotDown (H k) (Z₁.G j)


-- ====================================  `Zonotope.stUsed`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Row `k` of `‖[Γ, β]‖∞` in the `'approx:st'` test (`st`: Sadraddini-Tedrake), rounded up: the
sum `|βₖ| + ∑ⱼ |Γₖⱼ|` of `stBeta` and `stGamma`, which the test needs at most `1`. -/
def Zonotope.stUsed (Z₂ Z₁ : Zonotope (Vec 𝕋 n)) (H : Mat 𝕋 Z₂.h n) (k : Fin Z₂.h) : 𝕋 :=
  addUp (absolute (Z₂.stBeta Z₁ H k)) (sumUp fun j => absolute (Z₂.stGamma Z₁ H k j))


-- ====================================  `Zonotope.stDelta`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The slack of the `'approx:st'` test (`st`: Sadraddini-Tedrake), rounded down: half of
`1 - max ₖ stUsed`, the size of coefficient the rounding residuals may still use. -/
def Zonotope.stDelta (Z₂ Z₁ : Zonotope (Vec 𝕋 n)) (H : Mat 𝕋 Z₂.h n) : 𝕋 :=
  half (subDown one (maximumOver (Z₂.stUsed Z₁ H)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
