module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.BilinGDown
public import CORALean.ContSet.PolyZonotope.Float.Operations.BilinGUp
public import CORALean.ContSet.PolyZonotope.Float.Operations.CenterResidual
public import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubset
public import CORALean.ContSet.PolyZonotope.Float.Operations.SplitGen
public import CORALean.ContSet.PolyZonotope.Float.Operations.SubsXprod
public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.Sum

@[expose] public section

/-!
# `ContSet/PolyZonotope/Float/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n h m : ℕ}


-- ================================  `PolyZonotope.bilinGDiff`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- How far a stored generator can be from the exact bilinear form.

The gap between the generator rounded up and rounded down. -/
def PolyZonotope.bilinGDiff (Q : Fin m → Mat 𝕋 n n) (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) :
    Mat 𝕋 m ((pZ₁.h + 1) * (pZ₂.h + 1)) :=
  fun k l => subUp (PolyZonotope.bilinGUp Q pZ₁ pZ₂ k l) (PolyZonotope.bilinGDown Q pZ₁ pZ₂ k l)


-- ==================================  `PolyZonotope.centre`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `center` for a polynomial zonotope returns the field `c`: the stored centre,
unchanged. It carries no guarantee of its own; `centre_mem_construct` says when it lies in
the set. -/
def PolyZonotope.centre (pZ : PolyZonotope (Vec 𝕋 n)) : Vec 𝕋 n := pZ.c


-- ==================================  `PolyZonotope.fiberUp`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Split out of `Compact.lean` (issue #62): read again by `mergedColUp` in this
directory and by `Theorems/LeFiberUp.lean`, both outside this file. -/
def PolyZonotope.fiberUp (r : Fin h → Fin h) (G : Mat 𝕋 n h) (i : Fin n) (j : Fin h) : 𝕋 :=
  sumUp fun l => if r l = j then G i l else zero


-- ================================  `PolyZonotope.quadMapGUp`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Split out of `QuadMap.lean` (issue #62): read again by `quadMapGDiff` in this
directory and by `Theorems/QuadMapOuter.lean`, both outside this file. -/
def PolyZonotope.quadMapGUp (Q : Fin m → Mat 𝕋 n n) (pZ : PolyZonotope (Vec 𝕋 n)) :
    Mat 𝕋 m ((pZ.h + 1) * (pZ.h + 1)) :=
  PolyZonotope.bilinGUp Q pZ pZ


-- ===========================  `PolyZonotope.representsa_emptySet`  ============================ --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `@polyZonotope/representsa_` at type `emptySet`: a polynomial zonotope's nominal part is
never empty, so only an empty error box (some coordinate with `sup < inf`, by `ltStrict`) makes
the set empty; a `true` is sound. -/
def PolyZonotope.representsa_emptySet (pZ : PolyZonotope (Vec 𝕋 n)) : Bool :=
  pZ.I_error.representsa_emptySet


-- ==================================  `PolyZonotope.resolve`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Factor `k` fixed at the value `x`: `getSubset` at `[x, x]`, as over ℝ. -/
def PolyZonotope.resolve (pZ : PolyZonotope (Vec 𝕋 n)) (k : Fin pZ.p) (x : 𝕋) :
    PolyZonotope (Vec 𝕋 n) :=
  pZ.getSubset k x zero


-- =================================  `PolyZonotope.splitMany`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The pieces `containsPointSet` works with: `k` rounds, every piece replaced by the two halves
`splitGen` gives, as over ℝ. -/
def PolyZonotope.splitMany (pZ : PolyZonotope (Vec 𝕋 n)) : ℕ → List (PolyZonotope (Vec 𝕋 n))
  | 0 => [pZ]
  | k + 1 => (pZ.splitMany k).flatMap fun q => [q.splitGen.1, q.splitGen.2]


-- =================================  `PolyZonotope.subsTerms`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- The generators of the result, as pairs of an original generator and a term. -/
def PolyZonotope.subsTerms (pZ : PolyZonotope (Vec 𝕋 n)) {nu : ℕ} (pZin : PolyZonotope (Vec 𝕋 nu))
    (idu : Fin nu → Fin pZ.p) : List (Fin pZ.h × ((Interval 𝕋) × (Fin pZin.p → ℕ))) :=
  (List.finRange pZ.h).flatMap fun i => (pZ.subsXprod pZin idu i).map fun t => (i, t)


-- ==================================  `PolyZonotope.sumErr`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The sum of `m` error boxes, by `Interval.plus`.

The sum of `m` error boxes by `Interval.plus`, the error box of `PolyZonotope.sum`. -/
def PolyZonotope.sumErr : (m : ℕ) → (Fin m → Interval (Vec 𝕋 n)) → Interval (Vec 𝕋 n)
  | 0, _ => Interval.origin n
  | m + 1, f => (f 0).plus (PolyZonotope.sumErr m fun i => f i.succ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
