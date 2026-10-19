module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Float.Operations.GetSubset
public import CORALean.ContSet.ConPolyZono.Float.Operations.IntersectionAgree
public import CORALean.ContSet.ConPolyZono.Float.Operations.IsFullDimWith
public import CORALean.ContSet.ConPolyZono.Float.Operations.MergedCol
public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.PolyZonotope.Float.Operations.Compact
public import CORALean.ContSet.Zonotope.Float.Operations.RightInvCandidate

@[expose] public section

/-!
# `ContSet/ConPolyZono/Float/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

section

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ===================================  `ConPolyZono.center`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `center` of a constrained polynomial zonotope: the stored field `c`, nothing computed,
so nothing rounds. Whether it is a point of the set is `center_mem_construct`. -/
def ConPolyZono.center (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : Vec 𝕋 n := cPZ.c


-- =================================  `ConPolyZono.isFullDim`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `ConPolyZono.isFullDimWith` at the default candidate right inverse of the independent generators
(`Zonotope.rightInvCandidate`). Only `true` is certain. -/
def ConPolyZono.isFullDim (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : Bool :=
  cPZ.isFullDimWith (Zonotope.rightInvCandidate fun i j => cPZ.GI j i)


-- ================================  `ConPolyZono.mergedColUp`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- The same fibre rounded the other way, which is what bounds the gap. -/
def ConPolyZono.mergedColUp (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (i : Fin n)
    (j : Fin (PolyZonotope.repKeep cPZ.E).card) : 𝕋 :=
  PolyZonotope.fiberUp (Real.PolyZonotope.rep cPZ.E) (fun i l => cPZ.G l i) i
    (PolyZonotope.keepIdx cPZ.E j)


-- ===============================  `ConPolyZono.compactGensGap`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- What a merged generator column can be off by. -/
def ConPolyZono.compactGensGap (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    Mat 𝕋 n (PolyZonotope.repKeep cPZ.E).card :=
  fun i j => subUp (cPZ.mergedColUp i j) (cPZ.mergedCol i j)


-- ================================  `ConPolyZono.rescaleStep`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- One step of the fold `rescale` runs: factor `r` re-parametrized onto `cen r ± rad r` by the
float `getSubset`, the set left alone when `r` is not a factor. -/
def ConPolyZono.rescaleStep (cen rad : ℕ → 𝕋) (acc : ConPolyZono 𝕋 (Vec 𝕋 n)) (r : ℕ) :
    ConPolyZono 𝕋 (Vec 𝕋 n) :=
  if h : r < acc.p then acc.getSubset ⟨r, h⟩ (cen r) (rad r) else acc

end


section

open FloatOps


-- ==================================  `ConPolyZono.unitBox`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The factor box `[-1,1]ᵖ` with which CORA's `@conPolyZono/rescale` starts, stored as floats:
`-1` and `1` are exact in the scalar, so the box is the exact layer's. -/
def ConPolyZono.unitBox (𝕋 : Type) [FloatOps 𝕋] (p : ℕ) : Interval (Vec 𝕋 p) where
  inf := fun _ => neg one
  sup := fun _ => one

end

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
