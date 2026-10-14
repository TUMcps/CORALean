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

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ===================================  `ConPolyZono.centre`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `center` of a constrained polynomial zonotope: the stored field `c`, nothing computed,
so nothing rounds. Whether it is a point of the set is `centre_mem_construct`. -/
def ConPolyZono.centre (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : Vec 𝕋 n := cPZ.c


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


-- ===============================  `ConPolyZono.mergedConsCol`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- The merged constraint column as stored, `A`'s rows read as the generator
matrix they are on the constraint side. -/
def ConPolyZono.mergedConsCol (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (i : Fin cPZ.m)
    (l : Fin (PolyZonotope.repKeep cPZ.EC).card) : 𝕋 :=
  PolyZonotope.fiberDown (Real.PolyZonotope.rep cPZ.EC) cPZ.A i (PolyZonotope.keepIdx cPZ.EC l)


-- ==============================  `ConPolyZono.mergedConsColUp`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- `ConPolyZono.mergedConsColUp` -/
def ConPolyZono.mergedConsColUp (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (i : Fin cPZ.m)
    (l : Fin (PolyZonotope.repKeep cPZ.EC).card) : 𝕋 :=
  PolyZonotope.fiberUp (Real.PolyZonotope.rep cPZ.EC) cPZ.A i (PolyZonotope.keepIdx cPZ.EC l)


-- ===============================  `ConPolyZono.compactConsGap`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- What a merged constraint column can be off by. -/
def ConPolyZono.compactConsGap (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    Mat 𝕋 cPZ.m (PolyZonotope.repKeep cPZ.EC).card :=
  fun i l => subUp (cPZ.mergedConsColUp i l) (cPZ.mergedConsCol i l)


-- ===================================  `ConPolyZono.plusB`  ==================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- The two right-hand sides side by side. Copied, so nothing here rounds. -/
def ConPolyZono.plusB {m₁ m₂ : ℕ} (b₁ : Interval (Vec 𝕋 m₁)) (b₂ : Interval (Vec 𝕋 m₂)) :
    Interval (Vec 𝕋 (m₁ + m₂)) :=
  ⟨Fin.append b₁.inf b₂.inf, Fin.append b₁.sup b₂.sup⟩


-- ===============================  `ConPolyZono.intersectionB`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- The two systems' own bounds, then the agreement rows'. -/
def ConPolyZono.intersectionB (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    Interval (Vec 𝕋 (cPZ₁.m + cPZ₂.m + n)) :=
  ⟨Fin.append (ConPolyZono.plusB cPZ₁.b cPZ₂.b).inf (ConPolyZono.intersectionAgree cPZ₁ cPZ₂).inf,
   Fin.append (ConPolyZono.plusB cPZ₁.b cPZ₂.b).sup (ConPolyZono.intersectionAgree cPZ₁ cPZ₂).sup⟩


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

end CORALean.Float


namespace CORALean.Float

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

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
