import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
import CORALean.ContSet.Interval.Float.Operations.OfBounds
import CORALean.ContSet.ContSet.Float.SupportBound

/-!
# What a float halfspace description cannot do exactly

The same four as the exact layer, and for the same reason — the answer's rows
are not determined by the inputs' — so the caller names directions and the
bounds are composed. What this layer adds is where the rounding goes: `addUp`
when two extents are added, `maximum` when the larger is taken, nothing at all
for an image or a box.

Grouped in one file because the four differ only in which composition rule they
call.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n p : ℕ}
variable {P₁ P₂ P : HPolytope 𝕋 n}

def HPolytope.plusOf (Aq : Mat 𝕋 q n)
    (u₁ : ∀ i, FloatBound 𝕋 P₁.construct (rowLin Aq i))
    (u₂ : ∀ i, FloatBound 𝕋 P₂.construct (rowLin Aq i)) : HPolytope 𝕋 n :=
  HPolytope.ofBounds Aq fun i => (u₁ i).add (u₂ i)

def HPolytope.linCombOf (Aq : Mat 𝕋 q n)
    (u₁ : ∀ i, FloatBound 𝕋 P₁.construct (rowLin Aq i))
    (u₂ : ∀ i, FloatBound 𝕋 P₂.construct (rowLin Aq i)) : HPolytope 𝕋 n :=
  HPolytope.ofBounds Aq fun i => (u₁ i).segments (u₂ i)

/-- The map is a float matrix, so a direction on the target is pulled back
through what that matrix denotes. -/
def HPolytope.mtimesOf (M : Mat 𝕋 p n) (Aq : Mat 𝕋 q p)
    (u : ∀ i, FloatBound 𝕋 P.construct ((rowLin Aq i).comp (mulVecLin (toRealMat M)))) :
    HPolytope 𝕋 p :=
  HPolytope.ofBounds Aq fun i => FloatBound.image _ (u i)

def HPolytope.intervalOf (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) : Interval 𝕋 n :=
  Interval.ofBounds up lo

end CORALean.Float
