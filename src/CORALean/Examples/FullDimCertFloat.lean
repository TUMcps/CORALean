import CORALean.ContSet.ConPolyZono.Float.Theorems.IsFullDimSound
import CORALean.ContSet.ConZonotope.Float.Theorems.ContainsPointSound
import CORALean.ContSet.ConZonotope.Float.Theorems.IsFullDimSound
import CORALean.ContSet.ConZonotope.Float.Theorems.RepresentsaEmptySetSound
import CORALean.ContSet.HPolytope.Float.Theorems.IsFullDimSound
import CORALean.ContSet.PolyZonotope.Float.Theorems.IsFullDimSound
import CORALean.ContSet.VPolytope.Float.Operations.IsFullDim
import CORALean.ContSet.VPolytope.Float.Theorems.IsFullDimSound
import CORALean.ContSet.ZonoBundle.Float.Theorems.IsFullDimSound
import CORALean.ContSet.ZonoBundle.Float.Theorems.RepresentsaEmptySetSound
import CORALean.ContSet.Zonotope.Float.Theorems.ContainsPointSound
import CORALean.ContSet.Zonotope.Float.Theorems.IsFullDimSound
import CORALean.Global.Float.Instances.Dyadic.API
import CORALean.Specification.Instances

/-!
# The float certificate checkers, run

At `Dyadic 53`. `Zonotope.isFullDim` accepts a full-rank generator matrix (square, wide, and so
ill-conditioned that a naive rank test is on the edge) and refuses a rank-deficient one. A
constrained zonotope is full-dimensional with a strictly feasible coefficient point and a right
inverse (here the default candidate); a slab row `Ae β ∈ [-1/2, 1/2]` leaves a margin, and an
unsatisfiable row is refuted by a Farkas certificate. A box point is certified in a constrained
zonotope with no exact solve, the rounding absorbed by the box a right inverse reaches. A bundle
is full-dimensional at a point strictly inside every member, and empty when the members are
apart. A zonotope is certified inside another (Sadraddini and Tedrake's coefficients, the
rounding absorbed), unless it touches the boundary.

Each `true` is a guarantee (`Zonotope.isFullDim_sound`, `ConZonotope.isFullDim_sound`,
`ConZonotope.containsPoint_sound`, `ConZonotope.representsa_emptySet_sound`,
`ZonoBundle.isFullDim_sound`, `ZonoBundle.representsa_emptySet_sound`,
`Zonotope.containsZonotope_sound`,
`HPolytope.isFullDim_sound`, `VPolytope.isFullDim_sound`); a `false` decides nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.FullDimCertFloat

open CORALean CORALean.Float FloatOps

abbrev D := Dyadic 53

/-- `m · 2 ^ e`. -/
def d (m e : ℤ) : D := ⟨m, e⟩

/-- No rounding error. -/
def box0 : Interval (Vec D 2) := ⟨fun _ => d 0 0, fun _ => d 0 0⟩

/-- Zonotopes centred at the origin: invertible, rank one, wide, and nearly singular. -/
def zInv : Zonotope D 2 := ⟨2, ![d 0 0, d 0 0], !![d 1 0, d 1 0; d 0 0, d 1 0], box0⟩
def zRank1 : Zonotope D 2 := ⟨2, ![d 0 0, d 0 0], !![d 1 0, d 1 0; d 1 0, d 1 0], box0⟩
def zWide : Zonotope D 2 :=
  ⟨3, ![d 0 0, d 0 0], !![d 1 0, d 0 0, d 1 0; d 0 0, d 1 0, d 1 0], box0⟩
def zNear : Zonotope D 2 := ⟨2, ![d 0 0, d 0 0], !![d 1 0, d 1 0; d 0 0, d 1 (-30)], box0⟩

#eval zInv.isFullDim     -- true
#eval zRank1.isFullDim   -- false, the generators span a line
#eval zWide.isFullDim    -- true
#eval zNear.isFullDim    -- true

/-- `β₁ + β₂ ≤ 1`. -/
def sumLeOne : HPolytope D 2 :=
  ⟨1, fun _ _ => d 1 0, fun _ => d 1 0, 0, fun i => i.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩⟩

/-- `-β₁ ≤ -3`, unsatisfiable within the unit box. -/
def beyondBox : HPolytope D 2 :=
  ⟨1, fun _ j => if j = 0 then d (-1) 0 else d 0 0, fun _ => d (-3) 0, 0, fun i => i.elim0,
    ⟨fun i => i.elim0, fun i => i.elim0⟩⟩

/-- `β₁ + β₂ ∈ [-1/2, 1/2]`, an equality row with slack. -/
def slab : HPolytope D 2 :=
  ⟨0, fun i => i.elim0, fun i => i.elim0, 1, fun _ _ => d 1 0,
    ⟨fun _ => d (-1) (-1), fun _ => d 1 (-1)⟩⟩

/-- The unit square's generators with the constraint `P`. -/
def square (P : HPolytope D 2) : ConZonotope D 2 :=
  ⟨2, ![d 0 0, d 0 0], !![d 1 0, d 0 0; d 0 0, d 1 0], P, box0⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The default right inverse of the square's generators. -/
def H₀ (P : HPolytope D 2) : Mat D 2 2 := Zonotope.rightInvCandidate (square P).G

#eval (square sumLeOne).isFullDim (H₀ sumLeOne) (fun _ => d 0 0)    -- true
#eval (square slab).isFullDim (H₀ slab) (fun _ => d 0 0)            -- true
#eval (square beyondBox).isFullDim (H₀ beyondBox) (fun _ => d 0 0)  -- false, empty
#eval (square sumLeOne).representsa_emptySet                        -- false
#eval (square beyondBox).representsa_emptySet                       -- true

-- (1/2, 1/4) is in the set, reached from the coefficient point (1/2, 1/4)
#eval (square sumLeOne).containsPoint (H₀ sumLeOne) ![d 1 (-1), d 1 (-2)] ![d 1 (-1), d 1 (-2)]
-- (3, 1/4) is not
#eval (square sumLeOne).containsPoint (H₀ sumLeOne) ![d 1 (-1), d 1 (-2)] ![d 3 0, d 1 (-2)]

#eval sumLeOne.isFullDim ![d 0 0, d 0 0]   -- true: `0 < 1`
#eval sumLeOne.isFullDim ![d 1 0, d 0 0]   -- false: `1 < 1` fails

/-- A triangle and three collinear points, as vertices. -/
def triangle : VPolytope D 2 := ⟨3, !![d 0 0, d 1 0, d 0 0; d 0 0, d 0 0, d 1 0], box0⟩
def segment : VPolytope D 2 := ⟨3, !![d 0 0, d 1 0, d 2 0; d 0 0, d 1 0, d 2 0], box0⟩

#eval triangle.isFullDim   -- true
#eval segment.isFullDim    -- false, the points lie on a line

/-- A flat box and a thin parallelogram, which meet near the origin. -/
def bundle : ZonoBundle D 2 :=
  ⟨2, ![⟨2, ![d 0 0, d 0 0], !![d 2 0, d 0 0; d 0 0, d 1 (-3)], box0⟩,
        ⟨2, ![d 0 0, d 0 0], !![d 2 0, d 1 (-3); d 2 0, d (-1) (-3)], box0⟩]⟩

/-- Two unit segments five apart. -/
def apart : ZonoBundle D 2 :=
  ⟨2, ![⟨1, ![d 0 0, d 0 0], !![d 1 0; d 0 0], box0⟩,
        ⟨1, ![d 5 0, d 0 0], !![d 1 0; d 0 0], box0⟩]⟩

#eval bundle.isFullDim (fun i => Zonotope.rightInvCandidate (bundle.Z i).G) ![d 0 0, d 0 0]  -- true
#eval bundle.representsa_emptySet   -- false
#eval apart.representsa_emptySet    -- true

/-- `[-2, 2]²`, a unit square shifted by `(1/2, 0)`, one centred at `(3, 0)`, a diagonal segment. -/
def big : Zonotope D 2 := ⟨2, ![d 0 0, d 0 0], !![d 2 0, d 0 0; d 0 0, d 2 0], box0⟩
def inside : Zonotope D 2 := ⟨2, ![d 1 (-1), d 0 0], !![d 1 0, d 0 0; d 0 0, d 1 0], box0⟩
def outside : Zonotope D 2 := ⟨2, ![d 3 0, d 0 0], !![d 1 0, d 0 0; d 0 0, d 1 0], box0⟩
def diagonal : Zonotope D 2 := ⟨1, ![d 0 0, d 0 0], !![d 1 0; d 1 0], box0⟩

#eval Contains.contains big inside     -- true
#eval Contains.contains big outside    -- false
#eval Contains.contains big diagonal   -- true
#eval Contains.contains big big        -- false: touching the boundary is not certified

end CORALean.Examples.FullDimCertFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
