import CORALean.ContSet.ConZonotope.Float.Theorems.ContainsPointSound
import CORALean.ContSet.ConZonotope.Float.Theorems.IsFullDimSound
import CORALean.ContSet.ConZonotope.Float.Theorems.RepresentsaEmptySetSound
import CORALean.ContSet.HPolytope.Float.Theorems.IsFullDimSound
import CORALean.ContSet.Zonotope.Float.Theorems.IsFullDimSound
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.Specification.Instances

/-!
# Certificates for a constrained zonotope, run

At `Dyadic 53`. The unit square's generators under a constraint on the coefficients `β`.
The set is full-dimensional with a strictly feasible coefficient point and a right inverse
(here the default candidate): `β₁ + β₂ ≤ 1` and the slab `β₁ + β₂ ∈ [-1/2, 1/2]` leave a
margin at `β = 0`, while `-β₁ ≤ -3` is unsatisfiable within the unit box and is refuted by a
Farkas certificate. A box point is certified in the set with no exact solve, the rounding
absorbed by the box a right inverse reaches: `(1/2, 1/4)` is, `(3, 1/4)` is not.

Each `true` is a guarantee (`ConZonotope.isFullDim_sound`, `ConZonotope.containsPoint_sound`,
`ConZonotope.representsa_emptySet_sound`, `HPolytope.isFullDim_sound`); a `false` decides
nothing.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.ConZonotopeCertFloat

open CORALean CORALean.Float FloatOps

abbrev D := Dyadic 53

/-- `m · 2 ^ e`. -/
def d (m e : ℤ) : D := ⟨m, e⟩

/-- No rounding error. -/
def box0 : Interval (Vec D 2) := ⟨fun _ => d 0 0, fun _ => d 0 0⟩

/-- `β₁ + β₂ ≤ 1`. -/
def sumLeOne : HPolytope D (Vec D 2) :=
  ⟨1, fun _ _ => d 1 0, fun _ => d 1 0, 0, fun i => i.elim0, fun i => i.elim0,
    fun _ => FloatOps.zero, fun _ => FloatOps.zero, Interval.origin _⟩

/-- `-β₁ ≤ -3`, unsatisfiable within the unit box. -/
def beyondBox : HPolytope D (Vec D 2) :=
  ⟨1, fun _ j => if j = 0 then d (-1) 0 else d 0 0, fun _ => d (-3) 0, 0, fun i => i.elim0,
    fun i => i.elim0, fun _ => FloatOps.zero, fun _ => FloatOps.zero, Interval.origin _⟩

/-- `β₁ + β₂ ∈ [-1/2, 1/2]`, an equality row with slack, written as the two inequalities. -/
def slab : HPolytope D (Vec D 2) :=
  HPolytope.slab (q := 1) (fun _ _ => d 1 0) (fun _ => d (-1) (-1)) (fun _ => d 1 (-1))

/-- The unit square's generators with the constraint `P`. -/
def square (P : HPolytope D (Vec D 2)) : ConZonotope D (Vec D 2) :=
  ⟨2, ![d 0 0, d 0 0], ![![d 1 0, d 0 0], ![d 0 0, d 1 0]], P, box0⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The default right inverse of the square's generators. -/
def H₀ (P : HPolytope D (Vec D 2)) : Mat D 2 2 :=
  Zonotope.rightInvCandidate fun i j => (square P).G j i

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

end CORALean.Examples.ConZonotopeCertFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
