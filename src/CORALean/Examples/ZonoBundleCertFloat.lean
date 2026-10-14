import CORALean.ContSet.ZonoBundle.Float.Theorems.IsFullDimSound
import CORALean.ContSet.ZonoBundle.Float.Theorems.RepresentsaEmptySetSound
import CORALean.ContSet.Zonotope.Float.Theorems.IsFullDimSound
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.Specification.Instances

/-!
# Certificates for a zonotope bundle, run

At `Dyadic 53`. A bundle is the intersection of its members. A flat box and a thin
parallelogram that meet near the origin form a full-dimensional bundle — certified at a point
strictly inside every member — and not an empty one; two unit segments five apart have no
common point, and the bundle is certified empty.

Each `true` is a guarantee (`ZonoBundle.isFullDim_sound`,
`ZonoBundle.representsa_emptySet_sound`); a `false` decides nothing.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.ZonoBundleCertFloat

open CORALean CORALean.Float FloatOps

abbrev D := Dyadic 53

/-- `m · 2 ^ e`. -/
def d (m e : ℤ) : D := ⟨m, e⟩

/-- No rounding error. -/
def box0 : Interval (Vec D 2) := ⟨fun _ => d 0 0, fun _ => d 0 0⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A flat box and a thin parallelogram, which meet near the origin. -/
def bundle : ZonoBundle (Vec D 2) :=
  ⟨2, ![⟨2, ![d 0 0, d 0 0], ![![d 2 0, d 0 0], ![d 0 0, d 1 (-3)]], box0⟩,
        ⟨2, ![d 0 0, d 0 0], ![![d 2 0, d 2 0], ![d 1 (-3), d (-1) (-3)]], box0⟩]⟩

/-- Two unit segments five apart. -/
def apart : ZonoBundle (Vec D 2) :=
  ⟨2, ![⟨1, ![d 0 0, d 0 0], ![![d 1 0, d 0 0]], box0⟩,
        ⟨1, ![d 5 0, d 0 0], ![![d 1 0, d 0 0]], box0⟩]⟩

#eval bundle.isFullDim (fun i => Zonotope.rightInvCandidate fun r j => (bundle.Z i).G j r)
  ![d 0 0, d 0 0]  -- true
#eval bundle.representsa_emptySet   -- false
#eval apart.representsa_emptySet    -- true

end CORALean.Examples.ZonoBundleCertFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
