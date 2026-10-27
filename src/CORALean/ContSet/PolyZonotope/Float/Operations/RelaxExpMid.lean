module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
public import CORALean.ContSet.PolyZonotope.Float.Operations.MergedGen
public import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxDrift
public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMid
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `PolyZonotope.relaxExpMid`

The exact layer's `relaxExpMid`, rounded. The bracket `eDrift` reads is a pair of counts, so
the midpoint and the half-width are halves of natural multiples of one stored generator: `half`
is exact and the two layers shift and pay the same amount. The shift has no sign to case on, so
it is stored at its lower rounding and added to the center downward; its gap is the distance up
to the sum at the shift's *upper* rounding. Three sums round: the merged dependent column, the
halved independent one and the shifted center, each gap charged by `generatorError`.

## Inputs
* `pZ` – polynomial zonotope
* `part` – split with two selected generators
* `k₀` – factor index

## Output
* relaxed polynomial zonotope with midpoint center shift
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}
open FloatOps


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The center shift as stored: half the upward reach less half the downward
one, in copies of the relaxed generator, rounded down. -/
@[step_of PolyZonotope.relaxExpMid]
def PolyZonotope.step_relaxShiftMid (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : Vec 𝕋 n :=
  fun i => half (subDown (nsmulDown (pZ.relaxDrift part k₀).2 (pZ.G (part.right 0) i))
    (nsmulUp (pZ.relaxDrift part k₀).1 (pZ.G (part.right 0) i)))

/-- The same shift rounded up, which the center's gap reads. -/
@[step_of PolyZonotope.relaxExpMid]
def PolyZonotope.step_relaxShiftMidUp (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : Vec 𝕋 n :=
  fun i => half (subUp (nsmulUp (pZ.relaxDrift part k₀).2 (pZ.G (part.right 0) i))
    (nsmulDown (pZ.relaxDrift part k₀).1 (pZ.G (part.right 0) i)))

/-- The same fold rounded up, which only that column's gap reads. -/
@[step_of PolyZonotope.relaxExpMid]
def PolyZonotope.step_relaxGenMidUp (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : Vec 𝕋 n :=
  fun i => half (nsmulUp ((pZ.relaxDrift part k₀).1 + (pZ.relaxDrift part k₀).2)
    (pZ.G (part.right 0) i))

/-- The new independent column as stored: half of as many copies of the relaxed
generator as the bracket is wide, rounded down. -/
@[step_of PolyZonotope.relaxExpMid]
def PolyZonotope.step_relaxGenMid (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : Vec 𝕋 n :=
  fun i => half (nsmulDown ((pZ.relaxDrift part k₀).1 + (pZ.relaxDrift part k₀).2)
    (pZ.G (part.right 0) i))

/-- The shifted center as stored, the shift added at its lower rounding, so the
stored center stays below the exact one. -/
@[step_of PolyZonotope.relaxExpMid]
def PolyZonotope.step_relaxCenterMid (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : Vec 𝕋 n :=
  fun i => addDown (pZ.c i) (pZ.step_relaxShiftMid part k₀ i)

/-- What the merged column, the halved column and the shifted center can each be
off by, every one of them a gap between two roundings of one expression. -/
@[step_of PolyZonotope.relaxExpMid]
def PolyZonotope.step_relaxGapMid (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : Mat 𝕋 n 3 :=
  fun i =>
    ![subUp (addUp (pZ.G (part.right 1) i) (pZ.G (part.right 0) i)) (pZ.mergedGen part i),
      subUp (pZ.step_relaxGenMidUp part k₀ i) (pZ.step_relaxGenMid part k₀ i),
      subUp (addUp (pZ.c i) (pZ.step_relaxShiftMidUp part k₀ i)) (pZ.step_relaxCenterMid part k₀ i)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two generators `part.right` names merged into one, the drift's midpoint
moved into the center and its half-width into a new independent generator. -/
def PolyZonotope.relaxExpMid (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : PolyZonotope (Vec 𝕋 n) where
  p := pZ.p
  h := d + 1
  q := pZ.q + 1
  c := pZ.step_relaxCenterMid part k₀
  G := Fin.append (fun l => pZ.G (part.left l)) (fun _ => pZ.mergedGen part)
  E := fun k => Fin.append (fun l => pZ.E k (part.left l)) (fun _ => pZ.E k (part.right 1))
  GI := Fin.append pZ.GI (fun _ => pZ.step_relaxGenMid part k₀)
  I_error := pZ.I_error.plus (PolyZonotope.generatorError (pZ.step_relaxGapMid part k₀))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
