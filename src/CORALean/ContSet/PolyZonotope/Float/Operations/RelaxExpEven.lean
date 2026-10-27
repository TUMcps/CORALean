module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
public import CORALean.ContSet.PolyZonotope.Float.Operations.MergedGen
public import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxWidth
public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpEven
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `PolyZonotope.relaxExpEven`

The exact layer's `relaxExpEven`, rounded. `half` is exact, so the `ξ_E/2` the
recentering asks for costs nothing beyond what `ξ_E` copies of the generator
already cost: both layers relax by the same amount.

Three sums round here where `relaxExp` has two. The merged dependent column and
the halved independent one are stored downward; the recentered center is stored
downward too, by taking the *upward* rounding of the shift off it. Each gap is
charged to the box by `generatorError`.

## Inputs
* `pZ` – polynomial zonotope
* `part` – split with two selected generators
* `k₀` – factor index

## Output
* relaxed polynomial zonotope with even-exponent center shift
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

/-- The same fold rounded up, which only the center and the gaps read. -/
@[step_of PolyZonotope.relaxExpEven]
def PolyZonotope.step_relaxGenEvenUp (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : Vec 𝕋 n :=
  fun i => half (nsmulUp (pZ.relaxWidth part k₀) (pZ.G (part.right 0) i))

/-- Half of `ξ_E` copies of the relaxed generator, rounded down: the new
independent column, and the size of the center shift. -/
@[step_of PolyZonotope.relaxExpEven]
def PolyZonotope.step_relaxGenEven (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : Vec 𝕋 n :=
  fun i => half (nsmulDown (pZ.relaxWidth part k₀) (pZ.G (part.right 0) i))

/-- The recentered center as stored: the shift taken off at its upper rounding,
so the stored center stays below the exact one. -/
@[step_of PolyZonotope.relaxExpEven]
def PolyZonotope.step_relaxCenterEven (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : Vec 𝕋 n :=
  fun i => subDown (pZ.c i) (pZ.step_relaxGenEvenUp part k₀ i)

/-- What the merged column, the halved column and the recentered center can each
be off by, every one of them a gap between two roundings of one expression. -/
@[step_of PolyZonotope.relaxExpEven]
def PolyZonotope.step_relaxGapEven (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : Mat 𝕋 n 3 :=
  fun i =>
    ![subUp (addUp (pZ.G (part.right 1) i) (pZ.G (part.right 0) i)) (pZ.mergedGen part i),
      subUp (pZ.step_relaxGenEvenUp part k₀ i) (pZ.step_relaxGenEven part k₀ i),
      subUp (subUp (pZ.c i) (pZ.step_relaxGenEven part k₀ i)) (pZ.step_relaxCenterEven part k₀ i)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `relaxExp` with the drift's midpoint taken off the center, so the new
independent generator carries only its radius. -/
def PolyZonotope.relaxExpEven (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : PolyZonotope (Vec 𝕋 n) where
  p := pZ.p
  h := d + 1
  q := pZ.q + 1
  c := pZ.step_relaxCenterEven part k₀
  G := Fin.append (fun l => pZ.G (part.left l)) (fun _ => pZ.mergedGen part)
  E := fun k => Fin.append (fun l => pZ.E k (part.left l)) (fun _ => pZ.E k (part.right 1))
  GI := Fin.append pZ.GI (fun _ => pZ.step_relaxGenEven part k₀)
  I_error := pZ.I_error.plus (PolyZonotope.generatorError (pZ.step_relaxGapEven part k₀))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
