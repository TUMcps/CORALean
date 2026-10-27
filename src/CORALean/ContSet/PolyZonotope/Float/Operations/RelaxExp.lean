module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
public import CORALean.ContSet.PolyZonotope.Float.Operations.MergedGen
public import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxWidth
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `PolyZonotope.relaxExp`

The exact layer's `relaxExp`, rounded. Two things it computes are sums of stored
floats, the merged dependent column and the `ξ_E` copies of the relaxed one, and
each is stored downward with the gap to its upward rounding paid into the box,
as `compact` pays for merging columns.

`ξ_E` itself rounds nothing: `eDiff` is over ℕ in both layers, so the two layers
relax by the same width. The center is untouched, `ξ_c` being zero at
`ξ_G = ξ_E`, so nothing is added to the box beyond the two gaps.

## Inputs
* `pZ` – polynomial zonotope
* `part` – split with two selected generators
* `k₀` – factor index

## Output
* polynomial zonotope with the two generators relaxed into one
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}
open FloatOps


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The new independent generator as stored: `ξ_E` copies of the relaxed
generator, rounded down. -/
@[step_of PolyZonotope.relaxExp]
def PolyZonotope.step_relaxGen (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : Vec 𝕋 n :=
  fun i => nsmulDown (pZ.relaxWidth part k₀) (pZ.G (part.right 0) i)

/-- What the two stored columns can be off by, each the gap to the other
rounding direction of the same sum. -/
@[step_of PolyZonotope.relaxExp]
def PolyZonotope.step_relaxGap (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : Mat 𝕋 n 2 :=
  fun i =>
    ![subUp (addUp (pZ.G (part.right 1) i) (pZ.G (part.right 0) i)) (pZ.mergedGen part i),
      subUp (nsmulUp (pZ.relaxWidth part k₀) (pZ.G (part.right 0) i)) (pZ.step_relaxGen part k₀ i)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two generators `part.right` names merged into one, at the exponent
column of the second, the first scaled by `ξ_E` becoming independent. -/
def PolyZonotope.relaxExp (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : PolyZonotope (Vec 𝕋 n) where
  p := pZ.p
  h := d + 1
  q := pZ.q + 1
  c := pZ.c
  G := Fin.append (fun l => pZ.G (part.left l)) (fun _ => pZ.mergedGen part)
  E := fun k => Fin.append (fun l => pZ.E k (part.left l)) (fun _ => pZ.E k (part.right 1))
  GI := Fin.append pZ.GI (fun _ => pZ.step_relaxGen part k₀)
  I_error := pZ.I_error.plus (PolyZonotope.generatorError (pZ.step_relaxGap part k₀))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
