module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
public import CORALean.ContSet.PolyZonotope.Float.Operations.MergedGen
public import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxCentreEven
public import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGapEven
public import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGenEven
public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpEven

@[expose] public section

/-!
# `PolyZonotope.relaxExpEven`

The exact layer's `relaxExpEven`, rounded. `half` is exact, so the `ξ_E/2` the
recentring asks for costs nothing beyond what `ξ_E` copies of the generator
already cost: the width stays a count read off the exponent matrix, and both
layers relax by the same amount.

Three sums round here where `relaxExp` has two. The merged dependent column and
the halved independent one are stored downward; the recentred centre is a
subtraction, and it is stored downward too by taking the *upward* rounding of
the shift off it, so it stays below the exact centre and its gap is one-sided
like the others.

Each gap is the width between the two roundings of one expression, which is what
`generatorError` charges to the box — at coefficient `1` for the centre, at a
monomial or a zonotope coefficient for the two columns.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `relaxExp` with the drift's midpoint taken off the centre, so the new
independent generator carries only its radius. -/
def PolyZonotope.relaxExpEven (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : PolyZonotope (Vec 𝕋 n) where
  p := pZ.p
  h := d + 1
  q := pZ.q + 1
  c := pZ.relaxCentreEven part k₀
  G := Fin.append (fun l => pZ.G (part.left l)) (fun _ => pZ.mergedGen part)
  E := fun k => Fin.append (fun l => pZ.E k (part.left l)) (fun _ => pZ.E k (part.right 1))
  GI := Fin.append pZ.GI (fun _ => pZ.relaxGenEven part k₀)
  err := pZ.err.plus (PolyZonotope.generatorError (pZ.relaxGapEven part k₀))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
