import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
import CORALean.ContSet.PolyZonotope.Float.Operations.MergedGen
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxCentreEven
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGapEven
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGenEven
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpEven

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

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `relaxExp` with the drift's midpoint taken off the centre, so the new
independent generator carries only its radius. -/
def PolyZonotope.relaxExpEven (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin PZ.p) : PolyZonotope 𝕋 n where
  p := PZ.p
  h := d + 1
  q := PZ.q + 1
  c := PZ.relaxCentreEven part k₀
  G := fun i => Fin.append (fun l => PZ.G i (part.left l)) (fun _ => PZ.mergedGen part i)
  E := fun k => Fin.append (fun l => PZ.E k (part.left l)) (fun _ => PZ.E k (part.right 1))
  GI := fun i => Fin.append (PZ.GI i) (fun _ => PZ.relaxGenEven part k₀ i)
  err := PZ.err.plus (PolyZonotope.generatorError (PZ.relaxGapEven part k₀))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
