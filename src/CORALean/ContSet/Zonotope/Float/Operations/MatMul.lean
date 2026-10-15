module

public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Zonotope.Float.Operations.OfEntryBoundsMat

@[expose] public section

/-!
# `Zonotope.matMul`

The exact layer's `Zonotope.matMul`, which is `bilin` at the matrix product [1, Eq. (10)]:
center `C₁C₂`, then `G₁ᵢC₂`, `C₁G₂ⱼ` and every cross product `G₁ᵢG₂ⱼ`, each bracketed by
`matMulDown`/`matMulUp` and stored low by `ofEntryBoundsMat`. The boxes cannot be multiplied
as generators, so for `(a + e)(b + f) = ab + af + e(b + f)` the two error terms are taken
as interval products: `a` in the box around the first nominal part, `b + f` in the second
factor's `interval`.

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   09-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {p q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `bilin`'s center and generators at the matrix product, bracketed, plus the two error
terms as interval products. -/
def Zonotope.matMul (M : Zonotope (Mat 𝕋 p q)) (N : Zonotope (Mat 𝕋 q r)) :
    Zonotope (Mat 𝕋 p r) :=
  let gens : (Mat 𝕋 p q → Mat 𝕋 q r → Mat 𝕋 p r) → Fin (M.h + N.h + M.h * N.h) → Mat 𝕋 p r :=
    fun mul => Fin.append (Fin.append (fun i => mul (M.G i) N.c) (fun j => mul M.c (N.G j)))
      (fun k => mul (M.G (finProdFinEquiv.symm k).1) (N.G (finProdFinEquiv.symm k).2))
  -- the box around `a`, the first nominal part, then the two error terms `af + eB`
  let IM := ({ M with I_error := Interval.point fun _ _ => zero } : Zonotope
      (Mat 𝕋 p q)).matInterval
  let E := Interval.matPlus (Interval.matMul IM N.I_error) (Interval.matMul M.I_error N.matInterval)
  Zonotope.ofEntryBoundsMat (matMulDown M.c N.c) (matMulUp M.c N.c) (gens matMulDown)
    (gens matMulUp) E

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
