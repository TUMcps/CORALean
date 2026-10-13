module

public import CORALean.ContSet.PolyZonotope.Float.Operations.SubsGDiff
public import CORALean.ContSet.PolyZonotope.Float.Operations.SubsFactor
public import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
public import CORALean.ContSet.Interval.Float.Operations.Plus

@[expose] public section

/-!
# `PolyZonotope.subs`

CORA's `@polyZonotope/subs(pZ, pZin, idu)` on the stored floats: the dependent factors `idu` of
`pZ` are replaced by the outputs of `pZin`, whose own factors become factors of the result (shared
with `pZ`'s through `share`). One generator per term of each `Xprod`, stored rounded down with the
gap charged to the error box, as in `getSubset`; the replaced factors stay as zero rows, as in the
exact layer. Sound only where `pZin` has no independent generators and no error box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.subs (pZ : PolyZonotope (Vec 𝕋 n)) {nu : ℕ} (pZin : PolyZonotope (Vec 𝕋 nu))
    (idu : Fin nu → Fin pZ.p) (share : Fin pZin.p → Option (Fin pZ.p)) :
    PolyZonotope (Vec 𝕋 n) where
  p := pZ.p + pZin.p
  h := (pZ.subsTerms pZin idu).length
  q := pZ.q
  c := pZ.c
  G := fun l r => pZ.subsGDown pZin idu r l
  -- the exponents of `pZ`'s remaining factors, and those of the term in `pZin`'s factors
  E := fun r l =>
    Fin.addCases (fun k => if k ∈ Finset.univ.image idu then 0
      else pZ.E k ((pZ.subsTerms pZin idu).get l).1) (fun _ => 0) r
      + ∑ j ∈ Finset.univ.filter (fun j => pZ.subsFactor pZin share j = r),
          ((pZ.subsTerms pZin idu).get l).2.2 j
  GI := pZ.GI
  err := pZ.err.plus (PolyZonotope.generatorError (pZ.subsGDiff pZin idu))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
