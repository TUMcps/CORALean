module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE
public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic
public import Mathlib.Algebra.Module.Prod

@[expose] public section

/-!
# `ConPolyZono.extPolyZonotope`

The polynomial zonotope that `@conPolyZono/contains_` hands to `polyZonotope/contains_`: the
constraint rows appended below the generators, so that the constraint becomes a coordinate,

  `c = [c; -b]`, `G = blkdiag(G, A)`, `E = [E, R]`, `GI = [GI; 0]`,

whose last `m` coordinates `-b + A μ(α)` vanish exactly when the factors satisfy `A μ(α) = b`:
the lifted polynomial zonotope of [1, Lemma 1], with the independent block carried as `[GI; 0]`.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `polyZonotope([c; -b], blkdiag(G, A), [GI; 0], [E, R])`. -/
def ConPolyZono.extPolyZonotope (cPZ : ConPolyZono (Vec ℝ n)) :
    PolyZonotope (Vec ℝ n × Vec ℝ cPZ.m) where
  p := cPZ.p
  h := cPZ.h + cPZ.q
  q := cPZ.qI
  c := (cPZ.c, -cPZ.b)
  G := Fin.append (fun i => (cPZ.G i, 0)) (fun l => (0, ConPolyZono.consCol cPZ.A l))
  E := ConPolyZono.appendE cPZ.E cPZ.R
  GI := fun j => (cPZ.GI j, 0)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
