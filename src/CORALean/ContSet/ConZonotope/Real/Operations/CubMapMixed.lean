import CORALean.ContSet.ConZonotope.Real.ConZonotope
import CORALean.ContSet.ConZonotope.Real.Operations.CubLinearAt
import CORALean.ContSet.Zonotope.Real.Operations.CubMapMixed
import CORALean.ContSet.HPolytope.Real.Operations.Comap
import CORALean.ContSet.HPolytope.Real.Operations.Intersection

/-!
# `ConZonotope.cubMapMixed`

The mixed form of CORA's `@conZonotope/cubMap` (`aux_cubMapMixed`): the generators of
`Zonotope.cubMapMixed`, with the constraints of each of the three sets on its own linear
generators, `((0, 0), a)`, `((0, b), 0)` and `((j, 0), 0)`, and every other factor unconstrained.
The remark on `removeRedundantExponents` in `ConZonotope.cubMap` applies here as well.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_cubMapMixed`: `Zonotope.cubMapMixed`, each set's constraints on its linear generators. -/
noncomputable def ConZonotope.cubMapMixed (T : Fin m → Fin n → Mat ℝ n n)
    (cZ₁ cZ₂ cZ₃ : ConZonotope (Vec ℝ n)) : ConZonotope (Vec ℝ m) :=
  let Z : Zonotope (Vec ℝ m) :=
    Zonotope.cubMapMixed T ⟨cZ₁.h, cZ₁.c, cZ₁.G⟩ ⟨cZ₂.h, cZ₂.c, cZ₂.G⟩ ⟨cZ₃.h, cZ₃.c, cZ₃.G⟩
  { h := Z.h
    c := Z.c
    G := Z.G
    P := ((cZ₁.P.comap (ConZonotope.cubLinearAt (cZ₃.h + 1) (cZ₂.h + 1) (cZ₁.h + 1)
            (fun a : Fin cZ₁.h => ((0, 0), a.succ)))).intersection
          (cZ₂.P.comap (ConZonotope.cubLinearAt (cZ₃.h + 1) (cZ₂.h + 1) (cZ₁.h + 1)
            (fun b : Fin cZ₂.h => ((0, b.succ), 0))))).intersection
        (cZ₃.P.comap (ConZonotope.cubLinearAt (cZ₃.h + 1) (cZ₂.h + 1) (cZ₁.h + 1)
            (fun j : Fin cZ₃.h => ((j.succ, 0), 0)))) }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
