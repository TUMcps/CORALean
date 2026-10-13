import CORALean.ContSet.ConZonotope.Real.Operations.KeepEmbed
import CORALean.ContSet.ConZonotope.Real.Operations.KeepSlack

/-!
# `ConZonotope.keepRows`

The constraints on the kept coefficients: every row of `P`, read at a point whose
dropped coefficients are zero and loosened by what the dropped ones can add
(`keepSlack`). An equality `a · β = b` becomes the pair `a · β ≤ b + s` and
`-a · β ≤ -b + s`.

Each row is projected on its own, so this is an outer approximation of the exact
projection of `P` onto the kept coordinates, not the projection itself: the
Fourier-Motzkin combination of rows is not formed. It is exact on a row the
dropped coordinates do not enter, and in particular on a polytope that leaves them
unconstrained, which is the case `reduceKeep`'s ranking drops first.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {h q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Rows first, then each equality twice, as `≤`; no equalities remain. -/
noncomputable def ConZonotope.keepRows (P : HPolytope (Vec ℝ h))
    (part : Split (Fin h) into (Fin q) ⊕ (Fin r)) : HPolytope (Vec ℝ q) where
  m := P.m + (P.me + P.me)
  A := Fin.append (fun i => (P.A i).comp (ConZonotope.keepEmbed part))
    (Fin.append (fun i => (P.Ae i).comp (ConZonotope.keepEmbed part))
      (fun i => -((P.Ae i).comp (ConZonotope.keepEmbed part))))
  b := Fin.append (fun i => P.b i + ConZonotope.keepSlack part (P.A i))
    (Fin.append (fun i => P.be i + ConZonotope.keepSlack part (P.Ae i))
      (fun i => -P.be i + ConZonotope.keepSlack part (P.Ae i)))
  me := 0
  Ae := fun i => i.elim0
  be := fun i => i.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
