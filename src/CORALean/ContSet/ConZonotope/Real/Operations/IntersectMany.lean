import CORALean.ContSet.ConZonotope.Real.Operations.Intersection
import Mathlib.Algebra.BigOperators.Fin

/-!
# `ConZonotope.intersectMany`

The constrained zonotope that [1, Lemma 4] gives for the intersection of `d + 1` constrained
zonotopes `Cⱼ = ⟨cⱼ, Gⱼ, Aⱼ, bⱼ⟩`, in one step rather than pair by pair: the first set's centre
and generators, followed by zeros for the others' `d` coefficient blocks; each set's own constraints
on its own block; and one block of `n` rows per further set pinning its point to the first,
`G₁ β₁ - Gⱼ βⱼ = cⱼ - c₁` (eqs. 33-34). The blocks' lengths differ, so the later ones are
indexed by the sigma type of the sets, `finSigmaFinEquiv` order.

## References

* [1] A. Alanwar, V. Gaßmann, X. He, H. Said, H. Sandberg, K. H. Johansson and M. Althoff.
      "Privacy-Preserving Set-Based Estimation Using Partially Homomorphic Encryption".
      European Journal of Control, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Lemma 4]: `C₀ ∩ C₁ ∩ ⋯ ∩ C_d`, exactly, in one step. -/
def ConZonotope.intersectMany (cs : Fin (d + 1) → ConZonotope (Vec ℝ n)) :
    ConZonotope (Vec ℝ n) where
  h := (cs 0).h + ∑ j : Fin d, (cs j.succ).h
  c := (cs 0).c                                                  -- eq. 33
  G := Fin.append (cs 0).G 0
  P := ((Fin.foldl d (fun P j => P.intersection                  -- each block's own constraints
          ((cs j.succ).P.comap (LinearMap.funLeft ℝ ℝ fun t => Fin.natAdd (cs 0).h
            (finSigmaFinEquiv (⟨j, t⟩ : (j : Fin d) × Fin (cs j.succ).h)))))
        ((cs 0).P.comap (blockLeft (cs 0).h _))).intersection
      (HPolytope.eqs                                             -- the agreement rows, eq. 34
        (fun q => Fin.append (fun t => (cs 0).G t (finProdFinEquiv.symm q).2)
          fun u => -(if (finSigmaFinEquiv.symm u).1 = (finProdFinEquiv.symm q).1 then 1 else 0)
            * (cs (finSigmaFinEquiv.symm u).1.succ).G (finSigmaFinEquiv.symm u).2
              (finProdFinEquiv.symm q).2)
        fun q => (cs (finProdFinEquiv.symm q).1.succ).c (finProdFinEquiv.symm q).2
          - (cs 0).c (finProdFinEquiv.symm q).2))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
