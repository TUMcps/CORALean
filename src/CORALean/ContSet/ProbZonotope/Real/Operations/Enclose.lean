import CORALean.ContSet.ProbZonotope.Real.Operations.Zonotope
import CORALean.ContSet.Zonotope.Real.Operations.LinComb
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# `ProbZonotope.enclose`

CORA's `enclose(probZ, Ar, Rtrans)` [1, Sec. VI]: the probabilistic zonotope enclosing `probZ`
and its image under `e^{Ar}`. Following CORA's printed steps: the uncertain zonotope
`Zaux = (e^{Ar} - I) zonotope(probZ) + Rtrans` (the confidence set at `m = probZ.gamma`, here the
argument `m`), `deltaZ = enclose(zonotope(0), Zaux)` (`Zonotope.linComb`, CORA's zonotope
`enclose`), `probZ + deltaZ` (added to the mean zonotope), and the covariance `e^{Ar} Σ e^{Ar}ᵀ`
when `trace(Ar) < 0` (CORA's `probZ.cov`, as `gauss` is set here). CORA's own comment says the
computation differs from the dissertation's. `Theorems.EncloseMeanOuter` is what the mean
zonotope guarantees; the covariance is not claimed to enclose anything.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ProbZonotope.enclose (P : ProbZonotope n) (Ar : Mat ℝ n n) (m : ℝ)
    (Rtrans : Vec ℝ n) : ProbZonotope n :=
  let expAr : Mat ℝ n n := NormedSpace.exp Ar
  let Zaux : Zonotope (Vec ℝ n) :=
    (Zonotope.mtimes (expAr - 1) (P.zonotope m)).plus ⟨0, Rtrans, Fin.elim0⟩
  let deltaZ : Zonotope (Vec ℝ n) := Zonotope.linComb ⟨0, 0, Fin.elim0⟩ Zaux
  { Z := P.Z.plus deltaZ
    cov := if Ar.trace < 0 then expAr * P.cov * expArᵀ else P.cov }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
