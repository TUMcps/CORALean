import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.Global.EuclideanNorm

/-!
# `Zonotope.dcos`

The cosine of [1, Eq. (4)]: `dcos(gᵢ, gⱼ) = sign(gᵢ(1) gⱼ(1)) gᵢᵀgⱼ / √((gᵢᵀgᵢ)(gⱼᵀgⱼ))`, with
`sign x = -1` if `x < 0` and `1` otherwise ([1, Sec. II-A]). The paper says it is the cosine
of the angle between `sign(gᵢ(1)) gᵢ` and `sign(gⱼ(1)) gⱼ`; see `dcos_ne_cosSigned`.

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the
      Order Reduction of Zonotopes". IEEE Control Systems Letters, 9:1730-1735, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} [NeZero n]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. (4)], as printed. A zero generator gives `0/0 = 0`. -/
noncomputable def Zonotope.dcos (gi gj : Vec ℝ n) : ℝ :=
  (if gi 0 * gj 0 < 0 then -1 else 1) * dotProduct gi gj
    / Real.sqrt (dotProduct gi gi * dotProduct gj gj)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
