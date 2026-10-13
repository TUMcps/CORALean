import Mathlib.Data.Real.Basic

/-!
# The recursion of the exact inverse remainder

[1, Eq. 36–37]: `Sⱼ(x) = (x - c)ʲ/((j+1) cʲ⁺¹) - j/(j+1)·Sⱼ₋₁(x)` from `S₀(x) = 1/c - 1/x`,
the integrals `∫_c^x (x - t)ʲ / tʲ⁺² dt` that integration by parts relates. The source calls
`a·Sⱼ` by the name `Rⱼ` of eq. (34) with `a` fixed at the top order `q`, which is how CORA's
`priv_inverse` computes it: the recursion on `Sⱼ`, then one multiplication by `a`.

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.invRemS (c : ℝ) : ℕ → ℝ → ℝ
  | 0, x => c⁻¹ - x⁻¹
  | j + 1, x =>
    (x - c) ^ (j + 1) / ((j + 2) * c ^ (j + 2)) - (j + 1) / (j + 2) * Taylm.invRemS c j x

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
