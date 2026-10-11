import CORALean.Global.Tensor
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# The gadget matrix of the inapproximability reduction

[1, Eq. 63]: `H = [[Iₙ, -Iₙ], [1ᵀ, 1ᵀ]] ∈ ℝ^{(n+1)×2n}` (the paper's Eq. 62), the generator matrix
of the circumbody `Ẑ = {H β | ‖β‖_∞ ≤ 1, β ≥ 0}` through which the `p ↦ 1` matrix norm reduces to an
ellipsotope-in-zonotope containment. Written as a map `ℝⁿ × ℝⁿ → ℝⁿ × ℝ`: a coefficient
`β = (β₁, β₂)` goes to `(β₁ - β₂, 1ᵀβ₁ + 1ᵀβ₂)`, the first `n` rows and the last one. Product
norms are maxima, so the supremum norm of `(β₁, β₂)` is that of `β ∈ ℝ^{2n}`.

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
      doi:10.1109/TAC.2025.3583624. arXiv:2404.11185.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `β ↦ H β` for `H = [[Iₙ, -Iₙ], [1ᵀ, 1ᵀ]]`. -/
def gadgetH (n : ℕ) : (Vec ℝ n × Vec ℝ n) →ₗ[ℝ] Vec ℝ n × ℝ where
  toFun β := (β.1 - β.2, ∑ i, β.1 i + ∑ i, β.2 i)
  map_add' β γ := by
    refine Prod.ext ?_ ?_
    · funext i; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.sub_apply]; ring
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib]; ring
  map_smul' a β := by
    refine Prod.ext ?_ ?_
    · funext i; simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul, RingHom.id_apply, Prod.smul_mk]; ring
    · simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
        Prod.smul_mk, ← Finset.mul_sum]; ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
