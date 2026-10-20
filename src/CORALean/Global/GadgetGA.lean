module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Normed.Lp.PiLp

@[expose] public section

/-!
# The inbody generator matrix of the inapproximability reduction

`G_A = [[A, 0], [0ᵀ, -L]]` of [1, Lemma 27] (the paper's Eq. 65) for `A ∈ ℝ^{n×m}`, the generator
matrix of the inbody `E_p(G_A, n e_{n+1})`. Its coefficient space is `ℝ^{m+1}` with the `p`-norm,
written as the `p`-product of `ℝᵐ` (itself with the `p`-norm) and `ℝ`: the two give the same norm,
`(‖α'‖_pᵖ + |α_{m+1}|ᵖ)^{1/p}`, and the maximum at `p = ∞`. A coefficient `(α', s)` goes to
`(A α', -L s)`.

## Inputs
* `p` – norm exponent
* `A` – matrix to be reduced
* `L` – weight of the last coefficient

## Output
* the linear generator map of the inbody

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
      doi:10.1109/TAC.2025.3583624. arXiv:2404.11185.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped ENNReal
open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `α ↦ G_A α = (A α', -L s)` for `α = (α', s)`. -/
def gadgetGA (p : ℝ≥0∞) (A : Mat ℝ n m) (L : ℝ) :
    WithLp p (PiLp p (fun _ : Fin m => ℝ) × ℝ) →ₗ[ℝ] Vec ℝ n × ℝ where
  toFun α := (A *ᵥ WithLp.ofLp α.fst, -L * α.snd)
  map_add' α β := by
    refine Prod.ext ?_ ?_
    · show A *ᵥ (WithLp.ofLp α.fst + WithLp.ofLp β.fst) = _
      rw [Matrix.mulVec_add]; rfl
    · show -L * (α.snd + β.snd) = _
      rw [mul_add]; rfl
  map_smul' a α := by
    refine Prod.ext ?_ ?_
    · show A *ᵥ (a • WithLp.ofLp α.fst) = _
      rw [Matrix.mulVec_smul]; rfl
    · show -L * (a * α.snd) = a * (-L * α.snd)
      ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
