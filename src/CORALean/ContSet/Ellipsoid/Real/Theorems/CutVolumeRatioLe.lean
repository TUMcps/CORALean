import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.ContSet.Ellipsoid.Real.Theorems.CutVolumeLe
import CORALean.ContSet.Ellipsoid.Real.Theorems.VolumeMtimes
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The cut ellipsoid shrinks the volume by a constant factor in any frame

[1, Eq. 19]: in iteration `j` the map `Φ` takes `E(Eⱼ, 0)` to the unit ball, and the cut
gives `E(E, 0)`, so `Eⱼ₊₁ = Φ⁻¹ E(E, 0)` and `Eⱼ = Φ⁻¹ B`, and
`vol(Eⱼ₊₁)/vol(Eⱼ) = vol(E)/vol(B) ≤ κ_ε`, the `κ_ε` of [1, Lemma 4.4]. Stated for any square
`M = Φ⁻¹`: the ratio is the same as in the unit frame (`vol(M E) vol(B) = vol(E) vol(M B)`), and
at most `κ_ε` (`volume_mtimes`). The cut needs `n ≥ 2`.

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix
open scoped MatrixOrder

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 19]: `vol(M E)/vol(M B) = vol(E)/vol(B) ≤ κ_ε`, for every square `M`. -/
theorem Ellipsoid.cut_volume_ratio_le {ε : ℝ} (hε : 0 < ε) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∀ (n : ℕ) (c : Vec ℝ n), 2 ≤ n → c ⬝ᵥ c = 1 → ∀ M : Mat ℝ n n,
      (Ellipsoid.mtimes M (Ellipsoid.ofShape (Ellipsoid.cutShape n c
          (1 / Real.sqrt ((n : ℝ) * (1 + ε)))) 0)).volume
          * (Ellipsoid.ofShape (1 : Mat ℝ n n) 0).volume
        = (Ellipsoid.ofShape (Ellipsoid.cutShape n c
            (1 / Real.sqrt ((n : ℝ) * (1 + ε)))) 0).volume
          * (Ellipsoid.mtimes M (Ellipsoid.ofShape (1 : Mat ℝ n n) 0)).volume
      ∧ (Ellipsoid.mtimes M (Ellipsoid.ofShape (Ellipsoid.cutShape n c
          (1 / Real.sqrt ((n : ℝ) * (1 + ε)))) 0)).volume
        ≤ ENNReal.ofReal κ
          * (Ellipsoid.mtimes M (Ellipsoid.ofShape (1 : Mat ℝ n n) 0)).volume := by -- --- PROOF ---
  obtain ⟨κ, hκ0, hκ1, hκ⟩ := Ellipsoid.cut_volume_le hε
  refine ⟨κ, hκ0, hκ1, fun n c hn hc M => ⟨?_, ?_⟩⟩
  · -- both products are `|det M|` times `vol(E) vol(B)`
    rw [Ellipsoid.volume_mtimes, Ellipsoid.volume_mtimes]
    ring
  · rw [Ellipsoid.volume_mtimes, Ellipsoid.volume_mtimes, mul_left_comm]
    exact mul_le_mul_right (hκ n c hn hc) _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
