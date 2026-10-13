import CORALean.Global.EuclideanGenOpNorm
import CORALean.Global.Float.Sqrt

/-!
# The induced Euclidean norm of generators, bounded from above in floats

`genOpNorm₂ G` is Mathlib's `ℓ²` operator norm of the `n × h` matrix whose columns are the
generators. The float layer has no operator norm and no singular value, but
`genOpNorm₂_le_sum_norm₂` bounds it by the generators' own Euclidean lengths summed, and
`normUp` bounds each length from above. So `genOpNormUp` is `Σ_l normUp (G_l)`, rounded up:
looser than the tight constant by at most `√h`, and enough wherever the quantity bounded is a
tuning one, as [1]'s `Δε^h_k` is.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n h : ℕ}


/-- An upper bound on `genOpNorm₂` of generators known only in magnitude: their Euclidean
lengths, each from above by `normUp` with `p` Newton steps, summed upward. -/
def genOpNormUp (p : ℕ) (m : Fin h → Vec 𝕋 n) : 𝕋 :=
  sumUp fun l => normUp p (m l)

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem genOpNorm₂_le_genOpNormUp (p : ℕ) {G : Fin h → Vec ℝ n} {m : Fin h → Vec 𝕋 n}
    (hm : ∀ l j, |G l j| ≤ |toReal (m l j)|) :
    genOpNorm₂ G ≤ toReal (genOpNormUp p m) := by
  refine (genOpNorm₂_le_sum_norm₂ G).trans (le_trans (Finset.sum_le_sum fun l _ => ?_)
    (sum_le_sumUp _))
  exact norm₂_le_normUp p (hm l)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
