module

public import CORALean.ContSet.ProbZonotope.Float.Operations.Basic
public import CORALean.ContSet.ProbZonotope.Float.Theorems.ZonotopeOuter
public import CORALean.ContSet.ProbZonotope.Real.Theorems.SupIsLUB
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# `ProbZonotope.sup` bounds the real `sup`

For a law of the float probabilistic zonotope, the exact confidence set lies in the float zonotope
(`ProbZonotope.zonotope_outer`) and so in its box, so every entry of a point is within the largest
magnitude of the box. The real `sup` is the least upper bound of the sup-norm over the exact set
(`sup_isLUB`), hence below it.

## Inputs
* `p` – natural number
* `P` – probabilistic zonotope
* `M` – scalar
* `μ` – mean of length `n`
* `S` – `n × n` matrix
* `m` – real number

## Hypotheses
* `hμ` – `μ` lies in `P.Z`
* `hS` – `S` lies in `P.cov`
* `hpsd` – `S.PosSemidef`
* `hm` – `0 ≤ m`
* `hmM` – `m ≤ toReal M`

## Conclusion
* the real `sup` of the exact probabilistic zonotope is at most the value returned
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.sup_le (p : ℕ) (P : ProbZonotope 𝕋 n) (M : 𝕋) {μ : Vec ℝ n}
    (hμ : μ ∈ P.Z.construct) {S : Mat ℝ n n} (hS : S ∈ P.cov.construct) (hpsd : S.PosSemidef)
    {m : ℝ} (hm : 0 ≤ m) (hmM : m ≤ toReal M) : -- --- CONCL ---
    Real.ProbZonotope.sup ⟨⟨0, μ, fun j => j.elim0⟩, S⟩ m
      ≤ toReal (P.sup p M) := by -- --- PROOF ---
  -- the exact confidence set lies in the float box
  have hsub : (Real.ProbZonotope.zonotope ⟨⟨0, μ, fun j => j.elim0⟩, S⟩ m).construct
      ⊆ (P.interval p M).construct :=
    (ProbZonotope.zonotope_outer p P M hμ hS hpsd hm hmM).trans
      (P.zonotope p M).interval_contains
  refine (Real.ProbZonotope.sup_isLUB _ m).2 ?_
  rintro _ ⟨x, hx, rfl⟩
  -- every entry is within the largest magnitude of the box
  have hent : ∀ i, |x i| ≤ toReal (P.sup p M) := fun i => by
    refine le_trans ?_ (le_maximumOver (P.interval p M).normMag i)
    rw [Interval.normMag, toReal_maximum, toReal_absolute, toReal_absolute]
    exact abs_le_max_abs_abs (hsub hx i).1 (hsub hx i).2
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Subsingleton.elim x 0, ProbZonotope.sup, maximumOver, toReal_zero]
  · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact (pi_norm_le_iff_of_nonempty _).mpr fun i => by
      rw [Real.norm_eq_abs]
      exact hent i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
