module

public import CORALean.ContSet.SpectraShadow.Real.Theorems.TraceMulNonneg
public import CORALean.ContSet.SpectraShadow.Real.Theorems.TraceLmiMul
public import CORALean.Global.LinProg.LinProg

@[expose] public section

/-!
# `SpectraShadow.supportBound`

Weak duality of the semidefinite program behind CORA's `@spectraShadow/supportFunc_`: a positive
semidefinite `Y` with `tr(Aᵢ Y) = -c(Gᵢ)` for every `i` bounds the functional `c` by
`c(c₀) + tr(A₀ Y)` on the whole set. The certificate `Y` is an argument, as the dual weights of
`HPolytope.supportBound` are, so a solver stays outside the trusted base. The bound equals the
supremum under complementary slackness (`SpectraShadow.supportFunc_eq_of_complementary`), which
is not claimed in general. CORA's `'lower'` and `'range'` types and the maximiser are not
modelled.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The bound `c(c₀) + tr(A₀ Y)` that a dual certificate `Y` proves. -/
def SpectraShadow.supportBound (S : SpectraShadow α) (c : α →ₗ[ℝ] ℝ) (Y : Mat ℝ S.k S.k)
    (hY : Y.PosSemidef) (hc : ∀ i, (S.A i * Y).trace = - c (S.G i)) :
    SupportBound S.construct c where
  val := c S.c + (S.A₀ * Y).trace
  le := by
    rintro _ ⟨β, hβ, rfl⟩
    -- the inequality's matrix against `Y` is nonnegative
    have h0 := SpectraShadow.trace_mul_nonneg hβ hY
    rw [SpectraShadow.trace_lmi_mul] at h0
    -- and the certificate turns each coefficient trace into `-c(Gᵢ)`
    have hs : ∑ i, β i * (S.A i * Y).trace = - ∑ i, β i * c (S.G i) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [hc i]; ring
    rw [hs] at h0
    rw [map_add, map_sum]
    simp only [map_smul, smul_eq_mul]
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
