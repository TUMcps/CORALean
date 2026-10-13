module

public import CORALean.ContSet.ProbZonotope.Float.Operations.Abs
public import CORALean.ContSet.Zonotope.Float.Theorems.AbsNominal
public import CORALean.ContSet.ProbZonotope.Real.Operations.Abs

@[expose] public section

/-!
# `ProbZonotope.abs` holds the real `abs`'s laws

Outer: for a real probabilistic zonotope whose mean zonotope is the nominal part of `P.Z` and
whose covariance is a positive semidefinite matrix of the covariance interval, every law of the
real `abs` is a law of the float `abs`, provided the error box of the means holds `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.abs_laws_outer (P : ProbZonotope 𝕋 n)
    (h0 : ∀ i, toReal (P.Z.E.inf i) ≤ 0 ∧ 0 ≤ toReal (P.Z.E.sup i))
    {S : Mat ℝ n n} (hS : S ∈ P.cov.construct) (hp : S.PosSemidef) :
    (CORALean.Real.ProbZonotope.abs ⟨nominal P.Z, S⟩).laws ⊆ P.abs.laws := by -- --- PROOF ---
  rintro _ ⟨μ, hμ, rfl⟩
  have hμ' : μ ∈ nominalSet P.Z.abs := by
    have : μ ∈ (CORALean.Real.Zonotope.abs (nominal P.Z)).construct := hμ
    rw [← Zonotope.abs_nominal] at this
    exact this
  exact ⟨μ, ⟨_, hμ', 0, h0, add_zero _⟩, S, hS, hp, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
