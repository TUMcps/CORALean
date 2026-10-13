module

public import CORALean.ContSet.ProbZonotope.Float.Operations.ReduceGirard
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceGirardOuter

@[expose] public section

/-!
# `ProbZonotope.reduceGirard` keeps the laws

Outer: every law of `P` is a law of the reduced model, as the mean zonotope grows and the
covariance is kept.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open MeasureTheory ProbabilityTheory Matrix WithLp FloatOps SoundFloatArithmetic
open scoped Pointwise

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.reduceGirard_laws_outer (P : ProbZonotope 𝕋 n) (o : ℕ) :
    P.laws ⊆ (P.reduceGirard o).laws := by
  rintro m ⟨μ, hμ, S, hS, hp, rfl⟩
  exact ⟨μ, Zonotope.reduceGirard_outer P.Z o hμ, S, hS, hp, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
