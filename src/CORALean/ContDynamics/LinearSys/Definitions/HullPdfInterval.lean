module

public import CORALean.ContDynamics.LinearSys.Definitions.HullPdf

@[expose] public section

/-!
# The enclosing probabilistic hull over a time interval

`[1, Def. 2]`, second display: `f̄_X(x, [0, r]) = sup {f̄_X(x, t) | t ∈ [0, r]}`, the supremum
of the hulls at the times of the interval (`LinearSys.hullPdf`).

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {n m : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `f̄_X(x, [0, r]) = sup {f̄_X(x, t) | t ∈ [0, r]}`. -/
noncomputable def LinearSys.hullPdfInterval (sys : LinearSys 𝕋 n) (C : Mat ℝ n m) (U : S n)
    (μ₀ : Vec ℝ n) (Sig₀ : Mat ℝ n n) (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup {f | ∃ t ∈ Set.Icc (0:ℝ) r, f = sys.hullPdf C U μ₀ Sig₀ t x}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
