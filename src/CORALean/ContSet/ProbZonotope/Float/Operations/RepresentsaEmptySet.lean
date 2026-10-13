import CORALean.ContSet.ProbZonotope.Float.ProbZonotope

/-!
# `ProbZonotope.representsaEmptySet`, over a floating-point scalar

CORA's `representsa(P, 'emptySet')`, answered one-sidedly. CORA answers `false`, the mean zonotope
holding its centre; here `true` only if some covariance entry's interval is crossed (`ltStrict` on
its ends), which no matrix lies in, so there is no law. `false` refutes nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ProbZonotope.representsaEmptySet (P : ProbZonotope 𝕋 n) : Bool :=
  (List.finRange n).any fun i => (List.finRange n).any fun j =>
    ltStrict (P.cov.sup i j) (P.cov.inf i j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
