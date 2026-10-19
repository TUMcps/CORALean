module

public import CORALean.ContSet.PolyLevelSet.Float.PolyLevelSet

@[expose] public section

/-!
# `PolyLevelSet.switch` over a floating-point scalar

Each row's right-hand side `bᵢ` taken at the weight `(1 + σᵢ x^e) / 2`, as over ℝ: the column of
the new monomial is `∓ bᵢ / 2` and the right-hand side `bᵢ / 2`, both by `half`, which is exact,
so nothing rounds, the slack stands, and the rows read back as `Real.PolyLevelSet.switch`
(`eval_nominalCore_switch`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Row `i` with `bᵢ` weighted by `(1 + σᵢ x^e) / 2`, `σᵢ = 1` where `s i`, its slack kept. -/
def PolyLevelSet.switch (P : PolyLevelSet 𝕋 n) (e : Fin n → ℕ) (s : Fin P.m → Bool) :
    PolyLevelSet 𝕋 n where
  m := P.m
  q := P.q + 1
  A i := Fin.append (P.A i) fun _ => if s i then neg (half (P.b i)) else half (P.b i)
  R k := Fin.append (P.R k) fun _ => e k
  b i := half (P.b i)
  b_error := P.b_error
  op := P.op
  dom := P.dom

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
