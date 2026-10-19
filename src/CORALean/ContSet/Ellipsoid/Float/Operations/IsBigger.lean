module

public import CORALean.ContSet.Ellipsoid.Float.Operations.IsSymm
public import CORALean.ContSet.Ellipsoid.Float.Operations.Basic
public import CORALean.ContSet.Ellipsoid.Float.Operations.CholFactor
public import CORALean.ContSet.Ellipsoid.Float.Operations.PsdCheck

@[expose] public section

/-!
# `Ellipsoid.isBigger`, over a floating-point scalar

CORA's `@ellipsoid/isBigger` (`E₂` fits into `E₁` up to the centers) compares the shape matrices
by a simultaneous diagonalisation, which rounding cannot decide. What it decides is the Loewner
order `Q₂ ⪯ Q₁`, and that is what this certifies: both stored matrices symmetric, `Q₁ - Q₂`
bracketed entry by entry and checked positive semi-definite against the factor `cholFactor`
proposes (`psdCheck`), and `E₂`'s error box inside `E₁`'s. Only `true` is certain.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.isBigger (E₁ E₂ : Ellipsoid 𝕋 n) : Bool :=
  -- `Q₁ - Q₂`, entrywise between two roundings
  let D : Interval (Mat 𝕋 n n) :=
    ⟨fun i j => subDown (E₁.Q i j) (E₂.Q i j), fun i j => subUp (E₁.Q i j) (E₂.Q i j)⟩
  Ellipsoid.isSymm E₁.Q && Ellipsoid.isSymm E₂.Q &&
    Ellipsoid.psdCheck D (Ellipsoid.cholFactor 64 D.inf) &&
    (List.finRange n).all fun i =>
      le (E₁.I_error.inf i) (E₂.I_error.inf i) && le (E₂.I_error.sup i) (E₁.I_error.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
