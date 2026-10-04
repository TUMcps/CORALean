import CORALean.ContSet.Taylm.Float.Taylm

/-!
# `Taylm.representsa_point`, over a floating-point scalar

CORA's `representsa(T, 'point')`, a sufficient test: `true` only if in every component each term
of positive degree has coefficient `0` and the remainder is `[0, 0]` (`le` on the absolute values,
certified `true` only). The range set is then within the single point of the constant terms.
`false` refutes nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.representsa_point (T : Fin m → Taylm 𝕋 n) : Bool :=
  (List.finRange m).all fun i =>
    (T i).terms.all (fun a => decide (∀ k, a.2 k = 0) || le (absolute a.1) zero)
      && le (absolute (T i).remInf) zero && le (absolute (T i).remSup) zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
