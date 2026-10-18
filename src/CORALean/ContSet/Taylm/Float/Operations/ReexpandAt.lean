module

public import CORALean.ContSet.Taylm.Float.Operations.ReexpCoef
public import CORALean.Global.Float.ListSum

@[expose] public section

/-!
# `Taylm.reexpandAt`

One variable of the re-expansion: `sₖ` replaced by `m + r · sₖ`, every term binomially expanded in
the exponent of that variable, `(m + r sₖ)ᵉ = Σⱼ C(e, j) mᵉ⁻ʲ rʲ sₖʲ`. Each coefficient is the
term's times the bracketed binomial one; the upper corner is stored and the width goes to the
error box, a monomial being at most one in magnitude on the box. The remainder is kept.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.reexpandAt (k : Fin n) (m r : 𝕋) (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  -- what storing the upper corners costs, summed over the new terms
  let err := listSumUp ((T.reexpPairs k).map fun p =>
    subUp (Taylm.reexpCoef k m r p).sup (Taylm.reexpCoef k m r p).inf)
  ⟨(T.reexpPairs k).map fun p => ((Taylm.reexpCoef k m r p).sup, Function.update p.1.2 k p.2),
    T.rem, ⟨subDown T.I_error.inf err, addUp T.I_error.sup err⟩, T.maxOrder⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
