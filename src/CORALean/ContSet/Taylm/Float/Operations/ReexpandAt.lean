module

public import CORALean.ContSet.Taylm.Float.Operations.BinomCoef
public import CORALean.ContSet.Taylm.Float.Taylm
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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

def Taylm.aux_reexpCoef (k : Fin n) (m r : 𝕋) (p : (𝕋 × (Fin n → ℕ)) × ℕ) : Interval 𝕋 :=
  let B := Taylm.binomCoef (p.1.2 k) p.2 m r
  ⟨Interval.mulLo p.1.1 p.1.1 B.inf B.sup, Interval.mulHi p.1.1 p.1.1 B.inf B.sup⟩

def Taylm.aux_reexpPairs (k : Fin n) (T : Taylm 𝕋 n) : List ((𝕋 × (Fin n → ℕ)) × ℕ) :=
  T.terms.flatMap fun a => (List.range (a.2 k + 1)).map fun j => (a, j)


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.reexpandAt (k : Fin n) (m r : 𝕋) (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  -- what storing the upper corners costs, summed over the new terms
  let err := listSumUp ((T.aux_reexpPairs k).map fun p =>
    subUp (Taylm.aux_reexpCoef k m r p).sup (Taylm.aux_reexpCoef k m r p).inf)
  ⟨(T.aux_reexpPairs k).map fun p =>
      ((Taylm.aux_reexpCoef k m r p).sup, Function.update p.1.2 k p.2),
    T.rem, ⟨subDown T.I_error.inf err, addUp T.I_error.sup err⟩, T.maxOrder⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
