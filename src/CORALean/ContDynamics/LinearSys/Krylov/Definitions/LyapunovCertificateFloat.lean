module

public import CORALean.Global.Float.Interfaces
public import CORALean.Global.Tensor

@[expose] public section

/-!
# A checked Lyapunov weight of a matrix, as the float check returns it

Whether a symmetric weight `P` passed the check, and what it certifies: a lower bound `a` and an
upper bound `b` of its quadratic form, `a x*x ≤ x*Px ≤ b x*x`, and a growth rate `μ` with
`x*PAx ≤ μ x*Px`, so that `‖e^{tA}‖₂ ≤ √(b/a) e^{μt}` ([1, Eq. 3.4] with a weight). A weight that
did not pass certifies nothing.

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- A Lyapunov weight with its bounds `a`, `b` and rate `μ`, and whether the check accepted it. -/
structure Krylov.LyapunovCertificateFloat (𝕋 : Type) where
  ok : Bool
  lower : 𝕋
  upper : 𝕋
  rate : 𝕋

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
