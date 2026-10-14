module

public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Float.Operations.RightInvQ
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `ZonoBundle.parallelotope`, over a floating-point scalar

`Λ box(·)` of the exact layer [1, Eq. 2], where the box `B` is to hold `Λ⁻¹ x`. A float layer
has no exact `Λ⁻¹`: `H` is any candidate, `B` a box around `H x`, and the point is
`x = Λ (H x) + (1 - Λ H) x`. The first term is `Λ * zonotope(B)`; the second is at most
`q m` in every coordinate, `q` the row-sum bound `Zonotope.rightInvQ Λ H` of `1 - Λ H` and `m` a
bound on `|x|`, and is paid into the error box. Nothing is assumed of `H`: a poor one costs
precision alone.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Λ * zonotope(B)`, widened by `q m` for the residual `(1 - Λ H) x` of a candidate `H`. -/
def ZonoBundle.parallelotope (Λ H : Mat 𝕋 n n) (B : Interval (Vec 𝕋 n)) (m : 𝕋) :
    Zonotope (Vec 𝕋 n) :=
  let Z := Zonotope.mtimes Λ B.zonotope                         -- Λ * zonotope(B)
  let e := mulUp (Zonotope.rightInvQ Λ H) m                     -- reach of (1 - Λ H) x
  { h := Z.h
    c := Z.c
    G := Z.G
    I_error := Z.I_error.plus ⟨fun _ => neg e, fun _ => e⟩ }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
