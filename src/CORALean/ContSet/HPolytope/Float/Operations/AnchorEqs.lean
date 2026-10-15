module

public import CORALean.ContSet.HPolytope.Float.HPolytope
public import CORALean.ContSet.Zonotope.Float.Operations.RightInvCandidate
public import CORALean.ContSet.Zonotope.Float.Operations.RightInvGain

@[expose] public section

/-!
# `HPolytope.anchorEqs`: rounded equalities kept as equalities

An operation that has rounded an equality knows its points only up to a residual: each one
satisfies the stored inequalities and reads within `εᵢ` of the stored `beᵢ` on equality row `i`.
Such a point is moved onto the stored hyperplanes by a step `δ` with `Ae δ = be - Ae y`, and a
certified right inverse of `Ae` (`Zonotope.rightInvGain` at the candidate
`Zonotope.rightInvCandidate`) bounds that step by `ρ = γ maxᵢ εᵢ` in every coordinate. So the
equalities stay `(Ae, be)` as stored, every inequality is raised by what it reads on a step of
that size (`∑ⱼ |Aᵢⱼ| ρ`), and the error box grows by `[-ρ, ρ]` in every coordinate, the step
taken back.

When the certificate fails (a rank-deficient or ill-conditioned `Ae`), each equality is written
instead as the two inequalities `Aeᵢ x ≤ beᵢ + εᵢ` and `-Aeᵢ x ≤ -beᵢ + εᵢ`, rounded up, and the
box is kept. The choice is made at run time; `HPolytope.anchorEqs_outer` covers both.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `P` with its equalities kept and their residual bounds `ε` paid into the inequalities and the
error box, or, without a certificate, with each equality widened into two inequalities. -/
def HPolytope.anchorEqs (P : HPolytope 𝕋 (Vec 𝕋 n)) (ε : Vec 𝕋 P.me) : HPolytope 𝕋 (Vec 𝕋 n) :=
  match Zonotope.rightInvGain P.Ae (Zonotope.rightInvCandidate P.Ae) with
  | some γ =>
    -- the largest step onto the hyperplanes, in any coordinate
    let ρ := mulUp γ (maximumOver ε)
    { P with
      b := fun i => addUp (P.b i) (mulUp (radius P.A i) ρ)
      I_error := ⟨fun j => addDown (P.I_error.inf j) (neg ρ), fun j => addUp (P.I_error.sup j) ρ⟩ }
  | none =>
    -- each equality as its two inequalities, widened by its residual
    { m := P.m + (P.me + P.me)
      A := Fin.append P.A (Fin.append P.Ae (-P.Ae))
      b := Fin.append P.b
        (Fin.append (fun i => addUp (P.be i) (ε i)) fun i => addUp (neg (P.be i)) (ε i))
      me := 0
      Ae := fun i => i.elim0
      be := fun i => i.elim0
      I_error := P.I_error }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
