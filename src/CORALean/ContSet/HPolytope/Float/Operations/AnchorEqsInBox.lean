module

public import CORALean.ContSet.HPolytope.Float.HPolytope
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.RightInvCandidate
public import CORALean.ContSet.Zonotope.Float.Operations.RightInvGain

@[expose] public section

/-!
# `HPolytope.anchorEqsInBox`: rounded equalities kept, on coefficients in the unit box

The coefficient polytope of a constrained zonotope lives in the unit box `[-1, 1]ʰ`. Moving a point
onto the stored hyperplanes by a certified right inverse of `Ae` (`Zonotope.rightInvGain`) may leave
the box, whose rows have no slack to grow. A strictly feasible point `β̂` (a Slater point, from a
candidate right inverse `M` of `Ae`) brings it back; the check is `s > 0`. A `β` in the box meeting
the stored inequalities up to slack is moved onto the hyperplanes and pulled back along the segment
to `β̂`, by at most `τ`. The result is `P` with each slack grown by what it reads on such a move,
`b` kept (#218), and `τ`, paid into the point's error box. `none` leaves the fallback to the caller
(`anchorEqsInBox_sound`).

## Inputs
* `P` – H-polytope
* `ε` – vector of length `P.me`

## Output
* `P` with equalities kept and the residuals `ε` paid in, and the coefficient move, or `none`
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `P` with its equalities kept and their residual bounds `ε` paid into the inequalities, and the
largest coefficient move this costs, or `none` without a certificate or a strictly feasible
point. -/
def HPolytope.anchorEqsInBox (P : HPolytope 𝕋 (Vec 𝕋 n)) (ε : Vec 𝕋 P.me) :
    Option (HPolytope 𝕋 (Vec 𝕋 n) × 𝕋) :=
  let M := Zonotope.rightInvCandidate P.Ae
  match Zonotope.rightInvGain P.Ae M with
  | none => none
  | some γ =>
    -- the interior candidate `M be` and its residual on the stored equalities
    let β₀ : Vec 𝕋 n := fun j => dotUp (M j) P.be
    let r : Vec 𝕋 P.me := fun i =>
      maximum (subUp (dotUp (P.Ae i) β₀) (P.be i)) (subUp (P.be i) (dotDown (P.Ae i) β₀))
    -- how far inside the unit box its exact correction stays
    let s := subDown one (addUp (maximumOver fun j => absolute (β₀ j)) (mulUp γ (maximumOver r)))
    -- the step onto the hyperplanes, then the pull back into the box
    let ρ := mulUp γ (maximumOver ε)
    let τ := addUp ρ (mulUp (divUp ρ s) (addUp (addUp one one) ρ))
    if ltStrict zero s then
      some ({ P with b_error := fun k => addUp (absolute (P.b_error k)) (mulUp (radius P.A k) τ),
                     be_error := fun _ => zero }, τ)
    else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
