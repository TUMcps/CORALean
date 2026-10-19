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
the box, and the box is not a row whose slack can grow. A strictly feasible point brings it back (a
Slater point). The candidate is `β₀ = M be`, for the candidate right inverse `M` of `Ae`; its
residual `r` on the stored equalities is removed by a step of at most `σ = γ maxᵢ rᵢ`
(`Zonotope.rightInvGain`), so an exact solution `β̂` lies within `1 - s` of the origin in every
coordinate, `s = 1 - (maxⱼ |β₀ⱼ| + σ)` rounded down, and the check is `s > 0`.

A coefficient vector `β` in the box that satisfies the stored inequalities up to their slack and
reads within `εᵢ` of `beᵢ` is then moved onto the hyperplanes, `β' = β + δ` with `|δⱼ| ≤ ρ = γ maxᵢ
εᵢ`, and pulled back into the box along the segment to `β̂`: `β'' = (1 - λ) β' + λ β̂` with `λ = ρ /
(ρ + s)` keeps every equality and every `|β''ⱼ| ≤ 1`. In total `β` moves by at most `τ = ρ + (ρ / s)
(2 + ρ)`, rounded up. The result is `P` with every inequality's slack grown by what it reads on such
a move (`∑ⱼ |Aᵢⱼ| τ`), its `b` kept (#218), the equalities without slack, and `τ`, which the caller
pays into the point's error box. `none`, when the certificate or the slack fails, leaves the
fallback to the caller (`anchorEqsInBox_sound`).
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
