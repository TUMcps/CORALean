import CORALean.ContSet.ConZonotope.Float.Operations.SeparatesAlong

/-!
# `ConZonotope.isDisjointLP`: disjointness by a separating direction

CORA's `'exact'` `isIntersecting_` decides by a linear program whether the
intersection is empty. Here that program is solved at ℚ for a *witness* only:
the stacked coefficients `(β₁, β₂, s)` under both operands' boxes and constraints,
`max -s` over `|(c₁ + G₁β₁) - (c₂ + G₂β₂)|ᵢ ≤ s`, whose dual weights on the `2n`
gap rows combine into a direction `a` along which the nominal sets lie apart
when the optimum is `s > 0`.

The verdict is `separatesAlong`'s, at `a` and at `-a` (so the sign need not be
right), with the error boxes paid by `boundDot`. One-sided: `true` proves the
sets disjoint whatever direction the simplex returned; `false` says nothing.

A NaN among the stored data reads through `ToRat` as `1.5 · 2 ^ 1024`, so the program solved
is another one. That costs tightness only: the checker sees the NaN in rounded arithmetic.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A vector over `Fin h`, placed at offset `off` of an index read as `ℕ`, zero
elsewhere. -/
def ConZonotope.aux_place {h : ℕ} (f : Fin h → ℚ) (off v : ℕ) : ℚ :=
  if hv : off ≤ v ∧ v - off < h then f ⟨v - off, hv.2⟩ else 0

/-- A constraint polytope's rows on the coefficients at offset `off`: `A ≤ b`,
`Ae ≤ be.sup`, `-Ae ≤ -be.inf`, and the unit box both ways. -/
def ConZonotope.aux_coeffRows (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (off : ℕ) : List ((ℕ → ℚ) × ℚ) :=
  let A := fun k j => ToRat.toRat (cZ.P.A k j)
  let Ae := fun k j => ToRat.toRat (cZ.P.Ae k j)
  (List.finRange cZ.P.m).map (fun k => (ConZonotope.aux_place (A k) off, ToRat.toRat (cZ.P.b k)))
    ++ (List.finRange cZ.P.me).map (fun k =>
      (ConZonotope.aux_place (Ae k) off, ToRat.toRat (cZ.P.be.sup k)))
    ++ (List.finRange cZ.P.me).map (fun k =>
      (fun v => -ConZonotope.aux_place (Ae k) off v, -ToRat.toRat (cZ.P.be.inf k)))
    ++ (List.finRange cZ.h).map (fun j =>
      (ConZonotope.aux_place (fun l => if l = j then 1 else 0) off, 1))
    ++ (List.finRange cZ.h).map (fun j =>
      (ConZonotope.aux_place (fun l => if l = j then -1 else 0) off, 1))

/-- The gap rows, `±((G₁β₁ - G₂β₂)ᵢ) - s ≤ ±(c₂ - c₁)ᵢ`, the `+` block first. -/
def ConZonotope.aux_gapRows (cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n)) : List ((ℕ → ℚ) × ℚ) :=
  let s := cZ₁.h + cZ₂.h
  let gap (i : Fin n) : ℕ → ℚ := fun v =>
    ConZonotope.aux_place (fun j => ToRat.toRat (cZ₁.G j i)) 0 v
      - ConZonotope.aux_place (fun j => ToRat.toRat (cZ₂.G j i)) cZ₁.h v
  let dc (i : Fin n) : ℚ := ToRat.toRat (cZ₂.c i) - ToRat.toRat (cZ₁.c i)
  (List.finRange n).map (fun i => (fun v => gap i v - if v = s then 1 else 0, dc i))
    ++ (List.finRange n).map (fun i => (fun v => -gap i v - if v = s then 1 else 0, -dc i))

/-- A rational, rounded to the scalar with its sign kept; any value would do. -/
def ConZonotope.aux_ratSigned (q : ℚ) : 𝕋 := if 0 ≤ q then ratUp q else neg (ratUp (-q))

/-- The direction the program's dual proposes: the `-` block's weight minus the
`+` block's, coordinate by coordinate. All zero when the simplex returns
nothing, which then fails the check below. -/
def ConZonotope.aux_separator (cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n)) : Vec 𝕋 n :=
  let rows := ConZonotope.aux_coeffRows cZ₁ 0 ++ ConZonotope.aux_coeffRows cZ₂ cZ₁.h
    ++ ConZonotope.aux_gapRows cZ₁ cZ₂
  let N := cZ₁.h + cZ₂.h + 1
  let base := rows.length - (n + n)
  let A : Fin rows.length → Fin N → ℚ := fun r v => (rows.get r).1 v
  let b : Fin rows.length → ℚ := fun r => (rows.get r).2
  -- maximise `-s`, the coefficients free of cost
  let obj : Fin N → ℚ := fun v => if (v : ℕ) = cZ₁.h + cZ₂.h then -1 else 0
  match dualCandidate (64 * (rows.length + N + 1)) A b obj with
  | none => fun _ => zero
  | some w =>
    let wN : ℕ → ℚ := fun k => if hk : k < rows.length then w ⟨k, hk⟩ else 0
    fun i => ConZonotope.aux_ratSigned (wN (base + n + i) - wN (base + i))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Disjoint if the proposed direction, or its negation, separates the two
bounds. Sound when `true`; `false` decides nothing. -/
def ConZonotope.isDisjointLP (cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n)) : Bool :=
  let a := ConZonotope.aux_separator cZ₁ cZ₂
  ConZonotope.separatesAlong cZ₁ cZ₂ a || ConZonotope.separatesAlong cZ₁ cZ₂ fun i => neg (a i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
