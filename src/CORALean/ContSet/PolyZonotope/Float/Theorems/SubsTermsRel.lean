module

public import CORALean.ContSet.PolyZonotope.Float.Operations.SubsPow
public import CORALean.ContSet.PolyZonotope.Real.Operations.SubsPow
public import CORALean.ContSet.PolyZonotope.Float.Definitions.SubsRel
public import CORALean.ContSet.PolyZonotope.Float.Operations.SubsPoly
public import CORALean.ContSet.PolyZonotope.Real.Operations.SubsPoly
public import CORALean.ContSet.PolyZonotope.Float.Operations.SubsXprod
public import CORALean.ContSet.PolyZonotope.Real.Operations.SubsXprod
public import CORALean.ContSet.PolyZonotope.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.SubsTerms

@[expose] public section

/-!
# `subsTerms` keeps the bracket

The generators are the `Xprod`s of the original generators in turn, each term tagged with its
generator.

## Inputs
* `pZ` – polynomial zonotope
* `nu` – number of substituted factors
* `pZin` – polynomial zonotope substituted in
* `idu` – indices of the substituted factors

## Hypotheses
* none

## Conclusion
* the float terms bracket the exact terms
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {p : ℕ}

/-- If the float term lists `A`, `B` enclose the real lists `A'`, `B'` term by term (`subsRel`),
then the float product `subsMul A B` encloses the real product `subsMul A' B'` term by term. -/
private theorem PolyZonotope.aux_subsMul_rel {A B : List ((Interval 𝕋) × (Fin p → ℕ))}
    {A' B' : List (ℝ × (Fin p → ℕ))} (hA : PolyZonotope.subsRel A A')
    (hB : PolyZonotope.subsRel B B') : -- --- CONCL ---
    PolyZonotope.subsRel (PolyZonotope.subsMul A B)
      (Real.PolyZonotope.subsMul A' B') := by -- --- PROOF ---
  unfold PolyZonotope.subsRel at *
  induction hA with
  | nil => exact List.Forall₂.nil
  | cons hst _ ih =>
    rename_i s t _ _
    refine List.rel_append ?_ ih
    -- the row of one term of `A` against all of `B`
    clear ih
    induction hB with
    | nil => exact List.Forall₂.nil
    | cons hst' _ ih' =>
      refine List.Forall₂.cons ⟨?_, ?_⟩ ih'
      · simp only [hst.1, hst'.1]
      · have hb := Real.Interval.mul_between_corners hst.2.1 hst.2.2 hst'.2.1 hst'.2.2
        exact ⟨le_trans (Interval.mulLo_le _ _ _ _) hb.1, le_trans hb.2 (Interval.le_mulHi _ _ _ _)⟩

end


section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {p : ℕ}

/-- `subsPow` keeps the bracket. -/
private theorem PolyZonotope.aux_subsPow_rel {A : List ((Interval 𝕋) × (Fin p → ℕ))}
    {A' : List (ℝ × (Fin p → ℕ))} (hA : PolyZonotope.subsRel A A') (d : ℕ) :
    PolyZonotope.subsRel (PolyZonotope.subsPow A d) (Real.PolyZonotope.subsPow A' d) := by
  induction d with
  | zero =>
    exact List.Forall₂.cons ⟨rfl, by simp [toReal_one]⟩ List.Forall₂.nil
  | succ d ih => exact PolyZonotope.aux_subsMul_rel hA ih

end


section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- `subsPoly` is the stored polynomial of an output. -/
private theorem PolyZonotope.aux_subsPoly_rel {nu : ℕ} (pZin : PolyZonotope (Vec 𝕋 nu))
    (ii : Fin nu) : -- --- CONCL ---
    PolyZonotope.subsRel (pZin.subsPoly ii)
      (Real.PolyZonotope.subsPoly (InflatedContSet.nominal pZin) ii) := by -- --- PROOF ---
  refine List.Forall₂.cons ⟨rfl, le_refl _, le_refl _⟩ ?_
  generalize List.finRange pZin.h = L
  induction L with
  | nil => exact List.Forall₂.nil
  | cons j L ih => exact List.Forall₂.cons ⟨rfl, le_refl _, le_refl _⟩ ih

end


/-- `subsXprod` keeps the bracket. -/
private theorem PolyZonotope.aux_subsXprod_rel (pZ : PolyZonotope (Vec 𝕋 n)) {nu : ℕ}
    (pZin : PolyZonotope (Vec 𝕋 nu))
    (idu : Fin nu → Fin pZ.p) (i : Fin pZ.h) : -- --- CONCL ---
    PolyZonotope.subsRel (pZ.subsXprod pZin idu i)
      (Real.PolyZonotope.subsXprod (InflatedContSet.nominal pZ)
        (InflatedContSet.nominal pZin) idu i) := by -- --- PROOF ---
  unfold PolyZonotope.subsXprod Real.PolyZonotope.subsXprod
  generalize List.finRange nu = L
  have h1 : PolyZonotope.subsRel ([(⟨one, one⟩, 0)] : List ((Interval 𝕋) × (Fin pZin.p → ℕ)))
      [(1, 0)] := List.Forall₂.cons ⟨rfl, by simp [toReal_one]⟩ List.Forall₂.nil
  generalize ([(⟨one, one⟩, 0)] : List ((Interval 𝕋) × (Fin pZin.p → ℕ))) = acc at h1 ⊢
  generalize ([(1, 0)] : List (ℝ × (Fin pZin.p → ℕ))) = acc' at h1 ⊢
  induction L generalizing acc acc' with
  | nil => exact h1
  | cons ii L ih =>
    exact ih _ _ (PolyZonotope.aux_subsMul_rel h1
      (PolyZonotope.aux_subsPow_rel (PolyZonotope.aux_subsPoly_rel pZin ii) _))


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.subsTerms_rel (pZ : PolyZonotope (Vec 𝕋 n)) {nu : ℕ}
    (pZin : PolyZonotope (Vec 𝕋 nu))
    (idu : Fin nu → Fin pZ.p) : -- --- CONCL ---
    List.Forall₂ (fun s t => s.1 = t.1 ∧ s.2.2 = t.2.2 ∧ toReal s.2.1.inf ≤ t.2.1 ∧
        t.2.1 ≤ toReal s.2.1.sup)
      (pZ.subsTerms pZin idu)
      (Real.PolyZonotope.subsTerms (InflatedContSet.nominal pZ)
        (InflatedContSet.nominal pZin) idu) := by -- --- PROOF ---
  unfold PolyZonotope.subsTerms Real.PolyZonotope.subsTerms
  generalize List.finRange pZ.h = L
  induction L with
  | nil => exact List.Forall₂.nil
  | cons i L ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    refine List.rel_append ?_ ih
    have hx := PolyZonotope.aux_subsXprod_rel pZ pZin idu i
    unfold PolyZonotope.subsRel at hx
    generalize pZ.subsXprod pZin idu i = X at hx
    generalize Real.PolyZonotope.subsXprod (InflatedContSet.nominal pZ)
      (InflatedContSet.nominal pZin) idu i = X' at hx
    induction hx with
    | nil => exact List.Forall₂.nil
    | cons h _ ih' => exact List.Forall₂.cons ⟨rfl, h⟩ ih'

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
