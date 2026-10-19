module

public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExpMulti
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsSubMonomialLeSum
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient

@[expose] public section

/-!
# `relaxExpMulti` over-approximates, merging any two generators

The exact layer's argument at this layer's stored columns, with the same two
roundings charged as in `relaxExp_outer`. `abs_sub_monomial_le_sum` is the exact
layer's and is what bounds the drift between the two monomials, asking nothing
of the exponent columns; the width bounding it is a natural number both layers
read off the same exponent matrix, however many factors it sums over.

Each stored column is a sum rounded down, so each is off by at most its gap to
the upward rounding, and the coefficient reading it — a monomial for the merged
dependent column, `Zonotope.coefficient` for the new independent one — is in
`[-1,1]`. That is one `generatorError` with two columns, exactly as at one index.

The independent coefficient is one scalar for the whole column, so the column
has to be stored collinear with the generator it relaxes: rounding each
coordinate outward on its own would not be reachable by any single coefficient.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n d : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `relaxExpMulti`'s dependent count, stated through the
projection because that is the form the goal has. -/
theorem PolyZonotope.aux_sum_univ_relaxExpMulti_h {pZ : PolyZonotope (Vec 𝕋 n)}
    {part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)} (f : Fin (d + 1) → ℝ) :
    ∑ l : Fin (pZ.relaxExpMulti part).h, f l
      = ∑ l, f (Fin.castAdd 1 l) + ∑ l : Fin 1, f (Fin.natAdd d l) :=
  Fin.sum_univ_add f

omit [SoundFloatArithmetic 𝕋] in
/-- The same at the independent count. -/
theorem PolyZonotope.aux_sum_univ_relaxExpMulti_q {pZ : PolyZonotope (Vec 𝕋 n)}
    {part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)} (f : Fin (pZ.q + 1) → ℝ) :
    ∑ j : Fin (pZ.relaxExpMulti part).q, f j
      = ∑ j, f (Fin.castAdd 1 j) + ∑ j : Fin 1, f (Fin.natAdd pZ.q j) :=
  Fin.sum_univ_add f

/-- The merged column is stored downward, so it is off by at most its gap to the
upward rounding. -/
theorem PolyZonotope.aux_mergedGenMulti_gap (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (i : Fin n) : -- --- CONCL ---
    |toReal (pZ.G (part.right 1) i) + toReal (pZ.G (part.right 0) i)
      - toReal (pZ.mergedGen part i)|
      ≤ toReal (pZ.aux_relaxGapMulti part i 0) := by -- --- PROOF ---
  have hlo : toReal (pZ.mergedGen part i)
      ≤ toReal (pZ.G (part.right 1) i) + toReal (pZ.G (part.right 0) i) := addDown_le_add _ _
  have hhi : toReal (pZ.G (part.right 1) i) + toReal (pZ.G (part.right 0) i)
      ≤ toReal (addUp (pZ.G (part.right 1) i) (pZ.G (part.right 0) i)) := add_le_addUp _ _
  have hgap : toReal (addUp (pZ.G (part.right 1) i) (pZ.G (part.right 0) i))
      - toReal (pZ.mergedGen part i) ≤ toReal (pZ.aux_relaxGapMulti part i 0) := sub_le_subUp _ _
  rw [abs_le]
  constructor <;> linarith

/-- The new independent column is the summed `ξ_E` copies added downward, so it
too is off by at most its gap to the upward fold. -/
theorem PolyZonotope.aux_relaxGenMulti_gap (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (i : Fin n) : -- --- CONCL ---
    |(pZ.relaxWidthMulti part : ℝ) * toReal (pZ.G (part.right 0) i)
      - toReal (pZ.aux_relaxGenMulti part i)|
        ≤ toReal (pZ.aux_relaxGapMulti part i 1) := by -- --- PROOF ---
  have hlo : toReal (pZ.aux_relaxGenMulti part i)
      ≤ (pZ.relaxWidthMulti part : ℝ) * toReal (pZ.G (part.right 0) i) := nsmulDown_le _ _
  have hhi : (pZ.relaxWidthMulti part : ℝ) * toReal (pZ.G (part.right 0) i)
      ≤ toReal (nsmulUp (pZ.relaxWidthMulti part) (pZ.G (part.right 0) i)) := le_nsmulUp _ _
  have hgap : toReal (nsmulUp (pZ.relaxWidthMulti part) (pZ.G (part.right 0) i))
      - toReal (pZ.aux_relaxGenMulti part i) ≤ toReal (pZ.aux_relaxGapMulti part i 1) :=
        sub_le_subUp _ _
  rw [abs_le]
  constructor <;> linarith

-- the two stored columns and their two gaps, the drift carried by the second
theorem PolyZonotope.aux_relaxExpMulti_nominal (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) :
    nominalSet pZ ⊆ nominalSet (pZ.relaxExpMulti part)
      + (PolyZonotope.generatorError (pZ.aux_relaxGapMulti part)).construct := by -- --- PROOF ---
  intro x hx
  obtain ⟨a, β, ha, hβ, hxi⟩ := PolyZonotope.mem_nominalSet_iff.mp hx
  -- the width is a sum of naturals, and the drift bound is stated over its casts
  have hcast : (pZ.relaxWidthMulti part : ℝ)
      = ∑ k, (Real.PolyZonotope.eDiff (pZ.E k (part.right 0)) (pZ.E k (part.right 1)) : ℝ) := by
    rw [PolyZonotope.relaxWidthMulti, Nat.cast_sum]
  have habs : |Real.PolyZonotope.monomial pZ.E a (part.right 0)
      - Real.PolyZonotope.monomial pZ.E a (part.right 1)|
        ≤ (pZ.relaxWidthMulti part : ℝ) := by
    rw [hcast]
    exact Real.PolyZonotope.abs_sub_monomial_le_sum pZ.E ha _ _
  have hnn : (0:ℝ) ≤ (pZ.relaxWidthMulti part : ℝ) := Nat.cast_nonneg _
  set t := Real.Zonotope.coefficient (pZ.relaxWidthMulti part : ℝ)
    (Real.PolyZonotope.monomial pZ.E a (part.right 0)
      - Real.PolyZonotope.monomial pZ.E a (part.right 1)) with ht
  have hcoef : (pZ.relaxWidthMulti part : ℝ) * t
      = Real.PolyZonotope.monomial pZ.E a (part.right 0)
        - Real.PolyZonotope.monomial pZ.E a (part.right 1) := by
    rw [ht]
    exact Real.Zonotope.mul_coefficient habs
  -- the kept columns keep their monomials, and the merged one takes the second's
  have hmono : ∀ l : Fin d,
      Real.PolyZonotope.monomial (pZ.relaxExpMulti part).E a (Fin.castAdd 1 l)
        = Real.PolyZonotope.monomial pZ.E a (part.left l) := fun l => by
    simp only [Real.PolyZonotope.monomial, PolyZonotope.relaxExpMulti, Fin.append_left]
    rfl
  have hlast : Real.PolyZonotope.monomial (pZ.relaxExpMulti part).E a (Fin.natAdd d 0)
      = Real.PolyZonotope.monomial pZ.E a (part.right 1) := by
    simp only [Real.PolyZonotope.monomial, PolyZonotope.relaxExpMulti, Fin.append_right]
    rfl
  -- the point at the stored columns, and what the two gaps still owe it
  refine ⟨fun i => toReal (pZ.c i)
      + (∑ l : Fin d, toReal (pZ.G (part.left l) i)
            * Real.PolyZonotope.monomial pZ.E a (part.left l)
          + toReal (pZ.mergedGen part i) * Real.PolyZonotope.monomial pZ.E a (part.right 1))
      + (∑ j, toReal (pZ.GI j i) * β j + toReal (pZ.aux_relaxGenMulti part i) * t),
    PolyZonotope.mem_nominalSet_iff.mpr ⟨a, Fin.append β fun _ => t, ha, ?_, ?_⟩,
    _, PolyZonotope.mem_generatorError (G := pZ.aux_relaxGapMulti part)
      (Δ := fun i => ![toReal (pZ.G (part.right 1) i) + toReal (pZ.G (part.right 0) i)
          - toReal (pZ.mergedGen part i),
        (pZ.relaxWidthMulti part : ℝ) * toReal (pZ.G (part.right 0) i)
          - toReal (pZ.aux_relaxGenMulti part i)])
      (t := ![Real.PolyZonotope.monomial pZ.E a (part.right 1), t]) ?_ ?_, ?_⟩
  -- the fresh independent coefficient is what the drift asks of the new column
  · refine Fin.addCases (fun j => ?_) fun _ => ?_
    · rw [Fin.append_left]
      exact hβ j
    · rw [Fin.append_right, ht]
      exact Real.Zonotope.abs_coefficient_le_one hnn habs
  · intro i
    rw [PolyZonotope.aux_sum_univ_relaxExpMulti_h, PolyZonotope.aux_sum_univ_relaxExpMulti_q]
    simp only [Fin.sum_univ_one, hmono, hlast]
    simp only [PolyZonotope.relaxExpMulti, Fin.append_left, Fin.append_right]
  · refine fun i l => Fin.cases ?_ (fun l' => ?_) l
    · exact PolyZonotope.aux_mergedGenMulti_gap pZ part i
    · rw [Subsingleton.elim l' 0]
      exact PolyZonotope.aux_relaxGenMulti_gap pZ part i
  · refine Fin.cases ?_ (fun l' => ?_)
    · exact Real.PolyZonotope.abs_monomial_le_one pZ.E ha _
    · rw [Subsingleton.elim l' 0, ht]
      exact Real.Zonotope.abs_coefficient_le_one hnn habs
  -- the two stored columns, their gaps and the drift recombine into the exact sums
  · funext i
    show toReal (pZ.c i)
          + (∑ l : Fin d, toReal (pZ.G (part.left l) i)
              * Real.PolyZonotope.monomial pZ.E a (part.left l)
            + toReal (pZ.mergedGen part i) * Real.PolyZonotope.monomial pZ.E a (part.right 1))
          + (∑ j, toReal (pZ.GI j i) * β j + toReal (pZ.aux_relaxGenMulti part i) * t)
        + ∑ l, _ * _ = x i
    rw [hxi i, Fin.sum_univ_two,
      part.sum_split₂ fun l => toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l,
      Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination toReal (pZ.G (part.right 0) i) * hcoef


-- =======================================  MAIN THEOREM  ======================================= --

/-- Merging any two dependent generators over-approximates at the stored
columns, the summed width paying for every exponent that moves. -/
theorem PolyZonotope.relaxExpMulti_outer (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) :
    pZ.construct ⊆ (pZ.relaxExpMulti part).construct := by -- --- PROOF ---
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨z', hz', g, hg, hsum⟩ := PolyZonotope.aux_relaxExpMulti_nominal pZ part hz
  refine ⟨z', hz', e + g, Interval.plus_outer _ _ ⟨e, he, g, hg, rfl⟩, ?_⟩
  -- `Set.image2` leaves the sum a beta-redex, which `rw` will not match
  have hsum' : z' + g = z := hsum
  show z' + (e + g) = z + e
  rw [← hsum', add_comm e g, ← add_assoc]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
