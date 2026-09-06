import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExpMulti
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorError
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsSubMonomialLeSum
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient

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

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n d : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `relaxExpMulti`'s dependent count, stated through the
projection because that is the form the goal has. -/
theorem PolyZonotope.aux_sum_univ_relaxExpMulti_h {PZ : PolyZonotope 𝕋 n}
    {part : Split (Fin PZ.h) into (Fin d) and (Fin 2)} (f : Fin (d + 1) → ℝ) :
    ∑ l : Fin (PZ.relaxExpMulti part).h, f l
      = ∑ l, f (Fin.castAdd 1 l) + ∑ l : Fin 1, f (Fin.natAdd d l) :=
  Fin.sum_univ_add f

omit [SoundFloatArithmetic 𝕋] in
/-- The same at the independent count. -/
theorem PolyZonotope.aux_sum_univ_relaxExpMulti_q {PZ : PolyZonotope 𝕋 n}
    {part : Split (Fin PZ.h) into (Fin d) and (Fin 2)} (f : Fin (PZ.q + 1) → ℝ) :
    ∑ j : Fin (PZ.relaxExpMulti part).q, f j
      = ∑ j, f (Fin.castAdd 1 j) + ∑ j : Fin 1, f (Fin.natAdd PZ.q j) :=
  Fin.sum_univ_add f

/-- The merged column is stored downward, so it is off by at most its gap to the
upward rounding. -/
theorem PolyZonotope.aux_mergedGenMulti_gap (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (i : Fin n) :
    |toReal (PZ.G i (part.right 1)) + toReal (PZ.G i (part.right 0))
      - toReal (PZ.mergedGen part i)| ≤ toReal (PZ.relaxGapMulti part i 0) := by
  have hlo : toReal (PZ.mergedGen part i)
      ≤ toReal (PZ.G i (part.right 1)) + toReal (PZ.G i (part.right 0)) := addDown_le_add _ _
  have hhi : toReal (PZ.G i (part.right 1)) + toReal (PZ.G i (part.right 0))
      ≤ toReal (addUp (PZ.G i (part.right 1)) (PZ.G i (part.right 0))) := add_le_addUp _ _
  have hgap : toReal (addUp (PZ.G i (part.right 1)) (PZ.G i (part.right 0)))
      - toReal (PZ.mergedGen part i) ≤ toReal (PZ.relaxGapMulti part i 0) := sub_le_subUp _ _
  rw [abs_le]
  constructor <;> linarith

/-- The new independent column is the summed `ξ_E` copies added downward, so it
too is off by at most its gap to the upward fold. -/
theorem PolyZonotope.aux_relaxGenMulti_gap (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (i : Fin n) :
    |(PZ.relaxWidthMulti part : ℝ) * toReal (PZ.G i (part.right 0))
      - toReal (PZ.relaxGenMulti part i)| ≤ toReal (PZ.relaxGapMulti part i 1) := by
  have hlo : toReal (PZ.relaxGenMulti part i)
      ≤ (PZ.relaxWidthMulti part : ℝ) * toReal (PZ.G i (part.right 0)) := nsmulDown_le _ _
  have hhi : (PZ.relaxWidthMulti part : ℝ) * toReal (PZ.G i (part.right 0))
      ≤ toReal (nsmulUp (PZ.relaxWidthMulti part) (PZ.G i (part.right 0))) := le_nsmulUp _ _
  have hgap : toReal (nsmulUp (PZ.relaxWidthMulti part) (PZ.G i (part.right 0)))
      - toReal (PZ.relaxGenMulti part i) ≤ toReal (PZ.relaxGapMulti part i 1) := sub_le_subUp _ _
  rw [abs_le]
  constructor <;> linarith

-- the two stored columns and their two gaps, the drift carried by the second
theorem PolyZonotope.aux_relaxExpMulti_nominal (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) :
    nominalSet PZ ⊆ nominalSet (PZ.relaxExpMulti part)
      + (PolyZonotope.generatorError (PZ.relaxGapMulti part)).construct := by
  intro x hx
  obtain ⟨a, β, ha, hβ, hxi⟩ := PolyZonotope.mem_nominalSet_iff.mp hx
  -- the width is a sum of naturals, and the drift bound is stated over its casts
  have hcast : (PZ.relaxWidthMulti part : ℝ)
      = ∑ k, (Real.PolyZonotope.eDiff (PZ.E k (part.right 0)) (PZ.E k (part.right 1)) : ℝ) := by
    rw [PolyZonotope.relaxWidthMulti, Nat.cast_sum]
  have habs : |Real.PolyZonotope.monomial PZ.E a (part.right 0)
      - Real.PolyZonotope.monomial PZ.E a (part.right 1)|
        ≤ (PZ.relaxWidthMulti part : ℝ) := by
    rw [hcast]
    exact Real.PolyZonotope.abs_sub_monomial_le_sum PZ.E ha _ _
  have hnn : (0:ℝ) ≤ (PZ.relaxWidthMulti part : ℝ) := Nat.cast_nonneg _
  set t := Real.Zonotope.coefficient (PZ.relaxWidthMulti part : ℝ)
    (Real.PolyZonotope.monomial PZ.E a (part.right 0)
      - Real.PolyZonotope.monomial PZ.E a (part.right 1)) with ht
  have hcoef : (PZ.relaxWidthMulti part : ℝ) * t
      = Real.PolyZonotope.monomial PZ.E a (part.right 0)
        - Real.PolyZonotope.monomial PZ.E a (part.right 1) := by
    rw [ht]
    exact Real.Zonotope.mul_coefficient habs
  -- the kept columns keep their monomials, and the merged one takes the second's
  have hmono : ∀ l : Fin d,
      Real.PolyZonotope.monomial (PZ.relaxExpMulti part).E a (Fin.castAdd 1 l)
        = Real.PolyZonotope.monomial PZ.E a (part.left l) := fun l => by
    simp only [Real.PolyZonotope.monomial, PolyZonotope.relaxExpMulti, Fin.append_left]
    rfl
  have hlast : Real.PolyZonotope.monomial (PZ.relaxExpMulti part).E a (Fin.natAdd d 0)
      = Real.PolyZonotope.monomial PZ.E a (part.right 1) := by
    simp only [Real.PolyZonotope.monomial, PolyZonotope.relaxExpMulti, Fin.append_right]
    rfl
  -- the point at the stored columns, and what the two gaps still owe it
  refine ⟨fun i => toReal (PZ.c i)
      + (∑ l : Fin d, toReal (PZ.G i (part.left l))
            * Real.PolyZonotope.monomial PZ.E a (part.left l)
          + toReal (PZ.mergedGen part i) * Real.PolyZonotope.monomial PZ.E a (part.right 1))
      + (∑ j, toReal (PZ.GI i j) * β j + toReal (PZ.relaxGenMulti part i) * t),
    PolyZonotope.mem_nominalSet_iff.mpr ⟨a, Fin.append β fun _ => t, ha, ?_, ?_⟩,
    _, PolyZonotope.mem_generatorError (G := PZ.relaxGapMulti part)
      (Δ := fun i => ![toReal (PZ.G i (part.right 1)) + toReal (PZ.G i (part.right 0))
          - toReal (PZ.mergedGen part i),
        (PZ.relaxWidthMulti part : ℝ) * toReal (PZ.G i (part.right 0))
          - toReal (PZ.relaxGenMulti part i)])
      (t := ![Real.PolyZonotope.monomial PZ.E a (part.right 1), t]) ?_ ?_, ?_⟩
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
    · exact PolyZonotope.aux_mergedGenMulti_gap PZ part i
    · rw [Subsingleton.elim l' 0]
      exact PolyZonotope.aux_relaxGenMulti_gap PZ part i
  · refine Fin.cases ?_ (fun l' => ?_)
    · exact Real.PolyZonotope.abs_monomial_le_one PZ.E ha _
    · rw [Subsingleton.elim l' 0, ht]
      exact Real.Zonotope.abs_coefficient_le_one hnn habs
  -- the two stored columns, their gaps and the drift recombine into the exact sums
  · funext i
    show toReal (PZ.c i)
          + (∑ l : Fin d, toReal (PZ.G i (part.left l))
              * Real.PolyZonotope.monomial PZ.E a (part.left l)
            + toReal (PZ.mergedGen part i) * Real.PolyZonotope.monomial PZ.E a (part.right 1))
          + (∑ j, toReal (PZ.GI i j) * β j + toReal (PZ.relaxGenMulti part i) * t)
        + ∑ l, _ * _ = x i
    rw [hxi i, Fin.sum_univ_two,
      part.sum_split₂ fun l => toReal (PZ.G i l) * Real.PolyZonotope.monomial PZ.E a l,
      Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination toReal (PZ.G i (part.right 0)) * hcoef


-- =======================================  MAIN THEOREM  ======================================= --

/-- Merging any two dependent generators over-approximates at the stored
columns, the summed width paying for every exponent that moves. -/
theorem PolyZonotope.relaxExpMulti_outer (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) :
    PZ.construct ⊆ (PZ.relaxExpMulti part).construct := by
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨z', hz', g, hg, hsum⟩ := PolyZonotope.aux_relaxExpMulti_nominal PZ part hz
  refine ⟨z', hz', e + g, Interval.plus_outer _ _ ⟨e, he, g, hg, rfl⟩, ?_⟩
  -- `Set.image2` leaves the sum a beta-redex, which `rw` will not match
  have hsum' : z' + g = z := hsum
  show z' + (e + g) = z + e
  rw [← hsum', add_comm e g, ← add_assoc]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
