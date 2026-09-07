import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExp
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorError
import CORALean.ContSet.PolyZonotope.Float.Theorems.MergedGenGap
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsSubMonomialLe
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient

/-!
# `relaxExp` over-approximates, merging two similar generators

The exact layer's argument at this layer's stored columns, with two roundings
charged. `abs_sub_monomial_le` is the exact layer's and is what bounds the
drift between the two monomials; the width it is bounded by is a natural number
both layers read off the same exponent matrix.

Each stored column is a sum rounded down, so each is off by at most its gap to
the upward rounding, and the coefficient reading it — a monomial for the merged
dependent column, `Zonotope.coefficient` for the new independent one — is in
`[-1,1]`. That is one `generatorError` with two columns.

The independent coefficient is one scalar for the whole column, as over ℝ, which
is why the column has to be stored collinear with the generator it relaxes:
rounding each coordinate outward on its own would not be reachable by any single
coefficient.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n d : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `relaxExp`'s dependent count, stated through the
projection because that is the form the goal has. -/
theorem PolyZonotope.aux_sum_univ_relaxExp_h {pZ : PolyZonotope 𝕋 n}
    {part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)} {k₀ : Fin pZ.p} (f : Fin (d + 1) → ℝ) :
    ∑ l : Fin (pZ.relaxExp part k₀).h, f l
      = ∑ l, f (Fin.castAdd 1 l) + ∑ l : Fin 1, f (Fin.natAdd d l) :=
  Fin.sum_univ_add f

omit [SoundFloatArithmetic 𝕋] in
/-- The same at the independent count. -/
theorem PolyZonotope.aux_sum_univ_relaxExp_q {pZ : PolyZonotope 𝕋 n}
    {part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)} {k₀ : Fin pZ.p} (f : Fin (pZ.q + 1) → ℝ) :
    ∑ j : Fin (pZ.relaxExp part k₀).q, f j
      = ∑ j, f (Fin.castAdd 1 j) + ∑ j : Fin 1, f (Fin.natAdd pZ.q j) :=
  Fin.sum_univ_add f

/-- The new independent column is `ξ_E` copies added downward, so it too is off
by at most its gap to the upward fold. -/
theorem PolyZonotope.aux_relaxGen_gap (pZ : PolyZonotope 𝕋 n)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) (i : Fin n) :
    |(pZ.relaxWidth part k₀ : ℝ) * toReal (pZ.G i (part.right 0))
      - toReal (pZ.relaxGen part k₀ i)| ≤ toReal (pZ.relaxGap part k₀ i 1) := by -- --- PROOF ---
  have hlo : toReal (pZ.relaxGen part k₀ i)
      ≤ (pZ.relaxWidth part k₀ : ℝ) * toReal (pZ.G i (part.right 0)) := nsmulDown_le _ _
  have hhi : (pZ.relaxWidth part k₀ : ℝ) * toReal (pZ.G i (part.right 0))
      ≤ toReal (nsmulUp (pZ.relaxWidth part k₀) (pZ.G i (part.right 0))) := le_nsmulUp _ _
  have hgap : toReal (nsmulUp (pZ.relaxWidth part k₀) (pZ.G i (part.right 0)))
      - toReal (pZ.relaxGen part k₀ i) ≤ toReal (pZ.relaxGap part k₀ i 1) := sub_le_subUp _ _
  rw [abs_le]
  constructor <;> linarith

-- the two stored columns and their two gaps, the drift carried by the second
theorem PolyZonotope.aux_relaxExp_nominal (pZ : PolyZonotope 𝕋 n)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p)
    (hsim : ∀ k, k ≠ k₀ → pZ.E k (part.right 0) = pZ.E k (part.right 1)) :
    nominalSet pZ ⊆ nominalSet (pZ.relaxExp part k₀)
      + (PolyZonotope.generatorError (pZ.relaxGap part k₀)).construct := by -- --- PROOF ---
  intro x hx
  obtain ⟨a, β, ha, hβ, hxi⟩ := PolyZonotope.mem_nominalSet_iff.mp hx
  have habs : |Real.PolyZonotope.monomial pZ.E a (part.right 0)
      - Real.PolyZonotope.monomial pZ.E a (part.right 1)| ≤ (pZ.relaxWidth part k₀ : ℝ) :=
    Real.PolyZonotope.abs_sub_monomial_le pZ.E ha hsim
  have hnn : (0:ℝ) ≤ (pZ.relaxWidth part k₀ : ℝ) := Nat.cast_nonneg _
  set t := Real.Zonotope.coefficient (pZ.relaxWidth part k₀ : ℝ)
    (Real.PolyZonotope.monomial pZ.E a (part.right 0)
      - Real.PolyZonotope.monomial pZ.E a (part.right 1)) with ht
  have hcoef : (pZ.relaxWidth part k₀ : ℝ) * t
      = Real.PolyZonotope.monomial pZ.E a (part.right 0)
        - Real.PolyZonotope.monomial pZ.E a (part.right 1) := by
    rw [ht]
    exact Real.Zonotope.mul_coefficient habs
  -- the kept columns keep their monomials, and the merged one takes the second's
  have hmono : ∀ l : Fin d,
      Real.PolyZonotope.monomial (pZ.relaxExp part k₀).E a (Fin.castAdd 1 l)
        = Real.PolyZonotope.monomial pZ.E a (part.left l) := fun l => by
    simp only [Real.PolyZonotope.monomial, PolyZonotope.relaxExp, Fin.append_left]
    rfl
  have hlast : Real.PolyZonotope.monomial (pZ.relaxExp part k₀).E a (Fin.natAdd d 0)
      = Real.PolyZonotope.monomial pZ.E a (part.right 1) := by
    simp only [Real.PolyZonotope.monomial, PolyZonotope.relaxExp, Fin.append_right]
    rfl
  -- the point at the stored columns, and what the two gaps still owe it
  refine ⟨fun i => toReal (pZ.c i)
      + (∑ l : Fin d, toReal (pZ.G i (part.left l))
            * Real.PolyZonotope.monomial pZ.E a (part.left l)
          + toReal (pZ.mergedGen part i) * Real.PolyZonotope.monomial pZ.E a (part.right 1))
      + (∑ j, toReal (pZ.GI i j) * β j + toReal (pZ.relaxGen part k₀ i) * t),
    PolyZonotope.mem_nominalSet_iff.mpr ⟨a, Fin.append β fun _ => t, ha, ?_, ?_⟩,
    _, PolyZonotope.mem_generatorError (G := pZ.relaxGap part k₀)
      (Δ := fun i => ![toReal (pZ.G i (part.right 1)) + toReal (pZ.G i (part.right 0))
          - toReal (pZ.mergedGen part i),
        (pZ.relaxWidth part k₀ : ℝ) * toReal (pZ.G i (part.right 0))
          - toReal (pZ.relaxGen part k₀ i)])
      (t := ![Real.PolyZonotope.monomial pZ.E a (part.right 1), t]) ?_ ?_, ?_⟩
  -- the fresh independent coefficient is what the drift asks of the new column
  · refine Fin.addCases (fun j => ?_) fun _ => ?_
    · rw [Fin.append_left]
      exact hβ j
    · rw [Fin.append_right, ht]
      exact Real.Zonotope.abs_coefficient_le_one hnn habs
  · intro i
    rw [PolyZonotope.aux_sum_univ_relaxExp_h, PolyZonotope.aux_sum_univ_relaxExp_q]
    simp only [Fin.sum_univ_one, hmono, hlast]
    simp only [PolyZonotope.relaxExp, Fin.append_left, Fin.append_right]
  · refine fun i l => Fin.cases ?_ (fun l' => ?_) l
    · exact PolyZonotope.mergedGen_gap pZ part i
    · rw [Subsingleton.elim l' 0]
      exact PolyZonotope.aux_relaxGen_gap pZ part k₀ i
  · refine Fin.cases ?_ (fun l' => ?_)
    · exact Real.PolyZonotope.abs_monomial_le_one pZ.E ha _
    · rw [Subsingleton.elim l' 0, ht]
      exact Real.Zonotope.abs_coefficient_le_one hnn habs
  -- the two stored columns, their gaps and the drift recombine into the exact sums
  · funext i
    show toReal (pZ.c i)
          + (∑ l : Fin d, toReal (pZ.G i (part.left l))
              * Real.PolyZonotope.monomial pZ.E a (part.left l)
            + toReal (pZ.mergedGen part i) * Real.PolyZonotope.monomial pZ.E a (part.right 1))
          + (∑ j, toReal (pZ.GI i j) * β j + toReal (pZ.relaxGen part k₀ i) * t)
        + ∑ l, _ * _ = x i
    rw [hxi i, Fin.sum_univ_two,
      part.sum_split₂ fun l => toReal (pZ.G i l) * Real.PolyZonotope.monomial pZ.E a l,
      Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination toReal (pZ.G i (part.right 0)) * hcoef


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.relaxExp_outer (pZ : PolyZonotope 𝕋 n)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p)
    (hsim : ∀ k, k ≠ k₀ → pZ.E k (part.right 0) = pZ.E k (part.right 1)) :
    pZ.construct ⊆ (pZ.relaxExp part k₀).construct := by -- --- PROOF ---
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨z', hz', g, hg, hsum⟩ := PolyZonotope.aux_relaxExp_nominal pZ part k₀ hsim hz
  refine ⟨z', hz', e + g, Interval.plus_outer _ _ ⟨e, he, g, hg, rfl⟩, ?_⟩
  -- `Set.image2` leaves the sum a beta-redex, which `rw` will not match
  have hsum' : z' + g = z := hsum
  show z' + (e + g) = z + e
  rw [← hsum', add_comm e g, ← add_assoc]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
