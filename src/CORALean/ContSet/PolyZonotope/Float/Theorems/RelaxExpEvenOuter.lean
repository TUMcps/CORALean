import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExpEven
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorError
import CORALean.ContSet.PolyZonotope.Float.Theorems.MergedGenGap
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsSubMonomialLe
import CORALean.ContSet.PolyZonotope.Real.Theorems.SubMonomialNonpos
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient

/-!
# The recentred relaxation over-approximates, at the stored columns

The exact layer's argument at this layer's stored fields, with three roundings
charged instead of two. `abs_sub_monomial_le` and `sub_monomial_nonpos` are the
exact layer's and are what put the drift in `[-ξ_E, 0]`; the width bounding it
is a natural number both layers read off the same exponent matrix.

The third gap is the centre's. It is charged at coefficient `1` rather than at a
monomial, which is what a constant offset costs and what makes `generatorError`
the right box for it: the box already sums a row with no cancellation.

Storing the shift at its upward rounding is what keeps that gap one-sided —
the stored centre is then below the exact one, so the same `subUp` difference
that bounds a column's gap bounds the centre's.
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
/-- `Fin.sum_univ_add` at `relaxExpEven`'s dependent count, stated through the
projection because that is the form the goal has. -/
theorem PolyZonotope.aux_sum_univ_relaxExpEven_h {PZ : PolyZonotope 𝕋 n}
    {part : Split (Fin PZ.h) into (Fin d) and (Fin 2)} {k₀ : Fin PZ.p} (f : Fin (d + 1) → ℝ) :
    ∑ l : Fin (PZ.relaxExpEven part k₀).h, f l
      = ∑ l, f (Fin.castAdd 1 l) + ∑ l : Fin 1, f (Fin.natAdd d l) :=
  Fin.sum_univ_add f

omit [SoundFloatArithmetic 𝕋] in
/-- The same at the independent count. -/
theorem PolyZonotope.aux_sum_univ_relaxExpEven_q {PZ : PolyZonotope 𝕋 n}
    {part : Split (Fin PZ.h) into (Fin d) and (Fin 2)} {k₀ : Fin PZ.p} (f : Fin (PZ.q + 1) → ℝ) :
    ∑ j : Fin (PZ.relaxExpEven part k₀).q, f j
      = ∑ j, f (Fin.castAdd 1 j) + ∑ j : Fin 1, f (Fin.natAdd PZ.q j) :=
  Fin.sum_univ_add f

/-- The halved column is stored downward and its upward twin lies above the
exact half, so the gap between them covers it. -/
theorem PolyZonotope.aux_relaxGenEven_gap (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) (i : Fin n) :
    |(PZ.relaxWidth part k₀ : ℝ) / 2 * toReal (PZ.G i (part.right 0))
      - toReal (PZ.relaxGenEven part k₀ i)| ≤ toReal (PZ.relaxGapEven part k₀ i 1) := by
  -- halving rounds nothing, so each bound is the fold's own, divided by two
  have hlo : toReal (PZ.relaxGenEven part k₀ i)
      ≤ (PZ.relaxWidth part k₀ : ℝ) / 2 * toReal (PZ.G i (part.right 0)) := by
    rw [PolyZonotope.relaxGenEven, toReal_half]
    have h := nsmulDown_le (PZ.relaxWidth part k₀) (PZ.G i (part.right 0))
    linarith
  have hhi : (PZ.relaxWidth part k₀ : ℝ) / 2 * toReal (PZ.G i (part.right 0))
      ≤ toReal (PZ.relaxGenEvenUp part k₀ i) := by
    rw [PolyZonotope.relaxGenEvenUp, toReal_half]
    have h := le_nsmulUp (PZ.relaxWidth part k₀) (PZ.G i (part.right 0))
    linarith
  have hgap : toReal (PZ.relaxGenEvenUp part k₀ i) - toReal (PZ.relaxGenEven part k₀ i)
      ≤ toReal (PZ.relaxGapEven part k₀ i 1) := sub_le_subUp _ _
  rw [abs_le]
  constructor <;> linarith

/-- The recentred centre is stored below the exact one, and the gap between the
two roundings of that same subtraction bounds the difference. -/
theorem PolyZonotope.aux_relaxCentreEven_gap (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) (i : Fin n) :
    |toReal (PZ.c i) - (PZ.relaxWidth part k₀ : ℝ) / 2 * toReal (PZ.G i (part.right 0))
      - toReal (PZ.relaxCentreEven part k₀ i)| ≤ toReal (PZ.relaxGapEven part k₀ i 2) := by
  -- the shift is taken off at its upper rounding, so the stored centre is low
  have hhi : (PZ.relaxWidth part k₀ : ℝ) / 2 * toReal (PZ.G i (part.right 0))
      ≤ toReal (PZ.relaxGenEvenUp part k₀ i) := by
    rw [PolyZonotope.relaxGenEvenUp, toReal_half]
    have h := le_nsmulUp (PZ.relaxWidth part k₀) (PZ.G i (part.right 0))
    linarith
  have hstore : toReal (PZ.relaxCentreEven part k₀ i)
      ≤ toReal (PZ.c i) - toReal (PZ.relaxGenEvenUp part k₀ i) := subDown_le_sub _ _
  -- and the same subtraction rounded up lies above the exact centre
  have hlo : toReal (PZ.relaxGenEven part k₀ i)
      ≤ (PZ.relaxWidth part k₀ : ℝ) / 2 * toReal (PZ.G i (part.right 0)) := by
    rw [PolyZonotope.relaxGenEven, toReal_half]
    have h := nsmulDown_le (PZ.relaxWidth part k₀) (PZ.G i (part.right 0))
    linarith
  have hup : toReal (PZ.c i) - toReal (PZ.relaxGenEven part k₀ i)
      ≤ toReal (subUp (PZ.c i) (PZ.relaxGenEven part k₀ i)) := sub_le_subUp _ _
  have hgap : toReal (subUp (PZ.c i) (PZ.relaxGenEven part k₀ i))
      - toReal (PZ.relaxCentreEven part k₀ i)
      ≤ toReal (PZ.relaxGapEven part k₀ i 2) := sub_le_subUp _ _
  rw [abs_le]
  constructor <;> linarith

-- the three stored quantities and their three gaps, the drift split in two
theorem PolyZonotope.aux_relaxExpEven_nominal (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p)
    (hsim : ∀ k, k ≠ k₀ → PZ.E k (part.right 0) = PZ.E k (part.right 1))
    (heven : ∀ k, Even (PZ.E k (part.right 0)))
    (hevenj : Even (PZ.E k₀ (part.right 1)))
    (hle : PZ.E k₀ (part.right 1) ≤ PZ.E k₀ (part.right 0)) :
    nominalSet PZ ⊆ nominalSet (PZ.relaxExpEven part k₀)
      + (PolyZonotope.generatorError (PZ.relaxGapEven part k₀)).construct := by -- --- PROOF ---
  intro x hx
  obtain ⟨a, β, ha, hβ, hxi⟩ := PolyZonotope.mem_nominalSet_iff.mp hx
  have habs : |Real.PolyZonotope.monomial PZ.E a (part.right 0)
      - Real.PolyZonotope.monomial PZ.E a (part.right 1)| ≤ (PZ.relaxWidth part k₀ : ℝ) :=
    Real.PolyZonotope.abs_sub_monomial_le PZ.E ha hsim
  have hsign : Real.PolyZonotope.monomial PZ.E a (part.right 0)
      - Real.PolyZonotope.monomial PZ.E a (part.right 1) ≤ 0 :=
    Real.PolyZonotope.sub_monomial_nonpos PZ.E ha hsim heven hevenj hle
  have hnn : (0:ℝ) ≤ (PZ.relaxWidth part k₀ : ℝ) / 2 := by -- --- PROOF ---
    have h := Nat.cast_nonneg (α := ℝ) (PZ.relaxWidth part k₀)
    linarith
  -- one-sided drift: its midpoint is `-ξ_E/2` and its radius `ξ_E/2`
  have hmid : |Real.PolyZonotope.monomial PZ.E a (part.right 0)
      - Real.PolyZonotope.monomial PZ.E a (part.right 1) + (PZ.relaxWidth part k₀ : ℝ) / 2|
        ≤ (PZ.relaxWidth part k₀ : ℝ) / 2 := by
    rw [abs_le] at habs ⊢
    constructor <;> linarith [habs.1, habs.2]
  set t := Real.Zonotope.coefficient ((PZ.relaxWidth part k₀ : ℝ) / 2)
    (Real.PolyZonotope.monomial PZ.E a (part.right 0)
      - Real.PolyZonotope.monomial PZ.E a (part.right 1)
      + (PZ.relaxWidth part k₀ : ℝ) / 2) with ht
  have hcoef : (PZ.relaxWidth part k₀ : ℝ) / 2 * t
      = Real.PolyZonotope.monomial PZ.E a (part.right 0)
        - Real.PolyZonotope.monomial PZ.E a (part.right 1)
        + (PZ.relaxWidth part k₀ : ℝ) / 2 := by
    rw [ht]
    exact Real.Zonotope.mul_coefficient hmid
  -- the kept columns keep their monomials, and the merged one takes the second's
  have hmono : ∀ l : Fin d,
      Real.PolyZonotope.monomial (PZ.relaxExpEven part k₀).E a (Fin.castAdd 1 l)
        = Real.PolyZonotope.monomial PZ.E a (part.left l) := fun l => by
    simp only [Real.PolyZonotope.monomial, PolyZonotope.relaxExpEven, Fin.append_left]
    rfl
  have hlast : Real.PolyZonotope.monomial (PZ.relaxExpEven part k₀).E a (Fin.natAdd d 0)
      = Real.PolyZonotope.monomial PZ.E a (part.right 1) := by
    simp only [Real.PolyZonotope.monomial, PolyZonotope.relaxExpEven, Fin.append_right]
    rfl
  -- the point at the stored fields, and what the three gaps still owe it
  refine ⟨fun i => toReal (PZ.relaxCentreEven part k₀ i)
      + (∑ l : Fin d, toReal (PZ.G i (part.left l))
            * Real.PolyZonotope.monomial PZ.E a (part.left l)
          + toReal (PZ.mergedGen part i) * Real.PolyZonotope.monomial PZ.E a (part.right 1))
      + (∑ j, toReal (PZ.GI i j) * β j + toReal (PZ.relaxGenEven part k₀ i) * t),
    PolyZonotope.mem_nominalSet_iff.mpr ⟨a, Fin.append β fun _ => t, ha, ?_, ?_⟩,
    _, PolyZonotope.mem_generatorError (G := PZ.relaxGapEven part k₀)
      (Δ := fun i => ![toReal (PZ.G i (part.right 1)) + toReal (PZ.G i (part.right 0))
          - toReal (PZ.mergedGen part i),
        (PZ.relaxWidth part k₀ : ℝ) / 2 * toReal (PZ.G i (part.right 0))
          - toReal (PZ.relaxGenEven part k₀ i),
        toReal (PZ.c i) - (PZ.relaxWidth part k₀ : ℝ) / 2 * toReal (PZ.G i (part.right 0))
          - toReal (PZ.relaxCentreEven part k₀ i)])
      (t := ![Real.PolyZonotope.monomial PZ.E a (part.right 1), t, 1]) ?_ ?_, ?_⟩
  -- the fresh independent coefficient is what half the drift asks of the column
  · refine Fin.addCases (fun j => ?_) fun _ => ?_
    · rw [Fin.append_left]
      exact hβ j
    · rw [Fin.append_right, ht]
      exact Real.Zonotope.abs_coefficient_le_one hnn hmid
  · intro i
    rw [PolyZonotope.aux_sum_univ_relaxExpEven_h, PolyZonotope.aux_sum_univ_relaxExpEven_q]
    simp only [Fin.sum_univ_one, hmono, hlast]
    simp only [PolyZonotope.relaxExpEven, Fin.append_left, Fin.append_right]
  · refine fun i l => Fin.cases ?_ (fun l' => Fin.cases ?_ (fun l'' => ?_) l') l
    · exact PolyZonotope.mergedGen_gap PZ part i
    · exact PolyZonotope.aux_relaxGenEven_gap PZ part k₀ i
    · rw [Subsingleton.elim l'' 0]
      exact PolyZonotope.aux_relaxCentreEven_gap PZ part k₀ i
  · refine Fin.cases ?_ (fun l' => Fin.cases ?_ (fun l'' => ?_) l')
    · exact Real.PolyZonotope.abs_monomial_le_one PZ.E ha _
    · rw [ht]
      exact Real.Zonotope.abs_coefficient_le_one hnn hmid
    · rw [Subsingleton.elim l'' 0]
      exact le_of_eq abs_one
  -- the three gaps and the split drift recombine into the exact sums
  · funext i
    show toReal (PZ.relaxCentreEven part k₀ i)
          + (∑ l : Fin d, toReal (PZ.G i (part.left l))
              * Real.PolyZonotope.monomial PZ.E a (part.left l)
            + toReal (PZ.mergedGen part i) * Real.PolyZonotope.monomial PZ.E a (part.right 1))
          + (∑ j, toReal (PZ.GI i j) * β j + toReal (PZ.relaxGenEven part k₀ i) * t)
        + ∑ l, _ * _ = x i
    rw [hxi i, Fin.sum_univ_three,
      part.sum_split₂ fun l => toReal (PZ.G i l) * Real.PolyZonotope.monomial PZ.E a l,
      Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linear_combination toReal (PZ.G i (part.right 0)) * hcoef


-- =======================================  MAIN THEOREM  ======================================= --

/-- Merging two generators whose columns agree off `k₀`, with column `i` even,
`E_{k₀,j}` even and `E_{k₀,j} ≤ E_{k₀,i}`, over-approximates. -/
theorem PolyZonotope.relaxExpEven_outer (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p)
    (hsim : ∀ k, k ≠ k₀ → PZ.E k (part.right 0) = PZ.E k (part.right 1))
    (heven : ∀ k, Even (PZ.E k (part.right 0)))
    (hevenj : Even (PZ.E k₀ (part.right 1)))
    (hle : PZ.E k₀ (part.right 1) ≤ PZ.E k₀ (part.right 0)) :
    PZ.construct ⊆ (PZ.relaxExpEven part k₀).construct := by
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨z', hz', g, hg, hsum⟩ :=
    PolyZonotope.aux_relaxExpEven_nominal PZ part k₀ hsim heven hevenj hle hz
  refine ⟨z', hz', e + g, Interval.plus_outer _ _ ⟨e, he, g, hg, rfl⟩, ?_⟩
  -- `Set.image2` leaves the sum a beta-redex, which `rw` will not match
  have hsum' : z' + g = z := hsum
  show z' + (e + g) = z + e
  rw [← hsum', add_comm e g, ← add_assoc]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
