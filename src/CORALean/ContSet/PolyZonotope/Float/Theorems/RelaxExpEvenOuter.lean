module

public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExpEven
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MergedGenGap
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsSubMonomialLe
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SubMonomialNonpos
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient

@[expose] public section

/-!
# The recentered relaxation over-approximates, at the stored columns

The exact layer's argument at this layer's stored fields, with three roundings
charged instead of two. `abs_sub_monomial_le` and `sub_monomial_nonpos` are the
exact layer's and are what put the drift in `[-ξ_E, 0]`; the width bounding it
is a natural number both layers read off the same exponent matrix.

The third gap is the center's. It is charged at coefficient `1` rather than at a
monomial, which is what a constant offset costs and what makes `generatorError`
the right box for it: the box already sums a row with no cancellation.

Storing the shift at its upward rounding is what keeps that gap one-sided —
the stored center is then below the exact one, so the same `subUp` difference
that bounds a column's gap bounds the center's.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n d : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `relaxExpEven`'s dependent count, stated through the
projection because that is the form the goal has. -/
theorem PolyZonotope.aux_sum_univ_relaxExpEven_h {pZ : PolyZonotope (Vec 𝕋 n)}
    {part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)} {k₀ : Fin pZ.p} (f : Fin (d + 1) → ℝ) :
    ∑ l : Fin (pZ.relaxExpEven part k₀).h, f l
      = ∑ l, f (Fin.castAdd 1 l) + ∑ l : Fin 1, f (Fin.natAdd d l) :=
  Fin.sum_univ_add f

omit [SoundFloatArithmetic 𝕋] in
/-- The same at the independent count. -/
theorem PolyZonotope.aux_sum_univ_relaxExpEven_q {pZ : PolyZonotope (Vec 𝕋 n)}
    {part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)} {k₀ : Fin pZ.p} (f : Fin (pZ.q + 1) → ℝ) :
    ∑ j : Fin (pZ.relaxExpEven part k₀).q, f j
      = ∑ j, f (Fin.castAdd 1 j) + ∑ j : Fin 1, f (Fin.natAdd pZ.q j) :=
  Fin.sum_univ_add f

/-- The halved column is stored downward and its upward twin lies above the
exact half, so the gap between them covers it. -/
theorem PolyZonotope.aux_relaxGenEven_gap (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) (i : Fin n) :
    |(pZ.relaxWidth part k₀ : ℝ) / 2 * toReal (pZ.G (part.right 0) i)
      - toReal (pZ.relaxGenEven part k₀ i)|
        ≤ toReal (pZ.relaxGapEven part k₀ i 1) := by -- --- PROOF ---
  -- halving rounds nothing, so each bound is the fold's own, divided by two
  have hlo : toReal (pZ.relaxGenEven part k₀ i)
      ≤ (pZ.relaxWidth part k₀ : ℝ) / 2 * toReal (pZ.G (part.right 0) i) := by
    rw [PolyZonotope.relaxGenEven, toReal_half]
    have h := nsmulDown_le (pZ.relaxWidth part k₀) (pZ.G (part.right 0) i)
    linarith
  have hhi : (pZ.relaxWidth part k₀ : ℝ) / 2 * toReal (pZ.G (part.right 0) i)
      ≤ toReal (pZ.relaxGenEvenUp part k₀ i) := by
    rw [PolyZonotope.relaxGenEvenUp, toReal_half]
    have h := le_nsmulUp (pZ.relaxWidth part k₀) (pZ.G (part.right 0) i)
    linarith
  have hgap : toReal (pZ.relaxGenEvenUp part k₀ i) - toReal (pZ.relaxGenEven part k₀ i)
      ≤ toReal (pZ.relaxGapEven part k₀ i 1) := sub_le_subUp _ _
  rw [abs_le]
  constructor <;> linarith

/-- The recentered center is stored below the exact one, and the gap between the
two roundings of that same subtraction bounds the difference. -/
theorem PolyZonotope.aux_relaxCenterEven_gap (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) (i : Fin n) :
    |toReal (pZ.c i) - (pZ.relaxWidth part k₀ : ℝ) / 2 * toReal (pZ.G (part.right 0) i)
      - toReal (pZ.relaxCenterEven part k₀ i)|
        ≤ toReal (pZ.relaxGapEven part k₀ i 2) := by -- --- PROOF ---
  -- the shift is taken off at its upper rounding, so the stored center is low
  have hhi : (pZ.relaxWidth part k₀ : ℝ) / 2 * toReal (pZ.G (part.right 0) i)
      ≤ toReal (pZ.relaxGenEvenUp part k₀ i) := by
    rw [PolyZonotope.relaxGenEvenUp, toReal_half]
    have h := le_nsmulUp (pZ.relaxWidth part k₀) (pZ.G (part.right 0) i)
    linarith
  have hstore : toReal (pZ.relaxCenterEven part k₀ i)
      ≤ toReal (pZ.c i) - toReal (pZ.relaxGenEvenUp part k₀ i) := subDown_le_sub _ _
  -- and the same subtraction rounded up lies above the exact center
  have hlo : toReal (pZ.relaxGenEven part k₀ i)
      ≤ (pZ.relaxWidth part k₀ : ℝ) / 2 * toReal (pZ.G (part.right 0) i) := by
    rw [PolyZonotope.relaxGenEven, toReal_half]
    have h := nsmulDown_le (pZ.relaxWidth part k₀) (pZ.G (part.right 0) i)
    linarith
  have hup : toReal (pZ.c i) - toReal (pZ.relaxGenEven part k₀ i)
      ≤ toReal (subUp (pZ.c i) (pZ.relaxGenEven part k₀ i)) := sub_le_subUp _ _
  have hgap : toReal (subUp (pZ.c i) (pZ.relaxGenEven part k₀ i))
      - toReal (pZ.relaxCenterEven part k₀ i)
      ≤ toReal (pZ.relaxGapEven part k₀ i 2) := sub_le_subUp _ _
  rw [abs_le]
  constructor <;> linarith

-- the three stored quantities and their three gaps, the drift split in two
theorem PolyZonotope.aux_relaxExpEven_nominal (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p)
    (hsim : ∀ k, k ≠ k₀ → pZ.E k (part.right 0) = pZ.E k (part.right 1))
    (heven : ∀ k, Even (pZ.E k (part.right 0)))
    (hevenj : Even (pZ.E k₀ (part.right 1)))
    (hle : pZ.E k₀ (part.right 1) ≤ pZ.E k₀ (part.right 0)) :
    nominalSet pZ ⊆ nominalSet (pZ.relaxExpEven part k₀)
      + (PolyZonotope.generatorError (pZ.relaxGapEven part k₀)).construct := by -- --- PROOF ---
  intro x hx
  obtain ⟨a, β, ha, hβ, hxi⟩ := PolyZonotope.mem_nominalSet_iff.mp hx
  have habs : |Real.PolyZonotope.monomial pZ.E a (part.right 0)
      - Real.PolyZonotope.monomial pZ.E a (part.right 1)| ≤ (pZ.relaxWidth part k₀ : ℝ) :=
    Real.PolyZonotope.abs_sub_monomial_le pZ.E ha hsim
  have hsign : Real.PolyZonotope.monomial pZ.E a (part.right 0)
      - Real.PolyZonotope.monomial pZ.E a (part.right 1) ≤ 0 :=
    Real.PolyZonotope.sub_monomial_nonpos pZ.E ha hsim heven hevenj hle
  have hnn : (0:ℝ) ≤ (pZ.relaxWidth part k₀ : ℝ) / 2 := by
    have h := Nat.cast_nonneg (α := ℝ) (pZ.relaxWidth part k₀)
    linarith
  -- one-sided drift: its midpoint is `-ξ_E/2` and its radius `ξ_E/2`
  have hmid : |Real.PolyZonotope.monomial pZ.E a (part.right 0)
      - Real.PolyZonotope.monomial pZ.E a (part.right 1) + (pZ.relaxWidth part k₀ : ℝ) / 2|
        ≤ (pZ.relaxWidth part k₀ : ℝ) / 2 := by
    rw [abs_le] at habs ⊢
    constructor <;> linarith [habs.1, habs.2]
  set t := Real.Zonotope.coefficient ((pZ.relaxWidth part k₀ : ℝ) / 2)
    (Real.PolyZonotope.monomial pZ.E a (part.right 0)
      - Real.PolyZonotope.monomial pZ.E a (part.right 1)
      + (pZ.relaxWidth part k₀ : ℝ) / 2) with ht
  have hcoef : (pZ.relaxWidth part k₀ : ℝ) / 2 * t
      = Real.PolyZonotope.monomial pZ.E a (part.right 0)
        - Real.PolyZonotope.monomial pZ.E a (part.right 1)
        + (pZ.relaxWidth part k₀ : ℝ) / 2 := by
    rw [ht]
    exact Real.Zonotope.mul_coefficient hmid
  -- the kept columns keep their monomials, and the merged one takes the second's
  have hmono : ∀ l : Fin d,
      Real.PolyZonotope.monomial (pZ.relaxExpEven part k₀).E a (Fin.castAdd 1 l)
        = Real.PolyZonotope.monomial pZ.E a (part.left l) := fun l => by
    simp only [Real.PolyZonotope.monomial, PolyZonotope.relaxExpEven, Fin.append_left]
    rfl
  have hlast : Real.PolyZonotope.monomial (pZ.relaxExpEven part k₀).E a (Fin.natAdd d 0)
      = Real.PolyZonotope.monomial pZ.E a (part.right 1) := by
    simp only [Real.PolyZonotope.monomial, PolyZonotope.relaxExpEven, Fin.append_right]
    rfl
  -- the point at the stored fields, and what the three gaps still owe it
  refine ⟨fun i => toReal (pZ.relaxCenterEven part k₀ i)
      + (∑ l : Fin d, toReal (pZ.G (part.left l) i)
            * Real.PolyZonotope.monomial pZ.E a (part.left l)
          + toReal (pZ.mergedGen part i) * Real.PolyZonotope.monomial pZ.E a (part.right 1))
      + (∑ j, toReal (pZ.GI j i) * β j + toReal (pZ.relaxGenEven part k₀ i) * t),
    PolyZonotope.mem_nominalSet_iff.mpr ⟨a, Fin.append β fun _ => t, ha, ?_, ?_⟩,
    _, PolyZonotope.mem_generatorError (G := pZ.relaxGapEven part k₀)
      (Δ := fun i => ![toReal (pZ.G (part.right 1) i) + toReal (pZ.G (part.right 0) i)
          - toReal (pZ.mergedGen part i),
        (pZ.relaxWidth part k₀ : ℝ) / 2 * toReal (pZ.G (part.right 0) i)
          - toReal (pZ.relaxGenEven part k₀ i),
        toReal (pZ.c i) - (pZ.relaxWidth part k₀ : ℝ) / 2 * toReal (pZ.G (part.right 0) i)
          - toReal (pZ.relaxCenterEven part k₀ i)])
      (t := ![Real.PolyZonotope.monomial pZ.E a (part.right 1), t, 1]) ?_ ?_, ?_⟩
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
    · exact PolyZonotope.mergedGen_gap pZ part i
    · exact PolyZonotope.aux_relaxGenEven_gap pZ part k₀ i
    · rw [Subsingleton.elim l'' 0]
      exact PolyZonotope.aux_relaxCenterEven_gap pZ part k₀ i
  · refine Fin.cases ?_ (fun l' => Fin.cases ?_ (fun l'' => ?_) l')
    · exact Real.PolyZonotope.abs_monomial_le_one pZ.E ha _
    · rw [ht]
      exact Real.Zonotope.abs_coefficient_le_one hnn hmid
    · rw [Subsingleton.elim l'' 0]
      exact le_of_eq abs_one
  -- the three gaps and the split drift recombine into the exact sums
  · funext i
    show toReal (pZ.relaxCenterEven part k₀ i)
          + (∑ l : Fin d, toReal (pZ.G (part.left l) i)
              * Real.PolyZonotope.monomial pZ.E a (part.left l)
            + toReal (pZ.mergedGen part i) * Real.PolyZonotope.monomial pZ.E a (part.right 1))
          + (∑ j, toReal (pZ.GI j i) * β j + toReal (pZ.relaxGenEven part k₀ i) * t)
        + ∑ l, _ * _ = x i
    rw [hxi i, Fin.sum_univ_three,
      part.sum_split₂ fun l => toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l,
      Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linear_combination toReal (pZ.G (part.right 0) i) * hcoef


-- =======================================  MAIN THEOREM  ======================================= --

/-- Merging two generators whose columns agree off `k₀`, with column `i` even,
`E_{k₀,j}` even and `E_{k₀,j} ≤ E_{k₀,i}`, over-approximates. -/
theorem PolyZonotope.relaxExpEven_outer (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p)
    (hsim : ∀ k, k ≠ k₀ → pZ.E k (part.right 0) = pZ.E k (part.right 1))
    (heven : ∀ k, Even (pZ.E k (part.right 0)))
    (hevenj : Even (pZ.E k₀ (part.right 1)))
    (hle : pZ.E k₀ (part.right 1) ≤ pZ.E k₀ (part.right 0)) :
    pZ.construct ⊆ (pZ.relaxExpEven part k₀).construct := by -- --- PROOF ---
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨z', hz', g, hg, hsum⟩ :=
    PolyZonotope.aux_relaxExpEven_nominal pZ part k₀ hsim heven hevenj hle hz
  refine ⟨z', hz', e + g, Interval.plus_outer _ _ ⟨e, he, g, hg, rfl⟩, ?_⟩
  -- `Set.image2` leaves the sum a beta-redex, which `rw` will not match
  have hsum' : z' + g = z := hsum
  show z' + (e + g) = z + e
  rw [← hsum', add_comm e g, ← add_assoc]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
