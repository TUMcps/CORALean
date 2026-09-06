import CORALean.ContSet.InflatedContSet.Theorems.LinCombSubset
import CORALean.ContSet.Interval.Float.Theorems.LinCombOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
import CORALean.ContSet.PolyZonotope.Float.Operations.LinComb
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.Zonotope.Float.Theorems.LinCombOuter
import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
import CORALean.ContSet.Zonotope.Real.Theorems.LinCombOuter

/-!
# `PolyZonotope.linComb` contains every segment between the two sets

`InflatedContSet.linComb_subset` reduces this to two obligations: the nominal
parts spill only by what rounded, and the box absorbs that spill along with the
segment between the two incoming boxes.

The nominal obligation is the exact `linComb` argument — `2λ-1` on the fresh
factor, `pairCoeffSum` and `pairCoeffDiff` on the independent block — with the
centre, the sliding generator and the paired independent generators displaced.
No stored value is unfolded: each cancels against its own residual or against
`linCombGIDiff`, so what remains is the exact identity.

The three dependent blocks contribute nothing to the spill: halving and negation
are exact, and the monomials are exponent data over ℕ throughout, so both counts
are what they are over ℝ.

Only `_outer`, as over ℝ, and for the exact layer's reason rather than a
rounding one: the independent coefficients cannot be tied to the same `λ`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   03-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `linComb`'s dependent generator count, stated through
the projection because that is the form the goal has and simp will not rewrite a
binder's type. Only the outermost split needs it. -/
theorem PolyZonotope.aux_sum_univ_linComb_h {PZ₁ PZ₂ : PolyZonotope 𝕋 n}
    (f : Fin (PZ₁.h + PZ₂.h + (PZ₁.h + PZ₂.h + 1)) → ℝ) :
    ∑ l : Fin (PZ₁.linComb PZ₂).h, f l
      = ∑ l, f (Fin.castAdd (PZ₁.h + PZ₂.h + 1) l)
        + ∑ l, f (Fin.natAdd (PZ₁.h + PZ₂.h) l) :=
  Fin.sum_univ_add f

omit [SoundFloatArithmetic 𝕋] in
/-- The independent count read off the projection, which is the only thing the
goal and the pairing lemmas disagree about: the block is not split here, the
pairing crossing the two halves rather than closing on each. -/
theorem PolyZonotope.aux_sum_univ_linComb_q {PZ₁ PZ₂ : PolyZonotope 𝕋 n}
    (f : Fin (PZ₁.q + PZ₂.q) → ℝ) :
    ∑ j : Fin (PZ₁.linComb PZ₂).q, f j = ∑ j : Fin (PZ₁.q + PZ₂.q), f j := rfl

/-- The independent block `linComb` would store if nothing rounded. -/
noncomputable def PolyZonotope.aux_linCombGIReal (PZ₁ PZ₂ : PolyZonotope 𝕋 n) (i : Fin n) :
    Fin (PZ₁.q + PZ₂.q) → ℝ :=
  Fin.append
    (Real.Zonotope.pairSum (fun j => toReal (PZ₁.GI i j)) (fun j => toReal (PZ₂.GI i j)))
    (Real.Zonotope.pairDiff (fun j => toReal (PZ₁.GI i j)) (fun j => toReal (PZ₂.GI i j)))

/-- What the stored independent generators are wrong by, entrywise, which is
what `linCombGIDiff` records. -/
theorem PolyZonotope.aux_linCombGI_error (PZ₁ PZ₂ : PolyZonotope 𝕋 n) (i : Fin n)
    (j : Fin (PZ₁.q + PZ₂.q)) :
    |PolyZonotope.aux_linCombGIReal PZ₁ PZ₂ i j
        - toReal (PolyZonotope.linCombGI addDown subDown PZ₁ PZ₂ i j)|
      ≤ toReal (PolyZonotope.linCombGIDiff PZ₁ PZ₂ i j) := by -- --- PROOF ---
  have hbr : ∀ j : Fin (PZ₁.q + PZ₂.q),
      toReal (PolyZonotope.linCombGI addDown subDown PZ₁ PZ₂ i j)
          ≤ PolyZonotope.aux_linCombGIReal PZ₁ PZ₂ i j
        ∧ PolyZonotope.aux_linCombGIReal PZ₁ PZ₂ i j
          ≤ toReal (PolyZonotope.linCombGI addUp subUp PZ₁ PZ₂ i j) := by
    simp only [PolyZonotope.linCombGI, PolyZonotope.aux_linCombGIReal]
    refine Fin.addCases ?_ ?_
    · intro k
      simp only [Fin.append_left]
      exact Zonotope.pairSum_bracket (PZ₁.GI i) (PZ₂.GI i) k
    · intro k
      simp only [Fin.append_right]
      exact Zonotope.pairDiff_bracket (PZ₁.GI i) (PZ₂.GI i) k
  -- the gap between the two directed spellings is what bounds the error
  obtain ⟨hlo, hhi⟩ := hbr j
  have hgap := sub_le_subUp (PolyZonotope.linCombGI addUp subUp PZ₁ PZ₂ i j)
    (PolyZonotope.linCombGI addDown subDown PZ₁ PZ₂ i j)
  simp only [PolyZonotope.linCombGIDiff]
  rw [abs_le]
  constructor <;> linarith

/-- One row of the exact independent generators against the coefficients the
segment supplies: the pairing gives back the two sets' own sums. -/
theorem PolyZonotope.aux_linCombGI_row (PZ₁ PZ₂ : PolyZonotope 𝕋 n) (i : Fin n)
    (β₁ : Fin PZ₁.q → ℝ) (β₂ : Fin PZ₂.q → ℝ) (lam : ℝ) :
    (∑ j, PolyZonotope.aux_linCombGIReal PZ₁ PZ₂ i j
        * Fin.append (Real.Zonotope.pairCoeffSum β₁ β₂ lam)
            (Real.Zonotope.pairCoeffDiff β₁ β₂ lam) j)
      = lam * (∑ j, toReal (PZ₁.GI i j) * β₁ j)
        + (1 - lam) * ∑ j, toReal (PZ₂.GI i j) * β₂ j := by -- --- PROOF ---
  rw [Fin.sum_univ_add]
  simp only [PolyZonotope.aux_linCombGIReal, Fin.append_left, Fin.append_right]
  exact Zonotope.sum_pair_mul (fun j => toReal (PZ₁.GI i j))
    (fun j => toReal (PZ₂.GI i j)) β₁ β₂ lam

/-- The two directed midpoints bracket the exact one, halving being exact. -/
theorem PolyZonotope.aux_midpoint_mem_residual (a b : Vec 𝕋 n) :
    (fun i => (toReal (a i) + toReal (b i)) / 2 - toReal (PolyZonotope.midpoint a b i))
      ∈ (PolyZonotope.midpointResidual a b).construct :=
  Interval.sub_mem_residual fun i => by
    refine ⟨?_, ?_⟩
    · rw [toReal_half]
      have := addDown_le_add (a i) (b i)
      linarith
    · rw [toReal_half]
      have := add_le_addUp (a i) (b i)
      linarith

omit [SoundFloatArithmetic 𝕋] in
/-- A non-negative shortfall stays inside the symmetric box its own bound spans,
whatever a coefficient in `[-1,1]` does with it. -/
theorem PolyZonotope.aux_mul_mem_symmetric {q R s : ℝ} (hq0 : 0 ≤ q) (hqR : q ≤ R)
    (hs0 : -1 ≤ s) (hs1 : s ≤ 1) : -R ≤ q * s ∧ q * s ≤ R :=
  ⟨by nlinarith, by nlinarith⟩

/-- The sliding generator rounds down, so its shortfall is non-negative and no
larger than the gap between the two directed halvings; the fresh factor spreads
it over `[-1,1]`. -/
theorem PolyZonotope.aux_halfDiff_mem_error (a b : Vec 𝕋 n) {lam : ℝ}
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    (fun i => ((toReal (a i) - toReal (b i)) / 2 - toReal (PolyZonotope.halfDiff a b i))
        * (2 * lam - 1))
      ∈ (PolyZonotope.halfDiffError a b).construct := by -- --- PROOF ---
  intro i
  have hdown : toReal (PolyZonotope.halfDiff a b i) = toReal (subDown (a i) (b i)) / 2 :=
    toReal_half _
  have hq0 : 0 ≤ (toReal (a i) - toReal (b i)) / 2
      - toReal (PolyZonotope.halfDiff a b i) := by
    rw [hdown]
    have := subDown_le_sub (a i) (b i)
    linarith
  -- and above by the gap between the two directed halvings
  have hqR : (toReal (a i) - toReal (b i)) / 2 - toReal (PolyZonotope.halfDiff a b i)
      ≤ toReal (subUp (half (subUp (a i) (b i))) (half (subDown (a i) (b i)))) := by
    have h1 := sub_le_subUp (half (subUp (a i) (b i))) (half (subDown (a i) (b i)))
    rw [toReal_half, toReal_half] at h1
    have h2 := sub_le_subUp (a i) (b i)
    rw [hdown]
    linarith
  obtain ⟨hlo, hhi⟩ := PolyZonotope.aux_mul_mem_symmetric hq0 hqR
    (by linarith : (-1:ℝ) ≤ 2 * lam - 1) (by linarith : 2 * lam - 1 ≤ 1)
  refine ⟨?_, hhi⟩
  show toReal (neg _) ≤ _
  rw [toReal_neg]
  exact hlo

/-! Constants pulled out of a generator block: `ring` cannot do that for itself,
a sum being one atom to it. Stated at `toReal (half _)` rather than after
unfolding it, so simp fires on the whole sum and never on the stored centre,
which has to stay folded to cancel against its residual. `aux_sum_mul` strips a
coefficient's common factor first, which is why the two halving lemmas are
needed only in their bare form. -/

theorem PolyZonotope.aux_sum_mul {k : ℕ} (t : ℝ) (g : Fin k → 𝕋) (b : Fin k → ℝ) :
    ∑ j, toReal (g j) * (t * b j) = t * ∑ j, toReal (g j) * b j := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem PolyZonotope.aux_sum_half {k : ℕ} (g : Fin k → 𝕋) (m : Fin k → ℝ) :
    ∑ l, toReal (half (g l)) * m l = 1 / 2 * ∑ l, toReal (g l) * m l := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [toReal_half]; ring

/-- The same at the negated block, which is the only place a sign is stored. -/
theorem PolyZonotope.aux_sum_neg_half {k : ℕ} (g : Fin k → 𝕋) (m : Fin k → ℝ) :
    ∑ l, toReal (neg (half (g l))) * m l = -(1 / 2) * ∑ l, toReal (g l) * m l := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [toReal_neg, toReal_half]; ring

-- the witness is one nested `Fin.append` term, re-elaborated at every `Fin.addCases` branch
set_option maxHeartbeats 400000 in
theorem PolyZonotope.aux_linComb_nominal (PZ₁ PZ₂ : PolyZonotope 𝕋 n) :
    segments (nominalSet PZ₁) (nominalSet PZ₂) ⊆
      nominalSet (PZ₁.linComb PZ₂)
        + ((PolyZonotope.midpointResidual PZ₁.c PZ₂.c).construct
            + ((PolyZonotope.halfDiffError PZ₁.c PZ₂.c).construct
                + (Zonotope.generatorError
                    (PolyZonotope.linCombGIDiff PZ₁ PZ₂)).construct)) := by -- --- PROOF ---
  rintro _ ⟨y₁, hy₁', y₂, hy₂', lam, ⟨hl0, hl1⟩, rfl⟩
  obtain ⟨a₁, β₁, ha₁, hβ₁, hy₁⟩ := PolyZonotope.mem_nominalSet_iff.mp hy₁'
  obtain ⟨a₂, β₂, ha₂, hβ₂, hy₂⟩ := PolyZonotope.mem_nominalSet_iff.mp hy₂'
  have hcf : ∀ j : Fin (PZ₁.q + PZ₂.q),
      |Fin.append (Real.Zonotope.pairCoeffSum β₁ β₂ lam)
        (Real.Zonotope.pairCoeffDiff β₁ β₂ lam) j| ≤ 1 := by
    refine Fin.addCases ?_ ?_
    · intro j
      simpa using Real.Zonotope.abs_pairCoeffSum_le_one hβ₁ hβ₂ hl0 hl1 j
    · intro j
      simpa using Real.Zonotope.abs_pairCoeffDiff_le_one hβ₁ hβ₂ hl0 hl1 j
  -- the witness: the two factor vectors appended, plus the fresh segment factor
  refine ⟨fun i => toReal ((PZ₁.linComb PZ₂).c i)
            + (∑ l, toReal ((PZ₁.linComb PZ₂).G i l)
                * Real.PolyZonotope.monomial (PZ₁.linComb PZ₂).E
                    (Fin.append (Fin.append a₁ a₂) (fun _ : Fin 1 => 2 * lam - 1)) l)
            + ∑ j, toReal ((PZ₁.linComb PZ₂).GI i j)
                * Fin.append (Real.Zonotope.pairCoeffSum β₁ β₂ lam)
                    (Real.Zonotope.pairCoeffDiff β₁ β₂ lam) j,
          PolyZonotope.mem_nominalSet_iff.mpr
            ⟨Fin.append (Fin.append a₁ a₂) (fun _ : Fin 1 => 2 * lam - 1), _, ?_, hcf,
             fun _ => rfl⟩,
          _, ⟨_, PolyZonotope.aux_midpoint_mem_residual PZ₁.c PZ₂.c,
              _, ⟨_, PolyZonotope.aux_halfDiff_mem_error PZ₁.c PZ₂.c hl0 hl1,
                  _, Zonotope.mem_generatorError
                       (fun i j => PolyZonotope.aux_linCombGI_error PZ₁ PZ₂ i j) hcf,
                  rfl⟩, rfl⟩, ?_⟩
  -- every appended factor is admissible, the fresh one because `2λ-1` lies in `[-1,1]`
  · refine Fin.addCases ?_ ?_
    · refine Fin.addCases ?_ ?_
      · intro k
        simpa using ha₁ k
      · intro k
        simpa using ha₂ k
    · intro _
      simp only [Fin.append_right]
      rw [abs_le]
      constructor <;> linarith
  · funext i
    -- the stored independent generators and their shortfalls recombine
    have hGI : (∑ j : Fin (PZ₁.q + PZ₂.q),
          toReal (PolyZonotope.linCombGI addDown subDown PZ₁ PZ₂ i j)
            * Fin.append (Real.Zonotope.pairCoeffSum β₁ β₂ lam)
                (Real.Zonotope.pairCoeffDiff β₁ β₂ lam) j)
        + (∑ j, (PolyZonotope.aux_linCombGIReal PZ₁ PZ₂ i j
              - toReal (PolyZonotope.linCombGI addDown subDown PZ₁ PZ₂ i j))
            * Fin.append (Real.Zonotope.pairCoeffSum β₁ β₂ lam)
                (Real.Zonotope.pairCoeffDiff β₁ β₂ lam) j)
        = ∑ j, PolyZonotope.aux_linCombGIReal PZ₁ PZ₂ i j
            * Fin.append (Real.Zonotope.pairCoeffSum β₁ β₂ lam)
                (Real.Zonotope.pairCoeffDiff β₁ β₂ lam) j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [PolyZonotope.aux_linCombGI_row PZ₁ PZ₂ i β₁ β₂ lam] at hGI
    -- split as the goal is split, or the two block sums are different atoms
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right] at hGI
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hy₁ i, hy₂ i, PolyZonotope.aux_sum_univ_linComb_h,
      PolyZonotope.aux_sum_univ_linComb_q]
    simp only [PolyZonotope.linComb, Fin.sum_univ_add, Fin.sum_univ_one,
      Real.PolyZonotope.monomial_linCombE_fst, Real.PolyZonotope.monomial_linCombE_snd,
      Real.PolyZonotope.monomial_linCombE_last, Real.PolyZonotope.monomial_plusE_left,
      Real.PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right,
      PolyZonotope.aux_sum_mul, PolyZonotope.aux_sum_half,
      PolyZonotope.aux_sum_neg_half]
    linarith [hGI]

/-- The box absorbs the two incoming boxes, both centre roundings and the
independent block's. -/
theorem PolyZonotope.aux_linComb_error (PZ₁ PZ₂ : PolyZonotope 𝕋 n) :
    segments PZ₁.err.construct PZ₂.err.construct
        + ((PolyZonotope.midpointResidual PZ₁.c PZ₂.c).construct
            + ((PolyZonotope.halfDiffError PZ₁.c PZ₂.c).construct
                + (Zonotope.generatorError
                    (PolyZonotope.linCombGIDiff PZ₁ PZ₂)).construct))
      ⊆ (PZ₁.linComb PZ₂).err.construct :=
  subset_trans
    (Set.add_subset_add (Interval.linComb_outer PZ₁.err PZ₂.err)
      (subset_trans (Set.add_subset_add_left (Interval.plus_outer _ _))
        (Interval.plus_outer _ _)))
    (Interval.plus_outer _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.linComb_outer (PZ₁ PZ₂ : PolyZonotope 𝕋 n) :
    segments PZ₁.construct PZ₂.construct ⊆ (PZ₁.linComb PZ₂).construct :=
  InflatedContSet.linComb_subset (PolyZonotope.aux_linComb_nominal PZ₁ PZ₂)
    (PolyZonotope.aux_linComb_error PZ₁ PZ₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
