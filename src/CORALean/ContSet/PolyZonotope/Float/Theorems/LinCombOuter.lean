import CORALean.ContSet.InflatedContSet.Theorems.LinCombSubset
import CORALean.ContSet.Interval.Float.Theorems.LinCombOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
import CORALean.ContSet.PolyZonotope.Float.Operations.LinComb
import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombOuter

/-!
# `PolyZonotope.linComb` contains every segment between the two sets

`InflatedContSet.linComb_subset` reduces this to two obligations: the nominal
parts spill only by the two centre roundings, and the box absorbs that spill
along with the segment between the two incoming boxes.

The nominal obligation is the exact `linComb` argument — `2λ-1` on the fresh
factor, `λβ₁` and `(1-λ)β₂` on the independent coefficients — with the centre
and the sliding generator displaced. Neither stored value is unfolded: they
cancel against their own residuals, so what remains is the exact identity.

The three dependent blocks contribute nothing to the spill. Halving and negation
are exact, so `½G₁`, `½G₂` and `-½G₂` are the exact layer's blocks and not
roundings of them, and the monomials are exponent data over ℕ throughout. Both
counts are therefore what they are over ℝ.

Only `_outer`, as over ℝ, and for the exact layer's reason rather than for a
rounding one: the independent coefficients come out as `λβ₁` and `(1-λ)β₂`,
which the representation cannot record as tied to the same `λ` as the dependent
part.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem PolyZonotope.linComb_h (PZ₁ PZ₂ : PolyZonotope 𝕋 n) :
    (PZ₁.linComb PZ₂).h = PZ₁.h + PZ₂.h + (PZ₁.h + PZ₂.h + 1) := rfl

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem PolyZonotope.linComb_q (PZ₁ PZ₂ : PolyZonotope 𝕋 n) :
    (PZ₁.linComb PZ₂).q = PZ₁.q + PZ₂.q := rfl

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
/-- The same at the independent generator count. -/
theorem PolyZonotope.aux_sum_univ_linComb_q {PZ₁ PZ₂ : PolyZonotope 𝕋 n}
    (f : Fin (PZ₁.q + PZ₂.q) → ℝ) :
    ∑ j : Fin (PZ₁.linComb PZ₂).q, f j
      = ∑ j, f (Fin.castAdd PZ₂.q j) + ∑ j, f (Fin.natAdd PZ₁.q j) :=
  Fin.sum_univ_add f

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
      ∈ (PolyZonotope.halfDiffError a b).construct := by
  intro i
  have hdown : toReal (PolyZonotope.halfDiff a b i) = toReal (subDown (a i) (b i)) / 2 :=
    toReal_half _
  have hq0 : 0 ≤ (toReal (a i) - toReal (b i)) / 2
      - toReal (PolyZonotope.halfDiff a b i) := by
    rw [hdown]
    have := subDown_le_sub (a i) (b i)
    linarith
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

set_option maxHeartbeats 400000 in
theorem PolyZonotope.aux_linComb_nominal (PZ₁ PZ₂ : PolyZonotope 𝕋 n) :
    segments (nominalSet PZ₁) (nominalSet PZ₂) ⊆
      nominalSet (PZ₁.linComb PZ₂)
        + ((PolyZonotope.midpointResidual PZ₁.c PZ₂.c).construct
            + (PolyZonotope.halfDiffError PZ₁.c PZ₂.c).construct) := by
  rintro _ ⟨y₁, hy₁', y₂, hy₂', lam, ⟨hl0, hl1⟩, rfl⟩
  obtain ⟨a₁, β₁, ha₁, hβ₁, hy₁⟩ := PolyZonotope.mem_nominalSet_iff.mp hy₁'
  obtain ⟨a₂, β₂, ha₂, hβ₂, hy₂⟩ := PolyZonotope.mem_nominalSet_iff.mp hy₂'
  refine ⟨fun i => toReal ((PZ₁.linComb PZ₂).c i)
            + (∑ l, toReal ((PZ₁.linComb PZ₂).G i l)
                * Real.PolyZonotope.monomial (PZ₁.linComb PZ₂).E
                    (Fin.append (Fin.append a₁ a₂) (fun _ : Fin 1 => 2 * lam - 1)) l)
            + ∑ j, toReal ((PZ₁.linComb PZ₂).GI i j)
                * Fin.append (fun j => lam * β₁ j) (fun j => (1 - lam) * β₂ j) j,
          PolyZonotope.mem_nominalSet_iff.mpr
            ⟨Fin.append (Fin.append a₁ a₂) (fun _ : Fin 1 => 2 * lam - 1),
             Fin.append (fun j => lam * β₁ j) (fun j => (1 - lam) * β₂ j), ?_, ?_,
             fun _ => rfl⟩,
          _, ⟨_, PolyZonotope.aux_midpoint_mem_residual PZ₁.c PZ₂.c,
              _, PolyZonotope.aux_halfDiff_mem_error PZ₁.c PZ₂.c hl0 hl1, rfl⟩, ?_⟩
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
  · refine Fin.addCases ?_ ?_
    · intro j
      simpa using Real.PolyZonotope.abs_mul_le_one hl0 hl1 (hβ₁ j)
    · intro j
      simpa using Real.PolyZonotope.abs_mul_le_one (by linarith) (by linarith) (hβ₂ j)
  · funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hy₁ i, hy₂ i, PolyZonotope.aux_sum_univ_linComb_h,
      PolyZonotope.aux_sum_univ_linComb_q]
    simp only [PolyZonotope.linComb, Fin.sum_univ_add, Fin.sum_univ_one,
      Real.PolyZonotope.monomial_linCombE_fst, Real.PolyZonotope.monomial_linCombE_snd,
      Real.PolyZonotope.monomial_linCombE_last, Real.PolyZonotope.monomial_plusE_left,
      Real.PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right,
      PolyZonotope.aux_sum_mul, PolyZonotope.aux_sum_half,
      PolyZonotope.aux_sum_neg_half]
    ring

/-- The box absorbs the two incoming boxes and both centre roundings. -/
theorem PolyZonotope.aux_linComb_error (PZ₁ PZ₂ : PolyZonotope 𝕋 n) :
    segments PZ₁.err.construct PZ₂.err.construct
        + ((PolyZonotope.midpointResidual PZ₁.c PZ₂.c).construct
            + (PolyZonotope.halfDiffError PZ₁.c PZ₂.c).construct)
      ⊆ (PZ₁.linComb PZ₂).err.construct :=
  subset_trans
    (Set.add_subset_add (Interval.linComb_outer PZ₁.err PZ₂.err) (Interval.plus_outer _ _))
    (Interval.plus_outer _ _)

theorem PolyZonotope.linComb_outer (PZ₁ PZ₂ : PolyZonotope 𝕋 n) :
    segments PZ₁.construct PZ₂.construct ⊆ (PZ₁.linComb PZ₂).construct :=
  InflatedContSet.linComb_subset (PolyZonotope.aux_linComb_nominal PZ₁ PZ₂)
    (PolyZonotope.aux_linComb_error PZ₁ PZ₂)

end CORALean.Float
