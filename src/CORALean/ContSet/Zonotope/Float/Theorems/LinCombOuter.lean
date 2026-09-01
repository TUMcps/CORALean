import CORALean.ContSet.Zonotope.Float.Operations.API

/-!
# `Zonotope.linComb` contains every segment between the two zonotopes

`InflatedContSet.linComb_subset` reduces this to two obligations: the nominal
parts spill only by the two centre roundings, and the box absorbs that spill
along with the segment between the two incoming boxes.

The nominal obligation is the exact `linComb` argument — `λβ₁`, `(1-λ)β₂` and
`2λ-1` as the coefficients — with the centre and the sliding generator displaced.
Neither stored value is unfolded: they cancel against their own residuals, so
what remains is the same identity the exact proof closes with.

The count is therefore still `h₁ + h₂ + 1`, both roundings having gone into the
box.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem Zonotope.linComb_h (Z₁ Z₂ : Zonotope 𝕋 n) :
    (Z₁.linComb Z₂).h = Z₁.h + Z₂.h + 1 := rfl

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `linComb`'s generator count, stated through the
projection because that is the form the goal has and simp will not rewrite a
binder's type. -/
theorem Zonotope.aux_sum_univ_linComb {Z₁ Z₂ : Zonotope 𝕋 n}
    (f : Fin (Z₁.h + Z₂.h + 1) → ℝ) :
    ∑ j : Fin (Z₁.linComb Z₂).h, f j
      = ∑ j, f (Fin.castAdd 1 j) + ∑ j, f (Fin.natAdd (Z₁.h + Z₂.h) j) :=
  Fin.sum_univ_add f

/-- Scaling a coefficient by a weight in `[0,1]` keeps it a coefficient. -/
theorem aux_abs_mul_le_one {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb : |b| ≤ 1) :
    |a * b| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg ha0]
  nlinarith [abs_nonneg b]

/-- A non-negative shortfall stays inside the symmetric box its own bound spans,
whatever a coefficient in `[-1,1]` does with it. -/
theorem aux_mul_mem_symmetric {q R s : ℝ} (hq0 : 0 ≤ q) (hqR : q ≤ R)
    (hs0 : -1 ≤ s) (hs1 : s ≤ 1) : -R ≤ q * s ∧ q * s ≤ R :=
  ⟨by nlinarith, by nlinarith⟩

/-- The two directed midpoints bracket the exact one, halving being exact. -/
theorem Zonotope.aux_midpoint_mem_residual (a b : Vec 𝕋 n) :
    (fun i => (toReal (a i) + toReal (b i)) / 2 - toReal (Zonotope.midpoint a b i))
      ∈ (Zonotope.midpointResidual a b).construct :=
  Interval.sub_mem_residual fun i => by
    refine ⟨?_, ?_⟩
    · rw [toReal_half]
      have := addDown_le_add (a i) (b i)
      linarith
    · rw [toReal_half]
      have := add_le_addUp (a i) (b i)
      linarith

/-- The sliding generator rounds down, so its shortfall is non-negative and no
larger than the gap between the two directed halvings. -/
theorem Zonotope.aux_halfDiff_mem_error (a b : Vec 𝕋 n) {lam : ℝ}
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    (fun i => ((toReal (a i) - toReal (b i)) / 2 - toReal (Zonotope.halfDiff a b i))
        * (2 * lam - 1))
      ∈ (Zonotope.halfDiffError a b).construct := by
  intro i
  have hdown : toReal (Zonotope.halfDiff a b i) = toReal (subDown (a i) (b i)) / 2 :=
    toReal_half _
  have hq0 : 0 ≤ (toReal (a i) - toReal (b i)) / 2 - toReal (Zonotope.halfDiff a b i) := by
    rw [hdown]
    have := subDown_le_sub (a i) (b i)
    linarith
  have hqR : (toReal (a i) - toReal (b i)) / 2 - toReal (Zonotope.halfDiff a b i)
      ≤ toReal (subUp (half (subUp (a i) (b i))) (half (subDown (a i) (b i)))) := by
    have h1 := sub_le_subUp (half (subUp (a i) (b i))) (half (subDown (a i) (b i)))
    rw [toReal_half, toReal_half] at h1
    have h2 := sub_le_subUp (a i) (b i)
    rw [hdown]
    linarith
  obtain ⟨hlo, hhi⟩ := aux_mul_mem_symmetric hq0 hqR (by linarith : (-1:ℝ) ≤ 2 * lam - 1)
    (by linarith : 2 * lam - 1 ≤ 1)
  refine ⟨?_, hhi⟩
  show toReal (neg _) ≤ _
  rw [toReal_neg]
  exact hlo

set_option maxHeartbeats 400000 in
/-- The two generator blocks are exact, so the nominal part spills only by what
the centre and the sliding generator rounded. -/
theorem Zonotope.aux_linComb_nominal (Z₁ Z₂ : Zonotope 𝕋 n) :
    segments (nominalSet Z₁) (nominalSet Z₂) ⊆
      nominalSet (Z₁.linComb Z₂)
        + ((Zonotope.midpointResidual Z₁.c Z₂.c).construct
            + (Zonotope.halfDiffError Z₁.c Z₂.c).construct) := by
  rintro _ ⟨y₁, hy₁', y₂, hy₂', lam, ⟨hl0, hl1⟩, rfl⟩
  obtain ⟨β₁, hβ₁, hy₁⟩ := Zonotope.mem_nominalSet_iff.mp hy₁'
  obtain ⟨β₂, hβ₂, hy₂⟩ := Zonotope.mem_nominalSet_iff.mp hy₂'
  refine ⟨fun i => toReal ((Z₁.linComb Z₂).c i)
            + ∑ j, toReal ((Z₁.linComb Z₂).G i j)
                * Fin.append (Fin.append (fun j => lam * β₁ j) (fun j => (1 - lam) * β₂ j))
                    (fun _ : Fin 1 => 2 * lam - 1) j,
          Zonotope.mem_nominalSet_iff.mpr
            ⟨Fin.append (Fin.append (fun j => lam * β₁ j) (fun j => (1 - lam) * β₂ j))
              (fun _ : Fin 1 => 2 * lam - 1), ?_, fun _ => rfl⟩,
          _,
          ⟨_, Zonotope.aux_midpoint_mem_residual Z₁.c Z₂.c,
           _, Zonotope.aux_halfDiff_mem_error Z₁.c Z₂.c hl0 hl1, rfl⟩, ?_⟩
  · refine Fin.addCases ?_ ?_
    · refine Fin.addCases ?_ ?_
      · intro j
        simpa using aux_abs_mul_le_one hl0 hl1 (hβ₁ j)
      · intro j
        simpa using aux_abs_mul_le_one (by linarith) (by linarith) (hβ₂ j)
    · intro _
      simp only [Fin.append_right]
      rw [abs_le]
      constructor <;> linarith
  · funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hy₁ i, hy₂ i, Zonotope.aux_sum_univ_linComb]
    simp only [Zonotope.linComb, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      Fin.sum_univ_one]
    rw [Finset.sum_congr rfl (fun j _ => by ring : ∀ j ∈ Finset.univ,
        toReal (Z₁.G i j) * (lam * β₁ j) = lam * (toReal (Z₁.G i j) * β₁ j)),
      Finset.sum_congr rfl (fun j _ => by ring : ∀ j ∈ Finset.univ,
        toReal (Z₂.G i j) * ((1 - lam) * β₂ j) = (1 - lam) * (toReal (Z₂.G i j) * β₂ j)),
      ← Finset.mul_sum, ← Finset.mul_sum]
    ring

/-- The box absorbs the two incoming boxes and both centre roundings. -/
theorem Zonotope.aux_linComb_error (Z₁ Z₂ : Zonotope 𝕋 n) :
    segments Z₁.E.construct Z₂.E.construct
        + ((Zonotope.midpointResidual Z₁.c Z₂.c).construct
            + (Zonotope.halfDiffError Z₁.c Z₂.c).construct)
      ⊆ (Z₁.linComb Z₂).E.construct :=
  subset_trans
    (Set.add_subset_add (Interval.linComb_outer Z₁.E Z₂.E) (Interval.plus_outer _ _))
    (Interval.plus_outer _ _)

theorem Zonotope.linComb_outer (Z₁ Z₂ : Zonotope 𝕋 n) :
    segments Z₁.construct Z₂.construct ⊆ (Z₁.linComb Z₂).construct :=
  InflatedContSet.linComb_subset (Zonotope.aux_linComb_nominal Z₁ Z₂)
    (Zonotope.aux_linComb_error Z₁ Z₂)

end CORALean.Float
