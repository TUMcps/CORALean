module

public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.PolyZonotope.Float.Operations.LinComb
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.LinCombOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.Zonotope.Real.Theorems.LinCombOuter

@[expose] public section

/-!
# `PolyZonotope.linComb` at named factors

The nominal half of `linComb_outer`, with the factors said: the segment between
the points at `(a₁, β₁)` and `(a₂, β₂)` lies, up to what rounded, on the nominal
point of `linComb` at the factor vector `[a₁; a₂; 2λ-1]`.

Naming the dependent factors is what a constrained set needs: its constraints
read those factors, so `ConPolyZono.linComb` can only check them if it knows
which ones the segment point uses. The independent coefficients stay
existential, nothing reading them but the box `[-1,1]`.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope
* `a₁` – factor values of the first set
* `a₂` – factor values of the second set
* `β₁` – independent values of the first set
* `β₂` – independent values of the second set
* `lam` – convex weight

## Hypotheses
* `hβ₁` – first independent values are at most one
* `hβ₂` – second independent values are at most one
* `hl0` – weight is nonnegative
* `hl1` – weight is at most one

## Conclusion
* the weighted point is attained by suitable independent values
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   02-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `linComb`'s dependent generator count, stated through
the projection because that is the form the goal has and simp will not rewrite a
binder's type. Only the outermost split needs it. -/
private theorem PolyZonotope.aux_sum_univ_linComb_h {pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)}
    (f : Fin (pZ₁.h + pZ₂.h + (pZ₁.h + pZ₂.h + 1)) → ℝ) :
    ∑ l : Fin (pZ₁.linComb pZ₂).h, f l
      = ∑ l, f (Fin.castAdd (pZ₁.h + pZ₂.h + 1) l)
        + ∑ l, f (Fin.natAdd (pZ₁.h + pZ₂.h) l) :=
  Fin.sum_univ_add f

omit [SoundFloatArithmetic 𝕋] in
/-- The independent count read off the projection, which is the only thing the
goal and the pairing lemmas disagree about: the block is not split here, the
pairing crossing the two halves rather than closing on each. -/
private theorem PolyZonotope.aux_sum_univ_linComb_q {pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)}
    (f : Fin (pZ₁.q + pZ₂.q) → ℝ) :
    ∑ j : Fin (pZ₁.linComb pZ₂).q, f j = ∑ j : Fin (pZ₁.q + pZ₂.q), f j := rfl

/-- The independent block `linComb` would store if nothing rounded. -/
private noncomputable def PolyZonotope.aux_linCombGIReal (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n))
    (i : Fin n) :
    Fin (pZ₁.q + pZ₂.q) → ℝ :=
  Fin.append
    (Real.Zonotope.pairSum (fun j => toReal (pZ₁.GI j i)) (fun j => toReal (pZ₂.GI j i)))
    (Real.Zonotope.pairDiff (fun j => toReal (pZ₁.GI j i)) (fun j => toReal (pZ₂.GI j i)))

/-- What the stored independent generators are wrong by, entrywise, which is
what `linCombGIDiff` records. -/
private theorem PolyZonotope.aux_linCombGI_error (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) (i : Fin n)
    (j : Fin (pZ₁.q + pZ₂.q)) : -- --- CONCL ---
    |PolyZonotope.aux_linCombGIReal pZ₁ pZ₂ i j
        - toReal (PolyZonotope.linCombGI addDown subDown pZ₁ pZ₂ i j)|
      ≤ toReal (PolyZonotope.linCombGIDiff pZ₁ pZ₂ i j) := by -- --- PROOF ---
  have hbr : ∀ j : Fin (pZ₁.q + pZ₂.q),
      toReal (PolyZonotope.linCombGI addDown subDown pZ₁ pZ₂ i j)
          ≤ PolyZonotope.aux_linCombGIReal pZ₁ pZ₂ i j
        ∧ PolyZonotope.aux_linCombGIReal pZ₁ pZ₂ i j
          ≤ toReal (PolyZonotope.linCombGI addUp subUp pZ₁ pZ₂ i j) := by
    simp only [PolyZonotope.linCombGI, PolyZonotope.aux_linCombGIReal]
    refine Fin.addCases ?_ ?_
    · intro k
      simp only [Fin.append_left]
      exact Zonotope.pairSum_bracket (fun j => pZ₁.GI j i) (fun j => pZ₂.GI j i) k
    · intro k
      simp only [Fin.append_right]
      exact Zonotope.pairDiff_bracket (fun j => pZ₁.GI j i) (fun j => pZ₂.GI j i) k
  -- the gap between the two directed spellings is what bounds the error
  obtain ⟨hlo, hhi⟩ := hbr j
  have hgap := sub_le_subUp (PolyZonotope.linCombGI addUp subUp pZ₁ pZ₂ i j)
    (PolyZonotope.linCombGI addDown subDown pZ₁ pZ₂ i j)
  simp only [PolyZonotope.linCombGIDiff]
  rw [abs_le]
  constructor <;> linarith

/-- One row of the exact independent generators against the coefficients the
segment supplies: the pairing gives back the two sets' own sums. -/
private theorem PolyZonotope.aux_linCombGI_row (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) (i : Fin n)
    (β₁ : Fin pZ₁.q → ℝ) (β₂ : Fin pZ₂.q → ℝ) (lam : ℝ) : -- --- CONCL ---
    (∑ j, PolyZonotope.aux_linCombGIReal pZ₁ pZ₂ i j
        * Fin.append (Real.Zonotope.pairCoeffSum β₁ β₂ lam)
            (Real.Zonotope.pairCoeffDiff β₁ β₂ lam) j)
      = lam * (∑ j, toReal (pZ₁.GI j i) * β₁ j)
        + (1 - lam) * ∑ j, toReal (pZ₂.GI j i) * β₂ j := by -- --- PROOF ---
  rw [Fin.sum_univ_add]
  simp only [PolyZonotope.aux_linCombGIReal, Fin.append_left, Fin.append_right]
  exact Zonotope.sum_pair_mul (fun j => toReal (pZ₁.GI j i))
    (fun j => toReal (pZ₂.GI j i)) β₁ β₂ lam

/-- The two directed midpoints bracket the exact one, halving being exact. -/
private theorem PolyZonotope.aux_midpoint_mem_residual (a b : Vec 𝕋 n) :
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
private theorem PolyZonotope.aux_mul_mem_symmetric {q R s : ℝ} (hq0 : 0 ≤ q) (hqR : q ≤ R)
    (hs0 : -1 ≤ s) (hs1 : s ≤ 1) : -R ≤ q * s ∧ q * s ≤ R :=
  ⟨by nlinarith, by nlinarith⟩

/-- The sliding generator rounds down, so its shortfall is non-negative and no
larger than the gap between the two directed halvings; the fresh factor spreads
it over `[-1,1]`. -/
private theorem PolyZonotope.aux_halfDiff_mem_error (a b : Vec 𝕋 n) {lam : ℝ}
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) : -- --- CONCL ---
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
unfolding it, so simp fires on the whole sum and never on the stored center,
which has to stay folded to cancel against its residual. `aux_sum_mul` strips a
coefficient's common factor first, which is why the two halving lemmas are
needed only in their bare form. -/

private theorem PolyZonotope.aux_sum_mul {k : ℕ} (t : ℝ) (g : Fin k → 𝕋) (b : Fin k → ℝ) :
    ∑ j, toReal (g j) * (t * b j) = t * ∑ j, toReal (g j) * b j := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem PolyZonotope.aux_sum_half {k : ℕ} (g : Fin k → 𝕋) (m : Fin k → ℝ) :
    ∑ l, toReal (half (g l)) * m l = 1 / 2 * ∑ l, toReal (g l) * m l := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [toReal_half]; ring

/-- The same at the negated block, which is the only place a sign is stored. -/
private theorem PolyZonotope.aux_sum_neg_half {k : ℕ} (g : Fin k → 𝕋) (m : Fin k → ℝ) :
    ∑ l, toReal (neg (half (g l))) * m l = -(1 / 2) * ∑ l, toReal (g l) * m l := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [toReal_neg, toReal_half]; ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.linComb_nominal_at (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) {a₁ : Fin pZ₁.p → ℝ}
    {a₂ : Fin pZ₂.p → ℝ} {β₁ : Fin pZ₁.q → ℝ} {β₂ : Fin pZ₂.q → ℝ} {lam : ℝ}
    (hβ₁ : ∀ j, |β₁ j| ≤ 1) (hβ₂ : ∀ j, |β₂ j| ≤ 1) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) : -- --- CONCL ---
    ∃ β : Fin (pZ₁.linComb pZ₂).q → ℝ, (∀ j, |β j| ≤ 1) ∧
      lam • (fun i => toReal (pZ₁.c i)
          + (∑ l, toReal (pZ₁.G l i) * Real.PolyZonotope.monomial pZ₁.E a₁ l)
          + ∑ j, toReal (pZ₁.GI j i) * β₁ j)
        + (1 - lam) • (fun i => toReal (pZ₂.c i)
          + (∑ l, toReal (pZ₂.G l i) * Real.PolyZonotope.monomial pZ₂.E a₂ l)
          + ∑ j, toReal (pZ₂.GI j i) * β₂ j)
      ∈ ({fun i => toReal ((pZ₁.linComb pZ₂).c i)
            + (∑ l, toReal ((pZ₁.linComb pZ₂).G l i)
                * Real.PolyZonotope.monomial (pZ₁.linComb pZ₂).E
                    (Fin.append (Fin.append a₁ a₂) (fun _ : Fin 1 => 2 * lam - 1)) l)
            + ∑ j, toReal ((pZ₁.linComb pZ₂).GI j i) * β j} : Set (Vec ℝ n))
        + ((PolyZonotope.midpointResidual pZ₁.c pZ₂.c).construct
            + ((PolyZonotope.halfDiffError pZ₁.c pZ₂.c).construct
                + (Zonotope.generatorError
                    (PolyZonotope.linCombGIDiff pZ₁ pZ₂)).construct)) := by -- --- PROOF ---
  have hcf : ∀ j : Fin (pZ₁.q + pZ₂.q),
      |Fin.append (Real.Zonotope.pairCoeffSum β₁ β₂ lam)
        (Real.Zonotope.pairCoeffDiff β₁ β₂ lam) j| ≤ 1 := by
    refine Fin.addCases ?_ ?_
    · intro j
      simpa using Real.Zonotope.abs_pairCoeffSum_le_one hβ₁ hβ₂ hl0 hl1 j
    · intro j
      simpa using Real.Zonotope.abs_pairCoeffDiff_le_one hβ₁ hβ₂ hl0 hl1 j
  -- the independent coefficients: the exact layer's pairing of the two blocks
  refine ⟨Fin.append (Real.Zonotope.pairCoeffSum β₁ β₂ lam)
            (Real.Zonotope.pairCoeffDiff β₁ β₂ lam), hcf, _, rfl,
          _, ⟨_, PolyZonotope.aux_midpoint_mem_residual pZ₁.c pZ₂.c,
              _, ⟨_, PolyZonotope.aux_halfDiff_mem_error pZ₁.c pZ₂.c hl0 hl1,
                  _, Zonotope.mem_generatorError
                       (fun i j => PolyZonotope.aux_linCombGI_error pZ₁ pZ₂ i j) hcf,
                  rfl⟩, rfl⟩, ?_⟩
  funext i
  -- the stored independent generators and their shortfalls recombine
  have hGI : (∑ j : Fin (pZ₁.q + pZ₂.q),
        toReal (PolyZonotope.linCombGI addDown subDown pZ₁ pZ₂ i j)
          * Fin.append (Real.Zonotope.pairCoeffSum β₁ β₂ lam)
              (Real.Zonotope.pairCoeffDiff β₁ β₂ lam) j)
      + (∑ j, (PolyZonotope.aux_linCombGIReal pZ₁ pZ₂ i j
            - toReal (PolyZonotope.linCombGI addDown subDown pZ₁ pZ₂ i j))
          * Fin.append (Real.Zonotope.pairCoeffSum β₁ β₂ lam)
              (Real.Zonotope.pairCoeffDiff β₁ β₂ lam) j)
      = ∑ j, PolyZonotope.aux_linCombGIReal pZ₁ pZ₂ i j
          * Fin.append (Real.Zonotope.pairCoeffSum β₁ β₂ lam)
              (Real.Zonotope.pairCoeffDiff β₁ β₂ lam) j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [PolyZonotope.aux_linCombGI_row pZ₁ pZ₂ i β₁ β₂ lam] at hGI
  -- split as the goal is split, or the two block sums are different atoms
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right] at hGI
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [PolyZonotope.aux_sum_univ_linComb_h, PolyZonotope.aux_sum_univ_linComb_q]
  simp only [PolyZonotope.linComb, Fin.sum_univ_add, Fin.sum_univ_one,
    Real.PolyZonotope.monomial_linCombE_fst, Real.PolyZonotope.monomial_linCombE_snd,
    Real.PolyZonotope.monomial_linCombE_last, Real.PolyZonotope.monomial_plusE_left,
    Real.PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right,
    PolyZonotope.aux_sum_mul, PolyZonotope.aux_sum_half,
    PolyZonotope.aux_sum_neg_half]
  linarith [hGI]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
