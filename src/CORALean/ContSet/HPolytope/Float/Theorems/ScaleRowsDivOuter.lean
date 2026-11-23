module

public import CORALean.ContSet.HPolytope.Float.Operations.ScaleRowsDiv
public import CORALean.ContSet.HPolytope.Float.Theorems.MemSetRhsNominal
public import CORALean.ContSet.HPolytope.Float.Theorems.Basic
public import CORALean.ContSet.HPolytope.Float.Theorems.MemToSet
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners

@[expose] public section

/-!
# `HPolytope.scaleRowsDiv` keeps every point of the polytope inside the domain

As for `scaleRows_outer`, with the quotient in place of the product: the stored row `ṽ` is `v / d`
rounded down, `ṽᵀ x = (vᵀ x) / d - (v / d - ṽ)ᵀ x`, the first term at most `b / d` for an inequality
(the divisor positive) and exactly `bₑ / d` for an equality, the second between `step_divDevLo` and
`step_divDevHi`.

## Inputs
* `P` – H-polytope
* `dA` – divisors indexed by `Fin P.m`
* `dE` – divisors indexed by `Fin P.me`
* `dom` – domain interval

## Hypotheses
* `hP` – `P.IsErrFree`
* `hA` – every inequality divisor `dA i` is positive
* `hE` – every equality divisor `dE i` is certified negative or positive

## Conclusion
* inside `dom`, the divided polytope contains the error-free one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       22-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The signed quotient is bracketed: a certified negative divisor is negated with the numerator,
else it is positive. -/
private theorem HPolytope.aux_sdiv_between (a d : 𝕋)
    (hd : ltStrict d zero = true ∨ 0 < toReal d) : -- --- CONCL ---
    toReal (HPolytope.step_sdivDown a d) ≤ toReal a / toReal d
      ∧ toReal a / toReal d ≤ toReal (HPolytope.step_sdivUp a d) := by -- --- PROOF ---
  by_cases h : ltStrict d zero = true
  · have hneg : toReal d < 0 := by
      have := toReal_lt_of_ltStrict h
      rwa [toReal_zero] at this
    have hpos : 0 < toReal (neg d) := by rw [toReal_neg]; linarith
    have e : toReal a / toReal d = toReal (neg a) / toReal (neg d) := by
      rw [toReal_neg, toReal_neg, neg_div_neg_eq]
    simp only [HPolytope.step_sdivDown, HPolytope.step_sdivUp, h, if_true]
    rw [e]
    exact ⟨divDown_le_div _ _ hpos, div_le_divUp _ _ hpos⟩
  · have hpos : 0 < toReal d := hd.resolve_left h
    simp only [HPolytope.step_sdivDown, HPolytope.step_sdivUp, h, Bool.false_eq_true, if_false]
    exact ⟨divDown_le_div _ _ hpos, div_le_divUp _ _ hpos⟩

/-- What rounding a divided row costs, bounded over a domain. -/
private theorem HPolytope.aux_divDev_between (v : Vec 𝕋 n) (d : 𝕋)
    (hd : ltStrict d zero = true ∨ 0 < toReal d) (dom : Interval (Vec 𝕋 n))
    {x : Vec ℝ n} (hx : x ∈ dom.toSet) : -- --- CONCL ---
    toReal (HPolytope.step_divDevLo v d dom)
        ≤ ∑ j, (toReal (v j) / toReal d - toReal (HPolytope.step_sdivDown (v j) d)) * x j
      ∧ ∑ j, (toReal (v j) / toReal d - toReal (HPolytope.step_sdivDown (v j) d)) * x j
        ≤ toReal (HPolytope.step_divDevHi v d dom) := by -- --- PROOF ---
  have hdev : ∀ j, toReal (subDown (HPolytope.step_sdivDown (v j) d)
          (HPolytope.step_sdivDown (v j) d))
        ≤ toReal (v j) / toReal d - toReal (HPolytope.step_sdivDown (v j) d)
      ∧ toReal (v j) / toReal d - toReal (HPolytope.step_sdivDown (v j) d)
        ≤ toReal (subUp (HPolytope.step_sdivUp (v j) d) (HPolytope.step_sdivDown (v j) d)) := by
    intro j
    have h3 := (HPolytope.aux_sdiv_between (v j) d hd).1
    have h4 := (HPolytope.aux_sdiv_between (v j) d hd).2
    have h5 := subDown_le_sub (HPolytope.step_sdivDown (v j) d) (HPolytope.step_sdivDown (v j) d)
    have h6 := sub_le_subUp (HPolytope.step_sdivUp (v j) d) (HPolytope.step_sdivDown (v j) d)
    constructor <;> linarith
  have hxj : ∀ j, toReal (dom.inf j) ≤ x j ∧ x j ≤ toReal (dom.sup j) := hx
  have hprod := fun j => Interval.mul_between_corners (hdev j).1 (hdev j).2 (hxj j).1 (hxj j).2
  exact ⟨le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun j _ => (hprod j).1),
    le_trans (Finset.sum_le_sum fun j _ => (hprod j).2) (sum_le_sumUp _)⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- Inside `dom`, the divided polytope contains the error-free one. -/
theorem HPolytope.scaleRowsDiv_outer (P : HPolytope 𝕋 (Vec 𝕋 n)) (hP : P.IsErrFree)
    (dA : Fin P.m → 𝕋) (dE : Fin P.me → 𝕋)
    (hA : ∀ i, 0 < toReal (dA i)) (hE : ∀ i, ltStrict (dE i) zero = true ∨ 0 < toReal (dE i))
    (dom : Interval (Vec 𝕋 n)) : -- --- CONCL ---
    P.toSet ∩ dom.toSet ⊆
      (P.scaleRowsDiv dA dE dom).toSet ∩ dom.toSet := by -- --- PROOF ---
  rintro x ⟨hP', hd⟩
  refine ⟨?_, hd⟩
  obtain ⟨h1, h2⟩ := (HPolytope.mem_toSet_iff hP).mp hP'
  have hdA : ∀ i, ltStrict (dA i) zero = true ∨ 0 < toReal (dA i) := fun i => Or.inr (hA i)
  -- what rounding a row costs at `x`
  let dev : ∀ {k : ℕ}, Mat 𝕋 k n → (Fin k → 𝕋) → Fin k → ℝ := fun M s i =>
    ∑ j, (toReal (M i j) / toReal (s i) - toReal (HPolytope.step_sdivDown (M i j) (s i))) * x j
  -- the stored row is the divided row less the deviation
  have hsplit : ∀ {k : ℕ} (M : Mat 𝕋 k n) (s : Fin k → 𝕋) (i : Fin k),
      (toRealMat (fun i j => HPolytope.step_sdivDown (M i j) (s i)) *ᵥ x) i
        = (toRealMat M *ᵥ x) i / toReal (s i) - dev M s i := by
    intro k M s i
    simp only [dev, mulVec, dotProduct, toRealMat, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- the exact bound of a divided row at `x`, and its two ends
  have hends : ∀ {k : ℕ} (M : Mat 𝕋 k n) (c s : Fin k → 𝕋)
      (_ : ∀ i, ltStrict (s i) zero = true ∨ 0 < toReal (s i)) (i : Fin k),
      toReal (subDown (HPolytope.step_sdivDown (c i) (s i))
          (HPolytope.step_divDevHi (M i) (s i) dom)) ≤ toReal (c i) / toReal (s i) - dev M s i
        ∧ toReal (c i) / toReal (s i) - dev M s i
          ≤ toReal (subUp (HPolytope.step_sdivUp (c i) (s i))
            (HPolytope.step_divDevLo (M i) (s i) dom)) := by
    intro k M c s hs i
    obtain ⟨hlo, hhi⟩ := HPolytope.aux_divDev_between (M i) (s i) (hs i) dom hd
    have h1 := (HPolytope.aux_sdiv_between (c i) (s i) (hs i)).1
    have h2 := subDown_le_sub (HPolytope.step_sdivDown (c i) (s i))
      (HPolytope.step_divDevHi (M i) (s i) dom)
    have h3 := (HPolytope.aux_sdiv_between (c i) (s i) (hs i)).2
    have h4 := sub_le_subUp (HPolytope.step_sdivUp (c i) (s i))
      (HPolytope.step_divDevLo (M i) (s i) dom)
    simp only [dev]
    constructor <;> linarith
  refine (HPolytope.mem_nominal_of_origin rfl).mpr (HPolytope.mem_setRhs_nominal _ _ _
    (fun i => hends P.A P.b dA hdA i) (fun i => hends P.Ae P.be dE hE i) (fun i => ?_)
    (fun i => ?_))
  · -- an inequality row: the divided row at most the divided bound
    have hscaled := div_le_div_of_nonneg_right (h1 i) (hA i).le
    show (toRealMat (fun i j => HPolytope.step_sdivDown (P.A i j) (dA i)) *ᵥ x) i ≤ _ +
      |toReal (zero : 𝕋)|
    rw [hsplit P.A dA i, toReal_zero, abs_zero, add_zero]
    linarith
  · -- an equality row: the divided row is the divided bound
    show |(toRealMat (fun i j => HPolytope.step_sdivDown (P.Ae i j) (dE i)) *ᵥ x) i - _| ≤
      |toReal (zero : 𝕋)|
    rw [hsplit P.Ae dE i, h2 i, toReal_zero, abs_zero, abs_nonpos_iff]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
