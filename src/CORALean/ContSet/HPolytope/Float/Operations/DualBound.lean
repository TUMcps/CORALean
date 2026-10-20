module

public import CORALean.ContSet.HPolytope.Float.Theorems.RowsOfMemConstruct
public import CORALean.Global.Float.FloatBound

@[expose] public section

/-!
# Where a float halfspace description's own bounds come from

Weak duality again, at this layer's row structure. An equality row is read as the two inequalities
`Ae x ≤ beU` and `-Ae x ≤ beLN` (the right-hand side `be` with the error box folded in), so a dual
solution is three nonnegative vectors, and the error box is already in `bU`, `beU` and `beLN`. The
value is `dotUp`, rounded away from the set. Dual feasibility is stated over ℝ and is the caller's
to discharge: a float dual solution does not reproduce `c` exactly, and forcing it would make the
certificate unusable. The gap is paid by `addDir` instead: bound `c - yᵀA` over any enclosure in
hand and add the two, keeping the rounding where it can be measured.

## Inputs
* `P` – H-polytope
* `c` – center of length `n →ₗ[ℝ] ℝ`
* `y` – vector of length `P.m`
* `zu` – vector of length `P.me`
* `zl` – vector of length `P.me`

## Hypotheses
* `hy` – the entries of `y` are nonnegative
* `hzu` – the entries of `zu` are nonnegative
* `hzl` – the entries of `zl` are nonnegative
* `hc` – `c` is the dual combination of the rows with weights `y`, `zu`, `zl`

## Output
* where a float halfspace description's own bounds come from
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.boundOfDual (P : HPolytope 𝕋 (Vec 𝕋 n)) {c : Vec ℝ n →ₗ[ℝ] ℝ}
    (y : Vec 𝕋 P.m) (zu zl : Vec 𝕋 P.me)
    (hy : ∀ i, 0 ≤ toReal (y i)) (hzu : ∀ i, 0 ≤ toReal (zu i))
    (hzl : ∀ i, 0 ≤ toReal (zl i))
    (hc : ∀ x : Vec ℝ n, c x =
      (∑ i, toReal (y i) * (toRealMat P.A *ᵥ x) i)
        + (∑ i, toReal (zu i) * (toRealMat P.Ae *ᵥ x) i)
        - ∑ i, toReal (zl i) * (toRealMat P.Ae *ᵥ x) i) :
    FloatBound 𝕋 P.construct c where
  val := addUp (dotUp y P.bU) (addUp (dotUp zu P.beU) (dotUp zl P.beLN))
  -- weak duality: every dual weight is nonnegative, so each term is capped by its own row
  le x hx := by
    obtain ⟨hle, heq⟩ := HPolytope.rows_of_mem_construct hx
    have h1 : (∑ i, toReal (y i) * (toRealMat P.A *ᵥ x) i) ≤ toReal (dotUp y P.bU) :=
      le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hle i) (hy i))
        (le_dotUp _ _)
    have h2 : (∑ i, toReal (zu i) * (toRealMat P.Ae *ᵥ x) i) ≤ toReal (dotUp zu P.beU) :=
      le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (heq i).1 (hzu i))
        (le_dotUp _ _)
    have h3 : (∑ i, toReal (zl i) * (-(toRealMat P.Ae *ᵥ x) i)) ≤ toReal (dotUp zl P.beLN) :=
      le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (heq i).2 (hzl i))
        (le_dotUp _ _)
    -- the negated sum against its own negation, joined only by `Finset.sum_add_distrib`
    have hcancel : (∑ i, toReal (zl i) * (-(toRealMat P.Ae *ᵥ x) i))
        + ∑ i, toReal (zl i) * (toRealMat P.Ae *ᵥ x) i = 0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun i _ => by ring
    have hround := add_le_addUp (dotUp y P.bU) (addUp (dotUp zu P.beU) (dotUp zl P.beLN))
    have hround' := add_le_addUp (dotUp zu P.beU) (dotUp zl P.beLN)
    rw [hc x]
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
