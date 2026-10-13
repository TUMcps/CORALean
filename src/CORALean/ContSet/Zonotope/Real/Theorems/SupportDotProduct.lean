module

public import CORALean.ContSet.Zonotope.Real.Operations.SupportRadius
public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import Mathlib.Data.Real.Sign
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The extent of a zonotope in a direction is attained

[1, Def. 7]: the hyperplanes `cᵀx = r` and `cᵀx = q` are tangent to `Z = p ⊕ H Bᵐ` when `r = max_{x
∈ Z} cᵀx` and `q = min_{x ∈ Z} cᵀx`, and these are `cᵀp ± ‖Hᵀc‖₁`: each generator contributes `β_j
cᵀG_j` with `|β_j| ≤ 1`, at most `|cᵀG_j|`, and the coefficient `±sgn (cᵀG_j)` reaches it. Both are
stated as `IsGreatest` and `IsLeast` of the image, so they are attained.

## References

* [1] J. M. Bravo, T. Alamo and E. F. Camacho. "Bounded error identification of systems with
      time-varying parameters". IEEE Transactions on Automatic Control, 51(7):1144-1150, 2006.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.support_dotProduct (Z : Zonotope (Vec ℝ n)) (c : Vec ℝ n) :
    IsGreatest ((fun x => c ⬝ᵥ x) '' Z.construct) (c ⬝ᵥ Z.c + Z.supportRadius c) ∧
    IsLeast ((fun x => c ⬝ᵥ x) '' Z.construct) (c ⬝ᵥ Z.c - Z.supportRadius c) := by -- --- PROOF ---
  -- the value of `cᵀx` at the coefficients `β`
  have hval : ∀ β : Fin Z.h → ℝ, c ⬝ᵥ (Z.c + ∑ j, β j • Z.G j) =
      c ⬝ᵥ Z.c + ∑ j, β j * (c ⬝ᵥ Z.G j) := by
    intro β
    rw [dotProduct_add, dotProduct_sum]
    simp only [dotProduct_smul, smul_eq_mul]
  -- coefficients of absolute value at most one move `cᵀx` by at most the radius
  have hle : ∀ β : Fin Z.h → ℝ, (∀ j, |β j| ≤ 1) →
      |∑ j, β j * (c ⬝ᵥ Z.G j)| ≤ Z.supportRadius c := by
    intro β hβ
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_right (hβ j) (abs_nonneg (c ⬝ᵥ Z.G j))
  -- the sign coefficients reach `±` the radius
  have hsign : ∀ j, Real.sign (c ⬝ᵥ Z.G j) * (c ⬝ᵥ Z.G j) = |c ⬝ᵥ Z.G j| := fun j => by
    rcases lt_trichotomy (c ⬝ᵥ Z.G j) 0 with h | h | h
    · rw [Real.sign_of_neg h, neg_one_mul, abs_of_neg h]
    · rw [h, Real.sign_zero, zero_mul, abs_zero]
    · rw [Real.sign_of_pos h, one_mul, abs_of_pos h]
  have hsb : ∀ j, |Real.sign (c ⬝ᵥ Z.G j)| ≤ 1 := fun j => by
    rcases Real.sign_apply_eq (c ⬝ᵥ Z.G j) with h | h | h <;> simp [h]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- the maximum is attained at the sign coefficients
    refine ⟨Z.c + ∑ j, Real.sign (c ⬝ᵥ Z.G j) • Z.G j, ⟨_, hsb, rfl⟩, ?_⟩
    simp only [hval, hsign, Zonotope.supportRadius]
  · -- and nothing is larger
    rintro _ ⟨x, ⟨β, hβ, rfl⟩, rfl⟩
    beta_reduce
    rw [hval]
    linarith [(abs_le.mp (hle β hβ)).2]
  · -- the minimum is attained at the negated sign coefficients
    refine ⟨Z.c + ∑ j, (-Real.sign (c ⬝ᵥ Z.G j)) • Z.G j,
      ⟨_, fun j => by simpa using hsb j, rfl⟩, ?_⟩
    simp only [hval, neg_mul, hsign, Finset.sum_neg_distrib, Zonotope.supportRadius]
    ring
  · -- and nothing is smaller
    rintro _ ⟨x, ⟨β, hβ, rfl⟩, rfl⟩
    beta_reduce
    rw [hval]
    linarith [(abs_le.mp (hle β hβ)).1]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
