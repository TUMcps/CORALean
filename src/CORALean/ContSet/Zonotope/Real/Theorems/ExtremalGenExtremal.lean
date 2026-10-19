module

public import CORALean.ContSet.Zonotope.Real.Operations.ExtremalGen
public import CORALean.ContSet.Zonotope.Real.Theorems.InterHyperplaneIff

@[expose] public section

/-!
# `u ± g` are the extremal points of a zonotope along `s`

[1, Sec. 5.1], from the proof of [1, Prop. 2]: the extremal points of `Z = (u, ⟨v₁, …, v_m⟩)`
in the direction `s` are `u - g` and `u + g`, `g = Σⱼ sign(s·vⱼ)vⱼ`. Both are points of `Z`
(coefficients `∓sign(s·vⱼ)`), and `(u ± g)·s = u·s ± Σⱼ |vⱼ·s|`, the bounds every point of
`Z` keeps along `s` (`Zonotope.inter_hyperplane_iff`).

## References

* [1] A. Girard, C. Le Guernic and O. Maler. "Efficient Computation of Reachable Sets of
      Linear Time-Invariant Systems with Inputs". In Hybrid Systems: Computation and
      Control (HSCC), LNCS 3927, Springer, 2006, pp. 257-271.
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

/-- [1, Sec. 5.1]: `u + g` maximizes and `u - g` minimizes `x·s` over `Z`. -/
theorem Zonotope.extremalGen_extremal (Z : Zonotope (Vec ℝ n)) (s : Vec ℝ n) : -- --- CONCL ---
    (Z.c + Z.extremalGen s ∈ Z.construct ∧
        ∀ x ∈ Z.construct, x ⬝ᵥ s ≤ (Z.c + Z.extremalGen s) ⬝ᵥ s) ∧
      Z.c - Z.extremalGen s ∈ Z.construct ∧
        ∀ x ∈ Z.construct, (Z.c - Z.extremalGen s) ⬝ᵥ s ≤ x ⬝ᵥ s := by -- --- PROOF ---
  -- a sign is at most one in absolute value, and a sign times its argument is the modulus
  have hsg : ∀ r : ℝ, |Real.sign r| ≤ 1 := fun r => by
    rcases Real.sign_apply_eq r with h | h | h <;> simp [h]
  have hsm : ∀ r : ℝ, Real.sign r * r = |r| := fun r => by
    rcases lt_trichotomy r 0 with h | h | h
    · rw [Real.sign_of_neg h, neg_one_mul, abs_of_neg h]
    · rw [h, Real.sign_zero, zero_mul, abs_zero]
    · rw [Real.sign_of_pos h, one_mul, abs_of_pos h]
  -- along `s`, the offset `g` reaches `Σⱼ |vⱼ·s|`
  have hdot : Z.extremalGen s ⬝ᵥ s = ∑ j, |Z.G j ⬝ᵥ s| := by
    simp only [Zonotope.extremalGen, sum_dotProduct, smul_dotProduct, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [dotProduct_comm s, hsm]
  -- every point of `Z` stays within `Σⱼ |vⱼ·s|` of `u·s`
  have hb : ∀ x ∈ Z.construct, Z.c ⬝ᵥ s - ∑ j, |Z.G j ⬝ᵥ s| ≤ x ⬝ᵥ s ∧
      x ⬝ᵥ s ≤ Z.c ⬝ᵥ s + ∑ j, |Z.G j ⬝ᵥ s| := fun x hx =>
    (Z.inter_hyperplane_iff s (x ⬝ᵥ s)).1 ⟨x, hx, rfl⟩
  refine ⟨⟨⟨fun j => Real.sign (s ⬝ᵥ Z.G j), fun j => hsg _, rfl⟩, fun x hx => ?_⟩,
    ⟨fun j => -Real.sign (s ⬝ᵥ Z.G j), fun j => by simpa using hsg _, ?_⟩, fun x hx => ?_⟩
  · rw [add_dotProduct, hdot]; exact (hb x hx).2
  · simp only [Zonotope.extremalGen, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]
  · rw [sub_dotProduct, hdot]; exact (hb x hx).1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
