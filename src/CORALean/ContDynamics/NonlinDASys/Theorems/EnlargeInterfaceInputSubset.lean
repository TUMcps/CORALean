import CORALean.ContDynamics.NonlinDASys.Operations.EnlargeInterfaceInput
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff

/-!
# The enlarged interface input holds the interface part of the input set

[1, Eq. 14] enlarges the input set `U` of a subsystem to `Û`, and [1, Alg. 2] then checks the
other subsystems' reachable sets against `Λ Û`, the interface coordinates. For `λ_U ≥ 1`,
`Λ` a projection (`Λ Λ = Λ`, as a 0/1 diagonal matrix is) and `ĉ` the centre of `U`, the
interface part of `Û` holds that of `U`: `Λ U ⊆ Λ Û`, since `Λ ((λ_U - 1) Λ + I) = λ_U Λ` scales
`Λ (U ⊕ (-ĉ))` by `λ_U ≥ 1` and a zonotope is centrally symmetric about `ĉ`.

`U ⊆ Û` itself is not claimed: `Û` scales the interface coordinates only, which breaks any
correlation of `U` between them and the others.

## References

* [1] M. Althoff. "Formal and Compositional Analysis of Power Systems using Reachable Sets".
      IEEE Transactions on Power Systems, 29(5):2270-2280, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix Pointwise

variable {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 14]: `Λ U ⊆ Λ Û` for `λ_U ≥ 1`, `Λ Λ = Λ` and `ĉ` the centre of `U`. -/
theorem NonlinDASys.image_subset_enlargeInterfaceInput {lamU : ℝ} (hlam : 1 ≤ lamU)
    {Λ : Mat ℝ m m} (hΛ : Λ * Λ = Λ) (U : Zonotope (Vec ℝ m)) :
    (Λ *ᵥ ·) '' U.construct
      ⊆ (Λ *ᵥ ·) ''
        (NonlinDASys.enlargeInterfaceInput lamU Λ U.c U).construct := by -- --- PROOF ---
  have hpos : 0 < lamU := lt_of_lt_of_le one_pos hlam
  rintro _ ⟨z, ⟨β, hβ, rfl⟩, rfl⟩
  -- the point of `Û` over `z` scales the coefficients by `1 / λ_U`
  set t : Vec ℝ m := ∑ j, β j • U.G j with ht
  set s : Vec ℝ m := ∑ j, (β j / lamU) • U.G j with hs
  have hst : s = lamU⁻¹ • t := by
    rw [hs, ht, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, div_eq_inv_mul]
  -- the coefficients `β / λ_U` stay in `[-1, 1]`
  have hsmem : U.c + s ∈ U.construct :=
    ⟨fun j => β j / lamU, fun j => by
      rw [abs_div, abs_of_pos hpos]
      exact (div_le_one hpos).2 ((hβ j).trans hlam), rfl⟩
  -- membership in the pieces of `Û`, by the exactness of `plus` and `mtimes`
  have h1 : s ∈ (U.plus (Zonotope.ofPoint (-U.c))).construct := by
    rw [← Zonotope.plus_exact]
    have := Set.add_mem_add hsmem (Zonotope.mem_ofPoint (-U.c))
    convert this using 1
    abel
  have h2 : ((lamU - 1) • Λ + 1) *ᵥ s ∈
      (Zonotope.mtimes ((lamU - 1) • Λ + 1) (U.plus (Zonotope.ofPoint (-U.c)))).construct := by
    rw [← Zonotope.mtimes_exact]
    exact ⟨s, h1, rfl⟩
  have h3 := Set.add_mem_add h2 (Zonotope.mem_ofPoint U.c)
  rw [Zonotope.plus_exact] at h3
  refine ⟨((lamU - 1) • Λ + 1) *ᵥ s + U.c, h3, ?_⟩
  -- `Λ ((λ_U - 1) Λ + I) = λ_U Λ`, which undoes the `1 / λ_U`
  have hΛD : Λ * ((lamU - 1) • Λ + 1) = lamU • Λ := by
    rw [Matrix.mul_add, Matrix.mul_smul, hΛ, Matrix.mul_one, sub_smul, one_smul]; abel
  show Λ *ᵥ (((lamU - 1) • Λ + 1) *ᵥ s + U.c) = Λ *ᵥ (U.c + t)
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_mulVec, hΛD, hst,
    Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul,
    add_comm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
