module

public import CORALean.ContSet.Zonotope.Float.Theorems.TensorMultiplicationCoeff
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# A scaled tensor image is enclosed by `tensorMultiplication`, over a floating-point scalar

A zonotope centered at the origin and with a symmetric box is closed under scaling by `[-1, 1]`: the
coefficients and the shortfalls of `tensorMultiplication_coeff` scale together, so
`γ • { Mᵢⱼₖₗ xⱼ xₖ xₗ | x ∈ Z } ⊆ Z.tensorMultiplication M L` for `|γ| ≤ 1`. It is what the sum over
the generators of a matrix zonotope of tensors (`tensorMultiplication_zono`) needs.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.tensorMultiplication_smul_outer (Z : Zonotope (Vec 𝕋 n)) (M : Tensor3 𝕋 n)
    (L : Real.Zonotope.TensorLists Z.absorbRounding.h) (hc : ∀ i, toReal (Z.c i) = 0)
    (hperm : Function.Bijective fun p : Fin L.P => (L.perm p 0, L.perm p 1, L.perm p 2))
    (hmap : ∀ p q, L.map p = L.map q →
      ({L.perm p 0, L.perm p 1, L.perm p 2} : Multiset (Fin Z.absorbRounding.h)) =
        {L.perm q 0, L.perm q 1, L.perm q 2})
    {x : Vec ℝ n} (hx : x ∈ Z.construct) {t : ℝ} (ht : |t| ≤ 1) : -- --- CONCL ---
    t • Real.Zonotope.tensorEval (fun i a b c => toReal (M i a b c)) x
      ∈ (Z.tensorMultiplication M L).construct := by -- --- PROOF ---
  obtain ⟨γ, hγ, Δ, hΔ, heq⟩ := Zonotope.tensorMultiplication_coeff Z M L hc hperm hmap hx
  -- the scaled coefficients stay in `[-1, 1]`
  have hγt : ∀ m, |t * γ m| ≤ 1 := fun m => by
    rw [abs_mul]
    exact mul_le_one₀ ht (abs_nonneg _) (hγ m)
  -- the nominal point at the scaled coefficients, and the shortfalls in the box
  refine ⟨fun i => ∑ m, toReal ((Z.tensorMultiplication M L).G m i) * (t * γ m),
    Zonotope.mem_nominalSet_iff.mpr ⟨fun m => t * γ m, hγt, fun i => ?_⟩, _,
    Zonotope.mem_generatorError (G := Zonotope.aux_tensorHDiff M Z.absorbRounding L) hΔ hγt, ?_⟩
  · show _ = toReal (zero : 𝕋) + _
    rw [toReal_zero, zero_add]
  · funext i
    have e := congrFun heq i
    simp only [Pi.smul_apply, smul_eq_mul, e]
    change (∑ m, toReal (Zonotope.tensorHDown M Z.absorbRounding L i m) * (t * γ m))
        + ∑ j, Δ i j * (t * γ j) = _
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
