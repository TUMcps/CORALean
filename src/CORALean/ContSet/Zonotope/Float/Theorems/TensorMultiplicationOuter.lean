module

public import CORALean.ContSet.Zonotope.Float.Theorems.TensorMultiplicationCoeff
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# `Zonotope.tensorMultiplication` encloses the tensor images, over a floating-point scalar

For a zonotope `Z` centered at the origin and a tensor `M`,
`{ Mᵢⱼₖₗ xⱼ xₖ xₗ | x ∈ Z } ⊆ Z.tensorMultiplication M L`, under the exact layer's hypotheses on the
lists `L`: `perm` runs over every ordered triple of generator indices exactly once, and two
permutations sent to one column by `map` are reorderings of one another. The stored columns at the
coefficients of `tensorMultiplication_coeff` are the nominal point, and the shortfalls per
coefficient are in the box. The enclosure is not exact.

## Inputs
* `Z` – zonotope
* `M` – third-order tensor
* `L` – permutation lists
* `x` – point

## Hypotheses
* `hc` – center is zero
* `hperm` – permutations run over each triple once
* `hmap` – same column means reordered triple
* `hx` – point lies in the zonotope

## Conclusion
* tensor image of the point lies in the computed zonotope
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

theorem Zonotope.tensorMultiplication_outer (Z : Zonotope (Vec 𝕋 n)) (M : Tensor3 𝕋 n)
    (L : Real.Zonotope.TensorLists Z.absorbRounding.h) (hc : ∀ i, toReal (Z.c i) = 0)
    (hperm : Function.Bijective fun p : Fin L.P => (L.perm p 0, L.perm p 1, L.perm p 2))
    (hmap : ∀ p q, L.map p = L.map q →
      ({L.perm p 0, L.perm p 1, L.perm p 2} : Multiset (Fin Z.absorbRounding.h)) =
        {L.perm q 0, L.perm q 1, L.perm q 2})
    {x : Vec ℝ n} (hx : x ∈ Z.construct) : -- --- CONCL ---
    Real.Zonotope.tensorEval (fun i a b c => toReal (M i a b c)) x
      ∈ (Z.tensorMultiplication M L).construct := by -- --- PROOF ---
  obtain ⟨γ, hγ, Δ, hΔ, heq⟩ := Zonotope.tensorMultiplication_coeff Z M L hc hperm hmap hx
  -- the nominal point at `γ`, and the shortfalls in the box
  refine ⟨fun i => ∑ m, toReal ((Z.tensorMultiplication M L).G m i) * γ m,
    Zonotope.mem_nominalSet_iff.mpr ⟨γ, hγ, fun i => ?_⟩, _,
    Zonotope.mem_generatorError (G := Zonotope.step_tensorHDiff M Z.absorbRounding L) hΔ hγ, ?_⟩
  · show _ = toReal (zero : 𝕋) + _
    rw [toReal_zero, zero_add]
  · rw [heq]
    funext i
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
