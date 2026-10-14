module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `Zonotope.andAveraging`

CORA's `@zonotope/private/priv_andAveraging`, the zonotope [1, Thm. 1] encloses the intersection
of the `m_i` zonotopes `Z̄ʲ = ⟨c̄ʲ, Ḡʲ⟩` with: for weights `wʲ` of nonzero sum, the centre
`ć = (Σⱼ wʲ c̄ʲ) / Σⱼ wʲ` Eq. 14 of [1, Thm. 1] and the generators
`Ǵ = [w¹ Ḡ¹, …, wᵐ Ḡᵐ] / Σⱼ wʲ` Eq. 15 of [1, Thm. 1], the blocks laid side by side with
one coefficient each, as `cat` is a concatenation. The weights are any reals of nonzero sum,
a negative one included; CORA's `'normGen'` weights `wʲ = 1 / (tr(ḠʲḠʲᵀ) Σᵣ 1 / tr(ḠʳḠʳᵀ))`
are `[1, Prop. 1]`. It is the diffusion update, Step 2 of [1, Alg. 1] and of [1, Alg. 2].

## References

* [1] A. Alanwar, J. J. Rath, H. Said, K. H. Johansson and M. Althoff. "Distributed Set-Based
      Observers Using Diffusion Strategies". Journal of the Franklin Institute,
      360(10):6976-6993, 2023. arXiv:2003.10347.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Zonotope.andAveraging (Z : Fin N → Zonotope (Vec ℝ n)) (w : Fin N → ℝ) :
    Zonotope (Vec ℝ n) :=
  let s : ℝ := ∑ j, w j                                          -- Σⱼ wʲ
  { h := ∑ j, (Z j).h
    c := s⁻¹ • ∑ j, w j • (Z j).c                                -- Eq. 14
    G := fun k => (s⁻¹ * w (finSigmaFinEquiv.symm k).1) •        -- Eq. 15, block (wʲ / s) Ḡʲ
      (Z (finSigmaFinEquiv.symm k).1).G (finSigmaFinEquiv.symm k).2 }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
