import CORALean.ContSet.Zonotope.Real.Operations.ProjectHighDim
import CORALean.ContSet.Zonotope.Real.Theorems.MapExact

/-!
# `Zonotope.projectHighDim_` is exactly the zero-padded set

For an injective `proj`, the result is the set of vectors that read `y` at the coordinates
`proj` for some member `y`, and are `0` everywhere else. Equality, since padding is linear.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n N : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Zonotope.aux_embed_apply (proj : Fin n → Fin N) (hproj : Function.Injective proj)
    (y : Vec ℝ n) (i : Fin N) :
    Zonotope.embed proj y i = if h : ∃ k, proj k = i then y h.choose else 0 := by -- --- PROOF ---
  classical
  simp only [Zonotope.embed, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]
  by_cases h : ∃ k, proj k = i
  · rw [dif_pos h, Finset.sum_eq_single h.choose]
    · rw [if_pos h.choose_spec, one_mul]
    · intro k _ hk
      rw [if_neg, zero_mul]
      intro hki
      exact hk (hproj (hki.trans h.choose_spec.symm))
    · simp
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg fun hk => h ⟨k, hk⟩, zero_mul]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.projectHighDim_exact (Z : Zonotope (Vec ℝ n)) (proj : Fin n → Fin N)
    (hproj : Function.Injective proj) :
    (Z.projectHighDim_ proj).construct = {x | ∃ y ∈ Z.construct, (∀ k, x (proj k) = y k) ∧
      ∀ i, i ∉ Set.range proj → x i = 0} := by -- --- PROOF ---
  show (Z.map (Zonotope.embed proj)).construct = _
  rw [← Zonotope.map_exact (Zonotope.embed proj) Z]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, fun k => ?_, fun i hi => ?_⟩
    · rw [Zonotope.aux_embed_apply proj hproj, dif_pos ⟨k, rfl⟩]
      exact congrArg y (hproj (Exists.choose_spec (⟨k, rfl⟩ : ∃ k', proj k' = proj k)))
    · rw [Zonotope.aux_embed_apply proj hproj, dif_neg fun ⟨k, hk⟩ => hi ⟨k, hk⟩]
  · rintro ⟨y, hy, hx, h0⟩
    refine ⟨y, hy, funext fun i => ?_⟩
    rw [Zonotope.aux_embed_apply proj hproj]
    by_cases h : ∃ k, proj k = i
    · rw [dif_pos h, ← hx h.choose, h.choose_spec]
    · rw [dif_neg h, h0 i fun ⟨k, hk⟩ => h ⟨k, hk⟩]


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
