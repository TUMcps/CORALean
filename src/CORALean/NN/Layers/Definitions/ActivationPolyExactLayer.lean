module

public import CORALean.NN.Layers.Theorems.Real.ActivationPolySound

@[expose] public section

/-!
# The exact polynomial activation layer, as an `Enclose` kind

`Real.Layer.activationPoly` as a kind, at the exact polynomial zonotope: a polynomial
relaxation per neuron over ℝ, and a proof that all of them enclose some one `σ`, as in
`ActivationPolyLayer`. Its propagation is over ℝ,
so the instance is noncomputable and lives here beside the other specifications; the runnable
one is `ActivationPolyLayer`. It keeps the dimension, so it carries `dim`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

structure ActivationPolyLayer (n m : ℕ) where
  deg : ℕ
  P : LayerRelaxation ℝ n deg
  sound : ∃ σ : ℝ → ℝ, ∀ i, (P i).Sound σ
  dim : n = m

noncomputable instance : Enclose ActivationPolyLayer 𝒫𝒵 where
  eval := fun {n m} l => match n, m, l with
    | _, _, ⟨_, _, hP, rfl⟩ => Erased.mk fun x i => hP.choose (x i)
  enclose := fun {n m} l => match n, m, l with
    | _, _, ⟨_, P, _, rfl⟩ => (Layer.activationPoly P).enclose
  enclose_outer := fun {n m} l s => match n, m, l with
    | _, _, ⟨_, _, hP, rfl⟩ => by
      rw [Erased.out_mk]
      exact (Layer.activationPoly_sound hP.choose_spec).image_subset s

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
