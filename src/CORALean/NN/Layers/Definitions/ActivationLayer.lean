module

public import CORALean.NN.Layers.Definitions.Relaxation

@[expose] public section

/-!
# The weights of an activation layer at a relaxation

Any coordinatewise activation as an `Enclose` kind: a relaxation stored in the scalar, and a
proof that it encloses *some* `σ`. The proof is a `Prop`, so two layers at one relaxation are
one layer whichever `σ` each was proved for, and the layer stores nothing over ℝ; `eval` is
the `σ` the proof names, read back inside `Erased`. A layer whose `σ` matters to a caller is
`SigmoidLayer`, `TanhLayer` or `ReluLayer`, or the relational `Layer.activation_encloses`. The
dimension is kept, so its weights carry `dim`, which `rfl` discharges where a layer is built.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The weights of a coordinatewise activation layer: a relaxation stored in the scalar and a proof
that it encloses some activation `σ`. -/
structure ActivationLayer (𝕋 : Type) [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
    (n m : ℕ) where
  R : Relaxation 𝕋
  sound : ∃ σ : ℝ → ℝ, R.IsSound σ
  dim : n = m

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
