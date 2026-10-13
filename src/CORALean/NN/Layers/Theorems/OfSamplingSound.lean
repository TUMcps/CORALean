import CORALean.NN.Layers.Operations.PolyRelaxationOfSampling
import CORALean.NN.Layers.Theorems.CoarseBounds
import CORALean.NN.Layers.Theorems.OfBracketSound
import CORALean.NN.Layers.Theorems.SampleBoundsOfDeriv

/-!
# The sampled polynomial relaxation is sound

Only the derivative bound is asked for: a grid that fails its checks costs precision and not
soundness, and the fit owes nothing at all.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ σ' : ℝ → ℝ} {m N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyRelaxation.ofSampling_sound {E : Enclosure 𝕋} {c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋}
    {M dx : 𝕋 → 𝕋 → 𝕋} {p : 𝕋 → 𝕋 → Fin (N + 1) → 𝕋} (hE : E.Sound σ)
    (hd : ∀ x, HasDerivAt σ (σ' x) x)
    (hM : ∀ (l u : 𝕋) (x : ℝ), toReal l ≤ x → x ≤ toReal u →
      |σ' x - Real.evalPolyDeriv (fun k => toReal (c l u k)) x| ≤ toReal (M l u)) :
    (PolyRelaxation.ofSampling E c M dx p).Sound σ :=
  PolyRelaxation.ofBracket_sound (c := c) (lo := fitLo E c M dx p)
    (hi := fitHi E c M dx p) fun l u t hl hu => by
      -- the fit is a polynomial, so the deviation differentiates termwise
      have hg : ∀ x, HasDerivAt (fun y => σ y - Real.evalPoly (fun k => toReal (c l u k)) y)
          (σ' x - Real.evalPolyDeriv (fun k => toReal (c l u k)) x) x :=
        fun x => (hd x).sub (Real.hasDerivAt_evalPoly _ x)
      by_cases hchk : gridChecked (p l u) l u (dx l u) = true
      · rw [fitLo, fitHi, if_pos hchk, if_pos hchk]
        exact sample_bounds_of_deriv
          (g := fun y => σ y - Real.evalPoly (fun k => toReal (c l u k)) y)
          (t := t) hg (fun x hx hx' => hM l u x hx hx') hchk
          (fun i => sampleDevLo_le hE (c l u) (p l u i))
          (fun i => le_sampleDevUp hE (c l u) (p l u i)) hl hu
      · rw [fitLo, fitHi, if_neg hchk, if_neg hchk]
        exact coarse_bounds hE hd (fun x hx hx' => hM l u x hx hx') hl hu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
