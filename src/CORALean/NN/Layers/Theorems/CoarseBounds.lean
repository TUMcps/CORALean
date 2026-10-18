module

public import CORALean.NN.Layers.Operations.CoarseHi
public import CORALean.NN.Layers.Operations.CoarseLo
public import CORALean.NN.Layers.Theorems.LeSampleDevUp
public import CORALean.NN.Layers.Theorems.Real.HasDerivAtEvalPoly
public import CORALean.NN.Layers.Theorems.SampleBoundsOfCover
public import CORALean.NN.Layers.Theorems.SampleDevLoLe

@[expose] public section

/-!
# The fallback bracket is sound outright

The left end is in the box and the width covers it, so neither fact is a check.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ σ' : ℝ → ℝ} {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem coarse_bounds {E : Enclosure 𝕋} {c : Fin (m + 1) → 𝕋} {M l u : 𝕋} {t : ℝ}
    (hE : E.Sound σ) (hd : ∀ x, HasDerivAt σ (σ' x) x)
    (hM : ∀ x, toReal l ≤ x → x ≤ toReal u →
      |σ' x - Real.evalPolyDeriv (fun k => toReal (c k)) x| ≤ toReal M)
    (hl : toReal l ≤ t) (hu : t ≤ toReal u) : -- --- STMT ---
    toReal (coarseLo E c M l u) ≤ σ t - Real.evalPoly (fun k => toReal (c k)) t
      ∧ σ t - Real.evalPoly (fun k => toReal (c k)) t
        ≤ toReal (coarseHi E c M l u) := by -- --- PROOF ---
  have hg : ∀ x, HasDerivAt (fun y => σ y - Real.evalPoly (fun k => toReal (c k)) y)
      (σ' x - Real.evalPolyDeriv (fun k => toReal (c k)) x) x :=
    fun x => (hd x).sub (Real.hasDerivAt_evalPoly _ x)
  -- the whole width bounds every distance to the left end, rounded up
  have hw := sub_le_subUp u l
  exact sample_bounds_of_cover (g := fun y => σ y - Real.evalPoly (fun k => toReal (c k)) y)
    (t := t) (p := fun _ : Fin 1 => l) hg hM (fun _ => ⟨le_rfl, hl.trans hu⟩)
    (fun y hy hy' => ⟨0, by rw [abs_le]; exact ⟨by linarith, by linarith⟩⟩)
    (fun _ => sampleDevLo_le hE c l) (fun _ => le_sampleDevUp hE c l) hl hu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
