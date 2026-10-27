module

public import CORALean.NN.Layers.Operations.PolyRelaxationOfSampling
public import CORALean.NN.Layers.Operations.CoarseHi
public import CORALean.NN.Layers.Operations.CoarseLo
public import CORALean.NN.Layers.Operations.SampleDevUp
public import CORALean.NN.Layers.Theorems.EvalPolyDownLe
public import CORALean.NN.Layers.Theorems.Real.HasDerivAtEvalPoly
public import CORALean.NN.Layers.Theorems.SampleBoundsOfCover
public import CORALean.NN.Layers.Operations.SampleDevLo
public import CORALean.NN.Layers.Theorems.LeEvalPolyUp
public import CORALean.NN.Layers.Theorems.OfBracketEncloses
public import CORALean.NN.Layers.Theorems.SampleBoundsOfDeriv
public import CORALean.NN.Layers.Theorems.SampleDevLoLe

@[expose] public section

/-!
# The sampled polynomial relaxation is sound

Only the derivative bound is asked for: a grid that fails its checks costs precision and not
soundness, and the fit owes nothing at all.

## Inputs
* `E` – enclosure of the activation
* `c` – fit coefficients for each box
* `M` – derivative bound for each box
* `dx` – grid spacing for each box
* `p` – proposed sample grid for each box

## Hypotheses
* `hE` – enclosure is sound for the activation
* `hd` – the activation has the given derivative
* `hM` – derivative differs from the fit's by at most the bound

## Conclusion
* the sampled polynomial relaxation is sound for the activation
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ σ' : ℝ → ℝ} {m N : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ} {m : ℕ}


end


section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ} {m : ℕ}

/-- A sampled deviation's upper bound. -/
private theorem aux_le_sampleDevUp {E : Enclosure 𝕋} (hE : E.Encloses σ) (c : Fin (m + 1) → 𝕋)
    (x : 𝕋) : -- --- CONCL ---
    σ (toReal x) - Real.evalPoly (fun k => toReal (c k)) (toReal x)
      ≤ toReal (sampleDevUp E c x) := by -- --- PROOF ---
  have h1 := sub_le_subUp (E.enclose x).sup (evalPolyDown c x)
  have h2 := hE.le_hi x
  have h3 := evalPolyDown_le c x
  rw [sampleDevUp]
  linarith

end


section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ σ' : ℝ → ℝ} {m : ℕ}

/-- The fallback bracket is sound outright. -/
private theorem aux_coarse_bounds {E : Enclosure 𝕋} {c : Fin (m + 1) → 𝕋} {M l u : 𝕋} {t : ℝ}
    (hE : E.Encloses σ) (hd : ∀ x, HasDerivAt σ (σ' x) x)
    (hM : ∀ x, toReal l ≤ x → x ≤ toReal u →
      |σ' x - Real.evalPolyDeriv (fun k => toReal (c k)) x| ≤ toReal M)
    (hl : toReal l ≤ t) (hu : t ≤ toReal u) : -- --- CONCL ---
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
    (fun _ => sampleDevLo_le hE c l) (fun _ => aux_le_sampleDevUp hE c l) hl hu

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyRelaxation.ofSampling_encloses {E : Enclosure 𝕋} {c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋}
    {M dx : 𝕋 → 𝕋 → 𝕋} {p : 𝕋 → 𝕋 → Fin (N + 1) → 𝕋} (hE : E.Encloses σ)
    (hd : ∀ x, HasDerivAt σ (σ' x) x)
    (hM : ∀ (l u : 𝕋) (x : ℝ), toReal l ≤ x → x ≤ toReal u →
      |σ' x - Real.evalPolyDeriv (fun k => toReal (c l u k)) x| ≤ toReal (M l u)) :
    (PolyRelaxation.ofSampling E c M dx p).Encloses σ :=
  PolyRelaxation.ofBracket_encloses (c := c) (lo := fitLo E c M dx p)
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
          (fun i => aux_le_sampleDevUp hE (c l u) (p l u i)) hl hu
      · rw [fitLo, fitHi, if_neg hchk, if_neg hchk]
        exact aux_coarse_bounds hE hd (fun x hx hx' => hM l u x hx hx') hl hu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
