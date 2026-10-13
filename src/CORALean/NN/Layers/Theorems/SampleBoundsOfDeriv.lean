module

public import CORALean.NN.Layers.Theorems.ExistsGridClose
public import CORALean.NN.Layers.Theorems.GridMemOfChecked
public import CORALean.NN.Layers.Theorems.SampleBoundsOfCover

@[expose] public section

/-!
# A checked grid's sampled range brackets a function

`sample_bounds_of_cover` at a grid that passed its checks, which is the form a caller reaches:
sound at every such grid, and tighter as `dx` shrinks.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem sample_bounds_of_deriv {g g' : ℝ → ℝ} {l u M dx : 𝕋}
    {p gLo gUp : Fin (N + 1) → 𝕋} {t : ℝ} (hd : ∀ x, HasDerivAt g (g' x) x)
    (hM : ∀ x, toReal l ≤ x → x ≤ toReal u → |g' x| ≤ toReal M)
    (hchk : gridChecked p l u dx) (hlo : ∀ i, toReal (gLo i) ≤ g (toReal (p i)))
    (hup : ∀ i, g (toReal (p i)) ≤ toReal (gUp i)) (hl : toReal l ≤ t) (hu : t ≤ toReal u) :
    toReal (sampleLo gLo M dx) ≤ g t ∧ g t ≤ toReal (sampleHi gUp M dx) :=
  sample_bounds_of_cover hd hM (grid_mem_of_checked hchk)
    (fun _ hy hy' => exists_grid_close hchk hy hy') hlo hup hl hu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
