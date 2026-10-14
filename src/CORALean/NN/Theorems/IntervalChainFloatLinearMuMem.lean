module

public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MtimesMem
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.NN.Operations.IntervalChainFwdFloat

@[expose] public section

/-!
# The linear layer's centre is in its float box
The centre `mu = W (l + u)/2 + b` of the layer's output interval, for `l`, `u` in their boxes, is in
the box `IntervalChain.fwd` and `backprop` compute it as.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A float vector read as reals is in its point box. -/
theorem aux_mem_point {m : ℕ} (b : Vec 𝕋 m) :
    toRealVec b ∈ (⟨b, b⟩ : Interval (Vec 𝕋 m)).construct :=
  fun _ => ⟨le_rfl, le_rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem IntervalChain.linear_mu_mem {n m : ℕ} (W : Mat 𝕋 m n) (b : Vec 𝕋 m)
    {P : Interval (Vec 𝕋 n) × Interval (Vec 𝕋 n)} {p : Vec ℝ n × Vec ℝ n}
    (h1 : p.1 ∈ P.1.construct) (h2 : p.2 ∈ P.2.construct) :
    toRealMat W *ᵥ ((1 / 2 : ℝ) • (p.1 + p.2)) + toRealVec b
      ∈ (Interval.plus (Interval.mtimes W (Interval.halve (Interval.plus P.1 P.2)))
          ⟨b, b⟩).construct :=
  Interval.plus_outer _ _ (Set.add_mem_add
    (Interval.mtimes_mem W _ rfl _ (Interval.halve_plus_mem h1 h2)) (aux_mem_point b))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
