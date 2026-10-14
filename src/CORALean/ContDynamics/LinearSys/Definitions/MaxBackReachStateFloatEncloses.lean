module

public import CORALean.ContDynamics.LinearSys.Definitions.MaxBackReachState
public import CORALean.ContDynamics.LinearSys.Definitions.MaxBackReachStateFloat

@[expose] public section

/-!
# A float state of `Alg. 3` that stands for an exact one

What `maxBackReachStepFloat` keeps true of its state against the exact layer's: the time lies in
the bracket; the float `Z̲_U(t_k)` lies within `UErr` of the exact one and holds `0` in its
error box; the two disturbance sets `Ẑ_{W₀}`, `Ẑ_W` hold the exact ones; and the float
`R̂^{∃∀}(-τ_{k-1})` lies inside the exact one. The last is the inner approximation, the first
three are what it is derived from and are all outer or within a stated distance.
The lines are those of [1, Alg. 3].

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- The float state `s` stands for the exact state `sr`: the invariant of the float loop. -/
structure LinearSys.MaxBackReachStateFloat.Encloses (s : LinearSys.MaxBackReachStateFloat 𝕋 n)
    (sr : LinearSys.MaxBackReachState n) : Prop where
  /-- The bracket holds `t_k` from below. -/
  tLo_le : toReal s.tLo ≤ sr.t
  /-- And from above. -/
  le_tHi : sr.t ≤ toReal s.tHi
  /-- The error box of `Z̲_U` holds `0`, which the box lemmas ask of an operand. -/
  zero_mem : (0 : Vec ℝ n) ∈ s.ZU.I_error.construct
  /-- Every point of the float `Z̲_U` is a point of the exact one plus an error within `UErr`. -/
  ZU : ∀ x ∈ s.ZU.construct, ∃ u ∈ construct sr.ZU, ∃ e : Vec ℝ n,
    (∀ i, |e i| ≤ toReal (s.UErr i)) ∧ x = u + e
  /-- The float `Ẑ_{W₀}` holds the exact one. -/
  ZW₀ : construct sr.ZW₀ ⊆ s.ZW₀.construct
  /-- The float `Ẑ_W` holds the exact one. -/
  ZW : construct sr.ZW ⊆ s.ZW.construct
  /-- The float `R̂^{∃∀}` is inside the exact one. -/
  R : s.R ⊆ construct sr.R

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
