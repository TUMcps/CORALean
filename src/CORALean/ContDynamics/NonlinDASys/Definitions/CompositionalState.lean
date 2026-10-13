module

public import CORALean.ContDynamics.NonlinDASys.NonlinDASys
public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# What a pass of the compositional loop of [1, Alg. 2] carries

Per subsystem `i` of the `n_s`: the flag `inputEnclosure⁽ⁱ⁾` (line 1), its input set `U⁽ⁱ⁾`
(updated in line 16), the assumed input set `Û⁽ⁱ⁾` (line 5), and the two sets `[1, Alg. 1]`
returned for it from `Û⁽ⁱ⁾` (line 6): `R⁽ⁱ⁾ᵈ(t_{k+1})` and the local `R⁽ⁱ⁾(τ_k)`, of dimensions
`e i` and `d i`; `m i` is the dimension of the subsystem's inputs.

## References

* [1] M. Althoff. "Formal and Compositional Analysis of Power Systems using Reachable Sets".
      IEEE Transactions on Power Systems, 29(5):2270-2280, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- The data of one pass of [1, Alg. 2]'s `repeat` loop (lines 2-18). -/
structure NonlinDASys.CompositionalState {ns : ℕ} (m e d : Fin ns → ℕ) where
  /-- `inputEnclosure⁽ⁱ⁾`, lines 1, 12 and 14. -/
  inputEnclosure : Fin ns → Bool
  /-- `U⁽ⁱ⁾`, line 16. -/
  U : ∀ i, Zonotope (Vec ℝ (m i))
  /-- `Û⁽ⁱ⁾`, line 5. -/
  Uhat : ∀ i, Zonotope (Vec ℝ (m i))
  /-- `R⁽ⁱ⁾ᵈ(t_{k+1})`, line 6. -/
  Rnext : ∀ i, Zonotope (Vec ℝ (e i))
  /-- `R⁽ⁱ⁾(τ_k)`, line 6. -/
  Rloc : ∀ i, Zonotope (Vec ℝ (d i))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
