module

public import CORALean.ContSet.Zonotope.Real.Operations.LengthSplit
public import CORALean.ContSet.Zonotope.Real.Operations.SplitKept
public import CORALean.ContSet.Zonotope.Real.Operations.Plus

@[expose] public section

/-!
# `Zonotope.reduceUnderApproxNLP`

The nonlinear-programming method of [1, Sec. IV-D] in its fast form, Steps 1) to 3): keep the
`ν̂ - n` longest generators `G_a` and replace the rest, `⟨0, G_b⟩`, by a square `Ĝ_b ∈ ℝ^{n×n}`.
The program (6) that finds `Ĝ_b` (maximize `|det Ĝ_b|` subject to (1), by a gradient method that
is not guaranteed to find its global maximum) is the argument `Gb'`.

## Inputs
* `Z` – zonotope
* `r` – kept generator count
* `Gb'` – optimized replacement generators

## Hypotheses
* `hn` – at least `n` kept
* `hr` – fewer than all generators

## Output
* zonotope of the kept and replacement generators

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the
      Order Reduction of Zonotopes". IEEE Control Systems Letters, 9:1730-1735, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. IV-D]: `Ẑ = ⟨c, G_a⟩ ⊕ ⟨0, Ĝ_b⟩ = ⟨c, [G_a Ĝ_b]⟩`, of `ν̂` generators. -/
noncomputable def Zonotope.reduceUnderApproxNLP (Z : Zonotope (Vec ℝ n)) (r : ℕ) (hn : n ≤ r)
    (hr : r < Z.h) (Gb' : Fin n → Vec ℝ n) : Zonotope (Vec ℝ n) :=
  let part := Z.lengthSplit (r - n) (by omega)          -- 1) Z = ⟨c, G_a⟩ ⊕ ⟨0, G_b⟩
  let Za := Z.splitKept part                            --    ⟨c, G_a⟩
  Za.plus ⟨n, 0, Gb'⟩                                   -- 3) ⟨c, G_a⟩ ⊕ ⟨0, Ĝ_b⟩ (2: Ĝ_b = Gb')

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
