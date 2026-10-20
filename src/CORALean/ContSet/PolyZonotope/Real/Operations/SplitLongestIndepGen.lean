module

public import CORALean.ContSet.PolyZonotope.Real.Operations.SplitLongestGen

@[expose] public section

/-!
# `PolyZonotope.splitLongestIndepGen`

The subfunction `aux_splitLongestIndepGen` of CORA's `@polyZonotope/containsPointSet`: halve
the longest independent generator `g`, one half with center `c + g/2`, the other with
center `c - g/2`, the generator `g/2` in both. With no independent generator both halves are
the set itself, where CORA errors.

## Inputs
* `pZ` – polynomial zonotope

## Output
* pair of polynomial zonotopes from halving the longest independent generator
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def PolyZonotope.splitLongestIndepGen (pZ : PolyZonotope (Vec ℝ n)) :
    PolyZonotope (Vec ℝ n) × PolyZonotope (Vec ℝ n) :=
  match (List.finRange pZ.q).argmax (fun i => ∑ c, pZ.GI i c ^ 2) with
  | some j =>
    let g := pZ.GI j
    ({ pZ with c := pZ.c + (2 : ℝ)⁻¹ • g, GI := Function.update pZ.GI j ((2 : ℝ)⁻¹ • g) },
     { pZ with c := pZ.c - (2 : ℝ)⁻¹ • g, GI := Function.update pZ.GI j ((2 : ℝ)⁻¹ • g) })
  | none => (pZ, pZ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
