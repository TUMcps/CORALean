module

public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# `Zonotope.replaceIdMatCora`: `replaceId` of a matrix zonotope as CORA's code runs it

`@matZonotope/replaceId.m` is `@polyZonotope/replaceId.m` with `pZ` renamed to `mZ`: it reads the
property `mZ.id` (l. 38, `id_part_old = mZ.id`, and l. 46, `ismember(id_part_old,mZ.id)`) and
writes `mZ.id(ii_o)` (l. 52). `matZonotope.m` (l. 39-45) has the properties `C`, `G`, `gens` and
`generator` and no `id`, so reading it is an error. Every call stops: with one further argument at
l. 38; with two, at l. 46 (or earlier, at the `throw` of l. 46-49, when the two id lists differ in
length); with none, `id_part_old` is never assigned; with more, `narginchk(1,3)` rejects it.
Read from the source, not run.

# CORA's `replaceId(matZonotope, ...)` throws for every call

`replaceId(matZonotope(C,G), [1;2])` stops with an unrecognized property `id`.

## Inputs
* `k` – argument count

## Hypotheses
* none

## Conclusion
* every call ends in an error
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- Reading the property `p` of a `matZonotope`: an error unless `matZonotope.m` declares it, and it
declares `C`, `G`, `gens` and `generator`. -/
def Zonotope.matReadPropCora (p : String) : Option Unit :=
  if p ∈ ["C", "G", "gens", "generator"] then some () else none

-- The model: CORA's code as printed, kept only to be refuted.
/-- `replaceId(mZ, varargin{:})` with `k` further arguments: `none` is a MATLAB error. -/
def Zonotope.replaceIdMatCora (k : ℕ) : Option Unit := do
  guard (k ≤ 2)                                  -- narginchk(1,3)
  if k = 1 then Zonotope.matReadPropCora "id"    -- id_part_old = mZ.id
  else if k = 2 then pure ()                     -- id_part_old = varargin{1}
  else failure                                   -- k = 0: id_part_old is never assigned
  Zonotope.matReadPropCora "id"                  -- ismember(id_part_old, mZ.id)


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every call of `replaceId` on a matrix zonotope ends in an error. -/
theorem Zonotope.replaceIdMat_cora_counterexample (k : ℕ) :
    Zonotope.replaceIdMatCora k = none := by
  unfold Zonotope.replaceIdMatCora Zonotope.matReadPropCora
  by_cases h2 : k ≤ 2
  · by_cases h1 : k = 1 <;> by_cases h0 : k = 2 <;> simp [h2, h1, h0, failure]
  · simp [h2, failure]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
