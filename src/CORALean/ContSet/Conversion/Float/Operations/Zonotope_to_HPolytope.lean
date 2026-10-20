module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Zonotope.Float.Operations.FacetNormal
public import CORALean.Global.Float.Sqrt
public import Mathlib.Data.List.Sublists
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.InflatedContSet.Operations.Bound
public import CORALean.ContSet.Interval.Float.Operations.BoundDot

@[expose] public section

/-!
# A zonotope as halfspaces, over a floating-point scalar

`Zonotope.hPolytope` bounds the caller's rows. `Zonotope.hPolytopeFacets` is CORA's `polytope(Z)`
at `'exact'` with the rows computed in floats: the box rows `[I; -I]` when every generator is
zero, otherwise the cross product of every combination of `n - 1` generators (`facetNormal`, each
minor a determinant candidate), the zero ones dropped, each divided by its length `normUp p`
rounded up; their bounds are `boundDot`'s, so the rows are sound whatever the rounding made of
them, and only their tightness depends on it.

## Inputs
* `Z` – zonotope
* `c` – linear functional
* `a` – coefficient vector

## Hypotheses
* `hc` – functional equals the dot product with `a`

## Output
* float upper bound on `c` over the nominal set
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.nominalBoundDot (Z : Zonotope (Vec 𝕋 n)) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) :
    FloatBound 𝕋 (nominalSet Z) c :=
  FloatBound.ofSupportBound ((InflatedContSet.nominal Z).supportBound c)
    (addUp (dotUp a Z.c)
      (sumUp fun j => maximum (dotUp a fun i => Z.G j i) (neg (dotDown a fun i => Z.G j i))))
    (by
      have h₁ : c (InflatedContSet.nominal Z).c ≤ toReal (dotUp a Z.c) := by
        rw [hc]
        exact le_dotUp a Z.c
      have h₂ : ∀ j, |c ((InflatedContSet.nominal Z).G j)|
          ≤ toReal (maximum (dotUp a fun i => Z.G j i)
              (neg (dotDown a fun i => Z.G j i))) := by
        intro j
        -- the nominal generator spelt out, so both sides name the same sum
        have hval : c ((InflatedContSet.nominal Z).G j)
            = ∑ k, toReal (a k) * toReal (Z.G j k) := hc _
        rw [hval, toReal_maximum, toReal_neg]
        refine abs_le.mpr ⟨?_, ?_⟩
        · have hdown := dotDown_le a fun i => Z.G j i
          have hm := le_max_right (toReal (dotUp a fun i => Z.G j i))
            (-toReal (dotDown a fun i => Z.G j i))
          linarith
        · have hup := le_dotUp a fun i => Z.G j i
          have hm := le_max_left (toReal (dotUp a fun i => Z.G j i))
            (-toReal (dotDown a fun i => Z.G j i))
          linarith
      -- and the generators' total, summed upward once
      have h₃ : (∑ j, |c ((InflatedContSet.nominal Z).G j)|)
          ≤ toReal (sumUp fun j => maximum (dotUp a fun i => Z.G j i)
              (neg (dotDown a fun i => Z.G j i))) :=
        le_trans (Finset.sum_le_sum fun j _ => h₂ j) (sum_le_sumUp _)
      have h₄ := add_le_addUp (dotUp a Z.c)
        (sumUp fun j => maximum (dotUp a fun i => Z.G j i) (neg (dotDown a fun i => Z.G j i)))
      show c (InflatedContSet.nominal Z).c + ∑ j, |c ((InflatedContSet.nominal Z).G j)| ≤ _
      linarith)

def Zonotope.boundDot (Z : Zonotope (Vec 𝕋 n)) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) : FloatBound 𝕋 Z.construct c :=
  InflatedContSet.boundOfParts (Z.nominalBoundDot a hc) (Z.I_error.boundDot a hc)

def Zonotope.hPolytope (Z : Zonotope (Vec 𝕋 n)) (Aq : Mat 𝕋 q n) : HPolytope 𝕋 (Vec 𝕋 n) :=
  HPolytope.ofBounds Aq fun i => Z.boundDot (Aq i) fun _ => rfl

/-- CORA's `polytope(Z)` at `'exact'`, the facet rows computed in floats. -/
def Zonotope.hPolytopeFacets {m : ℕ} (p : ℕ) (Z : Zonotope (Vec 𝕋 (m + 1))) :
    HPolytope 𝕋 (Vec 𝕋 (m + 1)) :=
  let isZero : Vec 𝕋 (m + 1) → Bool := fun v => (List.finRange (m + 1)).all fun i =>
    le (absolute (v i)) zero
  -- 1. no generators: `C = [eye(n); -eye(n)]`
  if (List.finRange Z.h).all fun j => isZero (Z.G j) then
    let I : Mat 𝕋 (m + 1) (m + 1) := diagonalBlock fun _ => one
    Z.hPolytope (Fin.append I (-I))
  else
    -- 2. `ndimCross` of every combination of `n - 1` generators, the zero ones dropped
    let N := ((List.finRange Z.h).sublistsLen m).attach.map fun l =>
      Z.facetNormal fun j => l.1.get ⟨j, by rw [(List.mem_sublistsLen.mp l.2).2]; exact j.isLt⟩
    -- 3. each divided by its length, then `[C; -C]` at the zonotope's support values
    let C := (N.filter fun v => !isZero v).map fun v i => divUp (v i) (normUp p v)
    Z.hPolytope (Fin.append (fun k => C.get k) (-fun k => C.get k))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
