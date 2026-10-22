module

public import CORALean.NN.Layers.Definitions.RegionPoly

@[expose] public section

/-!
# The main loop of `findRegionPolys`
`while l < u` of CORA's: a left polynomial from `l`, then, unless that reached `u`, a right
polynomial from `u`, moving `l` and `u` inward. The loop ends when `u ≤ l` is certified by
`le`; CORA's `l == u` break after the left polynomial is the same test. `fuel` bounds the outer
loop and each inner halving, `none` being `CORA:notConverged` or running out of it. The
regions come back in the order found, not sorted by `l` as CORA's last line does.

## Inputs
* `F` – polynomial relaxations by order
* `order` – polynomial order
* `tol` – error tolerance

## Output
* regions found between the two ends, added to the accumulator
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]

/-- The relaxation's polynomial on the box `[l, u]` it is fitted on. -/
def RegionPoly.aux_ofRelaxation {m : ℕ} (R : PolyRelaxation 𝕋 m) (l u : 𝕋) : RegionPoly 𝕋 :=
  ⟨some l, some u, m, R.coeffs l u, R.error l u⟩

end


/-- The lowest-order fit of `[l, u]` the loop reaches from the current one `cur`. -/
def aux_lowerRegionOrder (F : (o : ℕ) → PolyRelaxation 𝕋 o) (tol l u : 𝕋) :
    ℕ → RegionPoly 𝕋 → RegionPoly 𝕋
  | 0, cur => cur
  | k + 1, cur =>
    if ltStrict ((F k).error l u) tol then
      aux_lowerRegionOrder F tol l u k (RegionPoly.aux_ofRelaxation (F k) l u)
    else cur


/-- The accepted region `[l_i, u]` with its left end `l_i`, or `none`. -/
def aux_findRegionRight (F : (o : ℕ) → PolyRelaxation 𝕋 o) (order : ℕ) (tol u : 𝕋) :
    ℕ → 𝕋 → Option (RegionPoly.Found 𝕋)
  | 0, _ => none
  | fuel + 1, li =>
    if le ((F order).error li u) tol then
      some ⟨RegionPoly.aux_ofRelaxation (F order) li u, li⟩
    else
      let li' := subDown u (half (subUp u li))
      if ltStrict (subUp u li') tol then none else aux_findRegionRight F order tol u fuel li'


/-- The accepted region `[l, u_i]` with its right end `u_i`, or `none`. -/
def aux_findRegionLeft (F : (o : ℕ) → PolyRelaxation 𝕋 o) (order : ℕ) (tol l : 𝕋) :
    ℕ → 𝕋 → Option (RegionPoly.Found 𝕋)
  | 0, _ => none
  | fuel + 1, ui =>
    if le ((F order).error l ui) tol then
      some ⟨aux_lowerRegionOrder F tol l ui order (RegionPoly.aux_ofRelaxation (F order) l ui), ui⟩
    else
      let ui' := addUp l (half (subUp ui l))
      if ltStrict (subUp ui' l) tol then none else aux_findRegionLeft F order tol l fuel ui'


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The regions found between `l` and `u`, put in front of `acc`. -/
def findRegionLoop (F : (o : ℕ) → PolyRelaxation 𝕋 o) (order : ℕ) (tol : 𝕋) :
    ℕ → 𝕋 → 𝕋 → List (RegionPoly 𝕋) → Option (List (RegionPoly 𝕋))
  | 0, l, u, acc => if le u l then some acc else none
  | fuel + 1, l, u, acc =>
    if le u l then some acc
    else
      match aux_findRegionLeft F order tol l (fuel + 1) u with
      | none => none
      | some ⟨rL, l'⟩ =>
        if le u l' then some (rL :: acc)
        else
          match aux_findRegionRight F order tol u (fuel + 1) l' with
          | none => none
          | some ⟨rR, u'⟩ => findRegionLoop F order tol fuel l' u' (rR :: rL :: acc)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
