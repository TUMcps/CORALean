module

public import CORALean.ContSet.Ellipsoid.Float.Operations.ExcludesPoint

@[expose] public section

/-!
# A `true` from `Ellipsoid.excludesPoint` proves non-membership

Every point of the set reads at most the bound in direction `a`; the point reads at least its
rounded-down reading, which the test found strictly above the bound.

## Inputs
* `E` – ellipsoid
* `p` – point
* `a` – separating direction
* `s` – length bounding `√(aᵀ Q a)`

## Hypotheses
* `h` – `excludesPoint` returns `true`

## Conclusion
* `p` lies outside `E`
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.excludesPoint_sound {E : Ellipsoid 𝕋 n} {p a : Vec 𝕋 n} {s : 𝕋}
    (h : E.excludesPoint p a s = true) : toRealVec p ∉ E.construct := by -- --- PROOF ---
  unfold Ellipsoid.excludesPoint at h
  split_ifs at h with hs
  intro hp
  -- the point's reading is at most the bound, and strictly above it
  have hle := (E.boundDot (c := rowLin (fun (_ : Fin 1) => a) 0) a (fun _ => rfl) s
    (toReal_le_of_le hs)).le _ hp
  have hlt := toReal_lt_of_ltStrict h
  have hd := dotDown_le a p
  have hc : rowLin (fun (_ : Fin 1) => a) 0 (toRealVec p)
      = ∑ k, toReal (a k) * toReal (p k) := rfl
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
