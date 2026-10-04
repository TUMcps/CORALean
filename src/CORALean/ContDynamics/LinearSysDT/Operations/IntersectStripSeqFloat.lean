import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import CORALean.ContSet.Zonotope.Float.Operations.IntersectStrip

/-!
# The strips taken one at a time, in floats

`LinearSysDT.intersectStripSeqFloat`: the strips `|C x - y| ≤ φ` met one after the other,
[1, Eq. 3], strip `i` by `Zonotope.intersectStrip` at one row and the gain column `i` of `Λ`
evaluated at the zonotope it meets, as the real `intersectStripSeq`. Soundness is
`intersectStripSeqFloat_outer`.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The strips of `C`, `φ`, `y` met one after the other, strip `i` at the gain column `i` of `Λ`
evaluated at the zonotope it meets. -/
def LinearSysDT.intersectStripSeqFloat (C : Mat 𝕋 p n) (φ y : Vec 𝕋 p)
    (Λ : Zonotope 𝕋 n → Mat 𝕋 n p) (Z : Zonotope 𝕋 n) : Zonotope 𝕋 n :=
  (List.finRange p).foldl
    (fun X i =>                                                  -- X̂_{k/i} from X̂_{k/i-1}
      let c_i : Mat 𝕋 1 n := Matrix.of fun _ => C i              -- the row c_iᵀ
      let l_i : Mat 𝕋 n 1 := Matrix.of fun r _ => Λ X r i        -- the gain λ_i
      Zonotope.intersectStrip c_i (fun _ => φ i) (fun _ => y i) l_i X)
    Z                                                            -- X̂_{k/0}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
