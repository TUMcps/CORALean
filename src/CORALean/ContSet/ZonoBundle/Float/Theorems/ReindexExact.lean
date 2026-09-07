import CORALean.ContSet.ZonoBundle.Float.Operations.Reindex
import CORALean.ContSet.Zonotope.Float.Theorems.ReindexExact

/-!
# `ZonoBundle.reindex` is exactly the relabelled bundle

`Zonotope.reindex_exact` needs no hypothesis on `e`; a bundle intersects several
members, and an image commutes with `⋂ i` only one way without more. The reverse
is `Set.image_iInter`, which wants `reindexLin e` *bijective*, not merely
injective: at `k = 0` the bundle already denotes `univ` in `Vec ℝ n`, and only a
surjective map carries that to `univ` in `Vec ℝ m` rather than to its range.

An equivalence supplies both halves, so the hypothesis is discharged inline from
`e` and the statement stays as unconditional as `Zonotope`'s.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.reindex_exact (e : Fin m ≃ Fin n) (zB : ZonoBundle 𝕋 n) :
    (zB.reindex e).construct = reindexLin e '' zB.construct := by -- --- PROOF ---
  -- `e`'s own cancellation laws move straight through the coordinate swap.
  have hl : Function.LeftInverse (reindexLin e.symm) (reindexLin e) :=
    fun x => funext fun i => by simp [reindexLin]
  have hr : Function.LeftInverse (reindexLin e) (reindexLin e.symm) :=
    fun x => funext fun i => by simp [reindexLin]
  have hb : Function.Bijective (reindexLin e) := ⟨hl.injective, hr.surjective⟩
  simp only [ZonoBundle.construct, ZonoBundle.reindex, Set.image_iInter hb]
  exact Set.iInter_congr fun i => Zonotope.reindex_exact e (zB.Z i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
