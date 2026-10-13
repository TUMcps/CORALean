import CORALean.ContSet.Zonotope.Real.Definitions.ColsSnoc
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The sum over generator subsets splits at the last generator

The sum behind `Zonotope.volume` runs over the subsets of `r + 1` generators that hold `n = m + 1`
of them. Those not holding the last generator are the subsets of the first `r`, and those holding
it are the `m`-subsets of the first `r` followed by it, in this order as `orderEmbOfFin` lists
them. This is the splitting [1, Sec. 6.1] uses when the strip generator `σλ` is appended last.

## References

* [1] T. Alamo, J. M. Bravo and E. F. Camacho. "Guaranteed state estimation by zonotopes".
      Automatica, 41(6):1035-1043, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Finset

variable {m r : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_orderEmbOfFin_map (S : Finset (Fin r)) (k : ℕ) (hS : S.card = k)
    (h' : (S.map Fin.castSuccEmb).card = k) :
    (S.map Fin.castSuccEmb).orderEmbOfFin h' = fun j => Fin.castSucc (S.orderEmbOfFin hS j) := by
  symm
  -- the lifted indices are in the set and increasing, which characterises the enumeration
  exact Finset.orderEmbOfFin_unique h' (fun j => by simp)
    (fun a b hab => Fin.castSucc_lt_castSucc_iff.mpr ((S.orderEmbOfFin hS).strictMono hab))

theorem aux_orderEmbOfFin_insert (T : Finset (Fin r)) (hT : T.card = m)
    (h' : (insert (Fin.last r) (T.map Fin.castSuccEmb)).card = m + 1) :
    (insert (Fin.last r) (T.map Fin.castSuccEmb)).orderEmbOfFin h' =
      Fin.snoc (α := fun _ => Fin (r+1))
        (fun j => Fin.castSucc (T.orderEmbOfFin hT j)) (Fin.last r) := by -- --- PROOF ---
  symm
  -- the lifted indices followed by `last` are in the set and increasing
  refine Finset.orderEmbOfFin_unique h' (fun j => ?_) ?_
  · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  · intro a b hab
    refine Fin.lastCases (fun hab => ?_) (fun a' hab => ?_) a hab
    · exact absurd hab (not_lt.mpr (Fin.le_last _))
    · refine Fin.lastCases (fun hab => ?_) (fun b' hab => ?_) b hab
      · simp
      · simp only [Fin.snoc_castSucc]
        exact Fin.castSucc_lt_castSucc_iff.mpr ((T.orderEmbOfFin hT).strictMono
          (Fin.castSucc_lt_castSucc_iff.mp (by simpa using hab)))

theorem aux_sum_powerset_map (g : Finset (Fin (r+1)) → ℝ) :
    ∑ t ∈ (Finset.univ.map Fin.castSuccEmb : Finset (Fin (r+1))).powerset, g t =
      ∑ S : Finset (Fin r), g (S.map Fin.castSuccEmb) := by -- --- PROOF ---
  symm
  -- a subset of the lifted indices is the image of the subset of the indices it comes from
  refine Finset.sum_bij (fun S _ => S.map Fin.castSuccEmb) (fun S _ => ?_) (fun S _ S' _ h => ?_)
    (fun t ht => ?_) (fun S _ => rfl)
  · exact Finset.mem_powerset.mpr (Finset.map_subset_map.mpr (Finset.subset_univ _))
  · exact Finset.map_injective _ h
  · obtain ⟨u, -, rfl⟩ := Finset.subset_map_iff.mp (Finset.mem_powerset.mp ht)
    exact ⟨u, Finset.mem_univ _, rfl⟩

theorem aux_sum_split (f : Finset (Fin (r+1)) → ℝ) :
    ∑ S : Finset (Fin (r+1)), f S =
      ∑ S : Finset (Fin r), f (S.map Fin.castSuccEmb) +
        ∑ S : Finset (Fin r), f (insert (Fin.last r) (S.map Fin.castSuccEmb)) := by -- --- PROOF ---
  have hu : (Finset.univ : Finset (Fin (r+1))) =
      insert (Fin.last r) (Finset.univ.map Fin.castSuccEmb) := by
    ext x; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_map, true_iff]
    rcases Fin.eq_castSucc_or_eq_last x with ⟨y, rfl⟩ | rfl
    · exact Or.inr ⟨y, trivial, rfl⟩
    · exact Or.inl rfl
  have hn : Fin.last r ∉ (Finset.univ.map Fin.castSuccEmb : Finset (Fin (r+1))) := by simp
  rw [← Finset.powerset_univ, hu, Finset.sum_powerset_insert hn, aux_sum_powerset_map,
    aux_sum_powerset_map (fun t => f (insert (Fin.last r) t))]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.volume_sum_snoc (G : Fin (r+1) → Vec ℝ (m+1)) :
    ∑ S : Finset (Fin (r+1)), (if hS : S.card = m + 1 then
        |(Matrix.of fun i k => G (S.orderEmbOfFin hS k) i : Mat ℝ (m+1) (m+1)).det| else 0) =
      ∑ S : Finset (Fin r), (if hS : S.card = m + 1 then
        |(Matrix.of fun i k => G (Fin.castSucc (S.orderEmbOfFin hS k)) i :
          Mat ℝ (m+1) (m+1)).det| else 0) +
      ∑ T : Finset (Fin r), (if hT : T.card = m then
        |(colsSnoc (fun k => G (Fin.castSucc (T.orderEmbOfFin hT k))) (G (Fin.last r))).det|
        else 0) := by -- --- PROOF ---
  -- the subsets without the last generator, then those with it
  rw [aux_sum_split]
  congr 1
  · refine Finset.sum_congr rfl fun S _ => ?_
    by_cases hS : S.card = m + 1
    · have h' : (S.map Fin.castSuccEmb).card = m + 1 := by simpa using hS
      simp only [hS, h', dif_pos, aux_orderEmbOfFin_map S _ hS h']
    · simp [hS]
  · -- the subsets with the last generator
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases hT : T.card = m
    · have h' : (insert (Fin.last r) (T.map Fin.castSuccEmb)).card = m + 1 := by
        rw [Finset.card_insert_of_notMem (by simp)]; simp [hT]
      simp only [hT, h', dif_pos, aux_orderEmbOfFin_insert T hT h']
      congr 2
      ext i k
      refine Fin.lastCases ?_ (fun k => ?_) k <;> simp [colsSnoc]
    · simp [hT]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
