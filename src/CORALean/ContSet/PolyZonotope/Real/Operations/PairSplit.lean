import CORALean.Global.Partition

/-!
# `PolyZonotope.pairSplit`

The split of `Fin m` naming `i` and `j` on the right, in that order, and every other index on
the left: the form `relaxExpMulti` takes the two generators it merges in, as line 6 of `[1, Alg. 2]`
names them.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The permutation carrying the last two indices onto `i` and `j`. -/
def PolyZonotope.aux_pairPerm {m : ℕ} (i j : Fin (m + 2)) : Equiv.Perm (Fin (m + 2)) :=
  (Equiv.swap (Fin.natAdd m 1) (Equiv.swap (Fin.natAdd m 0) i j)).trans
    (Equiv.swap (Fin.natAdd m 0) i)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The split naming `i` and `j` on the right, in that order, and every other index on the
left. -/
def PolyZonotope.pairSplit {m : ℕ} (h2 : 2 ≤ m) (i j : Fin m) :
    Split (Fin m) into (Fin (m - 2)) ⊕ (Fin 2) :=
  (Partition.split (m - 2) 2).reindex
    ((finCongr (Nat.sub_add_cancel h2).symm).trans
      (PolyZonotope.aux_pairPerm (finCongr (Nat.sub_add_cancel h2).symm i)
        (finCongr (Nat.sub_add_cancel h2).symm j)).symm)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
