import CORALean.ContDynamics.NonlinearSys.PolyAbstractionError
import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetPoint

/-!
# Narrowing a factor narrows the error with it

What the polynomialization variant buys, in one statement: re-parametrizing
factor `k` of the initial set onto a sub-interval — [1]'s `getSubset`, which is
how a set is split — re-parametrizes the *abstraction error* by the same
substitution. The error over a piece of the initial set is a piece of the error,
not the whole of it.

An interval error cannot say this. `AbstractionError`'s `L` is a set, so the same
`L` answers for every subset of `R` and splitting buys nothing on the error term;
here only `W`, the part that had to be boxed, stays put.

The proof `show`s the goal back into `L.p` and `pZ.p` before touching it: the
certificate's `Fin.cast` is at the counts `getSubset` leaves, `getSubset_point`'s
at the counts it was handed, and the two are the same map on defeq index types
but not the same term.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Real.PolyZonotope

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The certificate at a re-parametrized factor: the same substitution on both
sets, and `W` unchanged. -/
theorem PolyAbstractionError.getSubset {f : Vec ℝ n → Vec ℝ m → Vec ℝ n} {A : Mat ℝ n n}
    {B : Mat ℝ n m} {xs : Vec ℝ n} {us : Vec ℝ m} {pZ : Real.PolyZonotope (Vec ℝ n)}
    {Ba : Set (Fin pZ.p → ℝ)} {U : Set (Vec ℝ m)} {L W : Real.PolyZonotope (Vec ℝ n)}
    {hp : L.p = pZ.p} (cert : PolyAbstractionError f A B xs us pZ Ba U L hp W)
    (k : Fin pZ.p) (cen rad : ℝ) {Ba' : Set (Fin (pZ.getSubset k cen rad).p → ℝ)}
    (hBa' : ∀ b ∈ Ba', Function.update b k (cen + rad * b k) ∈ Ba) :
    PolyAbstractionError f A B xs us (pZ.getSubset k cen rad) Ba' U
      (L.getSubset (Fin.cast hp.symm k) cen rad) hp W where
  encloses b hb u hu := by
    -- the two casts agree on `k`, so the substituted entry is the same on both sides
    have hupd : Function.update (fun j : Fin L.p => b (Fin.cast hp j)) (Fin.cast hp.symm k)
          (cen + rad * b (Fin.cast hp (Fin.cast hp.symm k)))
        = fun j : Fin L.p => Function.update b k (cen + rad * b k) (Fin.cast hp j) :=
      funext fun j => by
        rcases eq_or_ne j (Fin.cast hp.symm k) with rfl | hj
        · exact (Function.update_self _ _ _).trans
            (Function.update_self k (cen + rad * b k) b).symm
        · -- `Fin.cast` is injective, so an index missing `k` on one side misses it on both
          have hne : Function.update b k (cen + rad * b k) (Fin.cast hp j) = b (Fin.cast hp j) := by
            apply Function.update_of_ne
            intro h
            exact hj (Fin.val_inj.mp (by simpa using congrArg Fin.val h))
          rw [Function.update_of_ne hj, hne]
    rw [Real.PolyZonotope.getSubset_point pZ k cen rad b,
      Real.PolyZonotope.getSubset_point L (Fin.cast hp.symm k) cen rad _]
    -- back into `L.p` and `pZ.p`, where `hupd` and the certificate are both stated
    show f (pZ.point (Function.update b k (cen + rad * b k))) u
        - (f xs us + A *ᵥ (pZ.point (Function.update b k (cen + rad * b k)) - xs)
          + B *ᵥ (u - us))
        - L.point (Function.update (fun j : Fin L.p => b (Fin.cast hp j)) (Fin.cast hp.symm k)
            (cen + rad * b (Fin.cast hp (Fin.cast hp.symm k)))) ∈ W.construct
    rw [hupd]
    exact cert.encloses _ (hBa' b hb) u hu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
