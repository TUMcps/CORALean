import CORALean.ContDynamics.NonlinearSys.Operations.GainOrder

/-!
# A method has zero abstraction error exactly when its gain order is infinite

The sentence `[1, Def. 6]` closes with: `R` yields zero abstraction error if and
only if `q = ∞`, because by `[1, (35)]` the error vanishes exactly when every
coefficient `‖Aᵖ(h)G(h)‖₁,ᵢ` does, which by `[1, Lemma 3]` is every `a⁽ᵖ⁾ᵢ`
being zero.

`hconv` is `[1, Lemma 3]`'s own convention — a coefficient of order `⊤` has a
zero leading vector — and is a hypothesis rather than a field on `gainOrderDim`
because it is a fact about where the two families came from, not about what the
infimum means. Without it a single order-`⊤` coefficient with a nonzero vector
would put `⊤` into the set and leave the infimum `⊤` while the error is not
zero, so the theorem would be false.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `[1, Def. 6]`: the gain order is `∞` exactly when every coefficient of the
expansion vanishes. -/
theorem gainOrder_eq_top_iff {q : ℕ → Fin n → ℕ∞} {a : ℕ → Fin n → Vec ℝ m}
    (hconv : ∀ p i, q p i = ⊤ → a p i = 0) :
    gainOrder q a = ⊤ ↔ ∀ p i, a p i = 0 := by -- --- PROOF ---
  rw [gainOrder, iInf_eq_top]
  constructor
  · intro h p i
    by_contra hpi
    -- a nonzero coefficient has a finite order by `hconv`, so it puts a finite `j` in the set
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 fun htop => hpi (hconv p i htop)
    have hmem : ((p + k : ℕ) : ℕ∞) ∈ {j : ℕ∞ | ∃ p : ℕ, (p : ℕ∞) + q p i = j ∧ a p i ≠ 0} :=
      ⟨p, by rw [Nat.cast_add, hk], hpi⟩
    have hle : gainOrderDim q a i ≤ ((p + k : ℕ) : ℕ∞) := sInf_le hmem
    rw [h i, top_le_iff] at hle
    exact ENat.coe_ne_top (p + k) hle
  · intro h i
    -- every coefficient being zero leaves the set empty, and `sInf ∅ = ⊤`
    have : {j : ℕ∞ | ∃ p : ℕ, (p : ℕ∞) + q p i = j ∧ a p i ≠ 0} = ∅ := by
      ext j
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      exact fun p hp => hp.2 (h p i)
    rw [gainOrderDim, this, sInf_empty]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
