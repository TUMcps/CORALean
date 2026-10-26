module

public import CORALean.ContDynamics.Conform.Definitions.PassesBF

@[expose] public section

/-!
# A conformant system passes the brute-force check

If the sets `R m k` the check is run against enclose the system's reachable output sets, a system
that is reachset conformant on the test suite passes: contrapositively, a measurement outside a
computed set proves the system is not conformant (CORA's `res = false`). The converse is false:
`R` is an outer set, so passing shows only that each measurement lies in an enclosure, not in the
reachable set itself.

## Inputs
* `sys` – plant
* `X0` – initial uncertainty set
* `W` – disturbance set
* `V` – noise set
* `T` – test cases
* `K` – horizon
* `R` – computed reachable sets

## Hypotheses
* `hR` – computed sets enclose the reachable outputs
* `hconf` – the system is conformant

## Conclusion
* the brute-force check passes
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Pointwise

variable {n p q : ℕ} {M S : Type} [ContSet S (Vec ℝ q)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Conform.passesBF_of_isConformant (sys : Conform.Plant n p q) (X0 W : Set (Vec ℝ n))
    (V : Set (Vec ℝ q)) (T : M → Conform.TestCase n p q) (K : ℕ) (R : M → ℕ → S)
    (hR : ∀ m, ∀ k ≤ K, sys.reachOutExact ({(T m).x0} + X0) (T m).u W V k ⊆ construct (R m k))
    (hconf : sys.IsConformant X0 W V T K) : Conform.PassesBF T K R :=
  fun m k hk => hR m k hk (hconf m k hk)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
