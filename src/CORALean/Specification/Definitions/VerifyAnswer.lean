module

@[expose] public section

/-!
# What a verification run concludes

Three answers, shared by `VerifyHalfspace` and `VerifyConvex`, which are
`[1, Alg. 2]` and `[1, Alg. 3 (exits)]`: a certificate of safety, a certificate that the
specification is violated, or neither found before the fuel ran out. `undecided`
is not a third verdict about the system — it says only that this run stopped,
which is the honest reading of a loop whose termination is never promised.

`violated` rather than `unsafe`, `unsafe` being a Lean keyword.

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Reachability Analysis with Support Functions". Proceedings of the 26th ACM
      International Conference on Hybrid Systems: Computation and Control,
      2023.](../../../../references/2023/wetzlinger-hscc-support-functions.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       16-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The answer of a verification run: safe, violated, or neither found before the fuel ran out. -/
inductive VerifyAnswer
  | safe
  | violated
  | undecided

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
