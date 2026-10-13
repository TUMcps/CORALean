
/-!
# What a verification run concludes

Three answers, shared by `VerifyHalfspace` and `VerifyConvex`, which are
`[1, Alg. 2]` and `[1, Alg. 3 (exits)]`: a certificate of safety, a certificate that the
specification is violated, or neither found before the fuel ran out. `undecided`
is not a third verdict about the system — it says only that this run stopped,
which is the honest reading of a loop whose termination is never promised.

`violated` rather than `unsafe`, `unsafe` being a Lean keyword.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Sonnet 5
-- Written:       16-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

inductive VerifyAnswer
  | safe
  | violated
  | undecided

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
