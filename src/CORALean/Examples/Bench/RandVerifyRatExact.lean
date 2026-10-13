import CORALean.Examples.Bench.Rational

/-!
# `randverify`: a rational as an exact dyadic

`parseExact` of `num/den`: a rational whose reduced denominator is not a power of two is refused,
for a system entry never rounded.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench


-- =====================================  MAIN DEFINITION  ====================================== --

def ratExact (q : ℚ) : Except String ExactDyadic := parseExact s!"{q.num}/{q.den}"

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
