import CORALean.Examples.Bench.Rational

/-!
# `randverify`: a rational as an exact dyadic

`parseExact` of `num/den`: a rational whose reduced denominator is not a power of two is refused,
for a system entry never rounded.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench


-- =====================================  MAIN DEFINITION  ====================================== --

def ratExact (q : ℚ) : Except String ExactDyadic := parseExact s!"{q.num}/{q.den}"

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
