module

public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# The sets `representsa_` is asked about

The values of `type` in `@stlInterval/representsa_.m` that are modelled: `'emptySet'`,
`'stlInterval'`, `'point'` and `'origin'`. The other types delegate, for a closed interval, to
`representsa(interval(I),type,...)`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

inductive STLInterval.RepresentsaType
  | emptySet
  | stlInterval
  | point
  | origin

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
