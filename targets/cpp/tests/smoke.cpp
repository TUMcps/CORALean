// Smoke test: the rounding mode reaches the hardware, and each operation keeps
// the shape and the enclosure its Lean counterpart promises.
//
// This is not the differential test against ../../c; see ../README.md.
//
// Authors:       Tobias Ladner
// Written:       16-August-2026
// Last update:   ---
// Last revision: ---

#include <cstdio>

#include "binary64.hpp"
#include "zonotope.hpp"

using namespace cora;

int main() {
  RoundUpGuard guard;
  if (!roundingIsUp()) {
    std::printf("FAIL: rounding mode not set\n");
    return 1;
  }
  int failures = 0;
  auto check = [&](const char* what, bool ok) {
    std::printf("%-22s %s\n", what, ok ? "ok" : "FAIL");
    if (!ok) ++failures;
  };

  // Multiplication must straddle. 0.1*0.1 is inexact; 1.0*x would not be, and
  // would pass under round-to-nearest too.
  const double lo = FloatOps<double>::mulDown(0.1, 0.1);
  const double hi = FloatOps<double>::mulUp(0.1, 0.1);
  check("mulDown < mulUp", lo < hi);

  // A negative operand must still round outward; mulDown negates the left one.
  check("mulDown neg operand",
        FloatOps<double>::mulDown(-0.1, 0.1) < FloatOps<double>::mulUp(-0.1, 0.1));
  check("addDown < addUp",
        FloatOps<double>::addDown(0.1, 0.2) < FloatOps<double>::addUp(0.1, 0.2));

  // Centre 5, one generator 3, box [0, 2]  ->  hull [2, 10].
  Zonotope<double> Z{{5.0}, Mat<double>(1, 1, 3.0), Interval<double>{{0.0}, {2.0}}};
  const Interval<double> I = Z.interval();
  check("interval [2, 10]", I.inf[0] == 2.0 && I.sup[0] == 10.0);

  // absorbError spends n generators to empty the box, and must not shrink the set.
  const Zonotope<double> A = Z.absorbError();
  const Interval<double> IA = A.interval();
  check("absorbError count", A.numGenerators() == Z.numGenerators() + Z.dim());
  check("absorbError encloses", IA.inf[0] <= I.inf[0] && IA.sup[0] >= I.sup[0]);

  Zonotope<double> W{{0.0, 0.0}, Mat<double>(2, 3, 1.0),
                     Interval<double>{{-1.0, -1.0}, {1.0, 1.0}}};
  W.G(0, 0) = 2.0;
  W.G(1, 2) = 4.0;
  const Interval<double> IW = W.interval();

  const Split part{{0}, {1, 2}};
  check("split is a partition", part.isValid(W.numGenerators()));

  // q + n generators, not q + n + n: the two diagonal blocks merge.
  const Zonotope<double> R = W.reduceAndAbsorb(part);
  check("reduceAndAbsorb count", R.numGenerators() == part.left.size() + W.dim());
  const Interval<double> IR = R.interval();
  check("reduceAndAbsorb encl.", IR.inf[0] <= IW.inf[0] && IR.sup[0] >= IW.sup[0] &&
                                     IR.inf[1] <= IW.inf[1] && IR.sup[1] >= IW.sup[1]);

  const Zonotope<double> Red = W.reduce(part);
  const Interval<double> IRed = Red.interval();
  check("reduce count", Red.numGenerators() == part.left.size() + W.dim());
  check("reduce encloses", IRed.inf[0] <= IW.inf[0] && IRed.sup[0] >= IW.sup[0] &&
                               IRed.inf[1] <= IW.inf[1] && IRed.sup[1] >= IW.sup[1]);

  // Generators concatenate exactly, so the count is h + k.
  check("plus count", W.plus(W).numGenerators() == 2 * W.numGenerators());

  // mtimes pays into the box rather than into new generators.
  Mat<double> M(2, 2, 0.0);
  M(0, 0) = 1.0;
  M(0, 1) = 1.0 / 3.0;
  M(1, 1) = 2.0;
  const Zonotope<double> Mz = Zonotope<double>::mtimes(M, W);
  check("mtimes count", Mz.numGenerators() == W.numGenerators());
  check("mtimes widens box",
        (Mz.E.sup[0] - Mz.E.inf[0]) >= (W.E.sup[0] - W.E.inf[0]));

  std::printf("\n%s\n", failures == 0 ? "all ok" : "FAILURES");
  return failures == 0 ? 0 : 1;
}
