// Worked examples with hand-computed answers.
//
// The other suites check properties over random data, which says an operation
// is sound without saying what it returns. These pin down the actual numbers on
// cases small enough to verify by reading, so a change in behaviour shows up as
// a changed value rather than as a still-satisfied inequality.
//
// Every case here is exact in binary64, so the expected values are equalities.
//
// Authors:       Tobias Ladner
// Written:       16-August-2026
// Last update:   ---
// Last revision: ---

#include "binary64.hpp"
#include "check.hpp"
#include "zonotope.hpp"

using namespace cora;
using namespace cora::test;

namespace {

Mat<double> mat(std::size_t rows, std::size_t cols, std::initializer_list<double> entries) {
  Mat<double> M(rows, cols);
  auto it = entries.begin();
  for (std::size_t i = 0; i < rows; ++i)
    for (std::size_t j = 0; j < cols; ++j) M(i, j) = *it++;
  return M;
}

}  // namespace

int main() {
  RoundUpGuard guard;
  check("rounding mode is up", roundingIsUp());

  // Directed rounding reaches the hardware. 0.1 * 0.1 is inexact; 1.0 * x would
  // pass under round-to-nearest too and so would prove nothing.
  check("mulDown < mulUp",
        FloatOps<double>::mulDown(0.1, 0.1) < FloatOps<double>::mulUp(0.1, 0.1));
  check("negative operand too",
        FloatOps<double>::mulDown(-0.1, 0.1) < FloatOps<double>::mulUp(-0.1, 0.1));
  check("addDown < addUp",
        FloatOps<double>::addDown(0.1, 0.2) < FloatOps<double>::addUp(0.1, 0.2));

  // Centre 5, one generator 3, box [0, 2]. Hull is 5 +- 3, then the box:
  // [5 - 3 + 0, 5 + 3 + 2] = [2, 10]. Same answer as the Dyadic example in Lean.
  {
    const Zonotope<double> Z{{5.0}, mat(1, 1, {3.0}), Interval<double>{{0.0}, {2.0}}};
    const Interval<double> I = Z.interval();
    check("hull is [2, 10]", I.inf[0] == 2.0 && I.sup[0] == 10.0);
  }

  // absorbError trades the box for one generator per coordinate. Box [-2, 4]
  // has midpoint 1 and radius 3, so the result is centre 1 with generator 3 —
  // and denotes exactly what it did before.
  {
    const Zonotope<double> Z{{0.0}, mat(1, 0, {}), Interval<double>{{-2.0}, {4.0}}};
    const Zonotope<double> A = Z.absorbError();
    check("absorbError centre", A.c[0] == 1.0);
    check("absorbError generator", A.numGenerators() == 1 && A.G(0, 0) == 3.0);
    check("absorbError box empty", A.E.inf[0] == 0.0 && A.E.sup[0] == 0.0);
    const Interval<double> I = A.interval();
    check("absorbError hull", I.inf[0] == -2.0 && I.sup[0] == 4.0);
  }

  // plus concatenates generators and adds centres: centre 11, generators 2 and
  // 5, so the hull is 11 +- 7.
  {
    const Zonotope<double> Z1{{1.0}, mat(1, 1, {2.0}), Interval<double>{{0.0}, {0.0}}};
    const Zonotope<double> Z2{{10.0}, mat(1, 1, {5.0}), Interval<double>{{0.0}, {0.0}}};
    const Zonotope<double> P = Z1.plus(Z2);
    check("plus centre", P.c[0] == 11.0);
    check("plus generators", P.numGenerators() == 2 && P.G(0, 0) == 2.0 && P.G(0, 1) == 5.0);
    const Interval<double> I = P.interval();
    check("plus hull", I.inf[0] == 4.0 && I.sup[0] == 18.0);
  }

  // reduce replaces the dropped generators by one box generator per coordinate.
  // Dropping columns 1 and 2 of [[1, 2, 3], [0, 4, 0]] leaves the kept column
  // and a diagonal of the dropped row sums: 2 + 3 = 5 and 4 + 0 = 4.
  {
    const Zonotope<double> Z{{0.0, 0.0}, mat(2, 3, {1.0, 2.0, 3.0, 0.0, 4.0, 0.0}),
                             Interval<double>{{0.0, 0.0}, {0.0, 0.0}}};
    const Split part{{0}, {1, 2}};
    const Zonotope<double> R = Z.reduce(part);
    check("reduce count", R.numGenerators() == 3);
    check("reduce keeps column", R.G(0, 0) == 1.0 && R.G(1, 0) == 0.0);
    check("reduce diagonal", R.G(0, 1) == 5.0 && R.G(1, 2) == 4.0);
    check("reduce off-diagonal", R.G(0, 2) == 0.0 && R.G(1, 1) == 0.0);
  }

  // mtimes keeps the generator count; the rounding goes into the box. With an
  // exact matrix the box stays empty, which is what makes 1/3 below visible.
  {
    const Zonotope<double> Z{{1.0}, mat(1, 2, {2.0, 4.0}), Interval<double>{{0.0}, {0.0}}};
    const Zonotope<double> T = Zonotope<double>::mtimes(mat(1, 1, {3.0}), Z);
    check("mtimes count", T.numGenerators() == 2);
    check("mtimes centre", T.c[0] == 3.0);
    check("mtimes generators", T.G(0, 0) == 6.0 && T.G(0, 1) == 12.0);
    check("exact map keeps box", T.E.inf[0] == 0.0 && T.E.sup[0] == 0.0);
  }

  // When the map rounds, the box must open up to hold what that cost. Note the
  // operands have to make the *product* inexact: (1/3) * 1 is exact, since 1/3
  // is only inexact as a literal, so a centre of 1 here would prove nothing.
  {
    const Zonotope<double> Z{{7.0}, mat(1, 1, {5.0}), Interval<double>{{0.0}, {0.0}}};
    const Mat<double> M = mat(1, 1, {1.0 / 3.0});
    check("the product is inexact",
          FloatOps<double>::mulDown(1.0 / 3.0, 7.0) < FloatOps<double>::mulUp(1.0 / 3.0, 7.0));

    const Zonotope<double> T = Zonotope<double>::mtimes(M, Z);
    check("rounding opens box", T.E.inf[0] < 0.0 || T.E.sup[0] > 0.0);

    // Z denotes [2, 12], so the image is [2/3, 4] and the hull must cover it.
    const Interval<double> I = T.interval();
    check("rounded map encloses", I.inf[0] <= 2.0 / 3.0 && I.sup[0] >= 4.0);
  }

  return report("examples");
}
