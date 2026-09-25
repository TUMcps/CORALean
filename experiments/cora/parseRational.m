function v = parseRational(s)
% parseRational - reads one of the config's exact rational strings ("3/64",
%    "-1/32", "1") into a MATLAB double.
%
%    The denominator in every value the headline config carries is a power of
%    two (Lean's ExactDyadic.parseExact rejects anything else), so num/den is
%    exactly representable in binary64 for the magnitudes this harness uses --
%    this file does not itself re-check that, since CORA is not where the
%    reject-on-non-representable contract is enforced; Bench/Rational.lean is.
%
% Syntax:
%    v = parseRational(s)
%
% Inputs:
%    s - a rational literal string, "m" or "m/d"
%
% Outputs:
%    v - the double it denotes

% Authors:       Tobias Ladner
% Written:       25-September-2026

parts = strsplit(s, '/');
if numel(parts) == 1
    v = str2double(parts{1});
elseif numel(parts) == 2
    v = str2double(parts{1}) / str2double(parts{2});
else
    error('parseRational:badLiteral', 'not a rational literal: %s', s);
end

end
