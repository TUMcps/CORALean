function recs = recordsFromSet(setCell, timeCell, isInterval)
% recordsFromSet - turns one of a reachSet's `.set`/`.time` cell pairs into
%    the harness's per-step record shape (k, t0, t1, c, G, E), E always zero
%    width -- CORA's zonotope carries no error box, unlike the float layer's.
%
% Syntax:
%    recs = recordsFromSet(setCell, timeCell, isInterval)
%
% Inputs:
%    setCell    - reachSet.timeInterval.set or .timePoint.set: cell array of
%                 zonotope
%    timeCell   - the matching .time: cell array of interval (time-interval)
%                 or of scalar double (time-point)
%    isInterval - true for timeInterval.time (interval, .inf/.sup), false for
%                 timePoint.time (a scalar)
%
% Outputs:
%    recs - struct array, one entry per step, fields k, t0, t1, c, G, Einf,
%           Esup, kept as doubles here -- writeRunFiles.m is where every one
%           is formatted, at full (%.17g) precision.

% Authors:       Tobias Ladner
% Written:       25-September-2026
% Last update:   27-September-2026

n = numel(setCell);
if n == 0
    % `recs(0) = ...` is not valid MATLAB -- an explicit 0x0 struct array
    % instead, so a scheme with no time-point set (or none requested) writes
    % `sets_tp: []` rather than erroring.
    recs = struct('k', {}, 't0', {}, 't1', {}, 'c', {}, 'G', {}, 'Einf', {}, 'Esup', {});
    return
end
recs(n) = struct('k', 0, 't0', 0, 't1', 0, 'c', [], 'G', [], 'Einf', [], 'Esup', []);
for k = 1:n
    Z = setCell{k};
    if isInterval
        t0 = timeCell{k}.inf;
        t1 = timeCell{k}.sup;
    else
        t0 = timeCell{k};
        t1 = timeCell{k};
    end
    recs(k).k = k - 1;
    recs(k).t0 = t0;
    recs(k).t1 = t1;
    recs(k).c = Z.c;
    recs(k).G = Z.G;
    recs(k).Einf = zeros(size(Z.c));
    recs(k).Esup = zeros(size(Z.c));
end

end
