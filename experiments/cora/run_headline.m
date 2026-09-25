function run_headline(configPath, scheme, outDir, reps)
% run_headline - runs CORA's `linearSys.reach` on the headline spiral, at
%    scheme (a) ('wrapping-free') or (b) ('standard', CORA's recursive
%    algorithm [1]) -- the MATLAB twin of `lake exe bench headline-a`/`-b`,
%    reading the SAME config JSON. Scheme (b) also exports the time-point
%    sets besides the time-interval ones, as `Bench.Registry`'s
%    `exp2-timepoint` does on the Lean side.
%
%    `A = [[a, b], [-b, a]]`, no input (`linearSys(A)`), `R0 = zonotope(c, G)`,
%    `options.timeStep`, `options.taylorTerms = eta`, `options.zonotopeOrder =
%    rho`, reduction 'girard' (CORA's default). `options.linAlg` is the one
%    setting that picks the scheme: see `experiments/README.md` for why
%    'wrapping-free' is (a) and 'standard' is (b), read from
%    `contDynamics/@linearSys/reach.m`.
%
% Syntax:
%    run_headline(configPath, scheme, outDir, reps)
%
% Inputs:
%    configPath - path to a headline config JSON file
%    scheme     - 'a' or 'b'
%    outDir     - results root, e.g. 'experiments/results'
%    reps       - repetitions to time (default: the config's own `reps`)
%
% References:
%    [1] A. Girard, "Reachability of uncertain linear systems using
%        zonotopes" in Hybrid Systems: Computation and Control,
%        ser. LNCS 3414. Springer, 2005, pp. 291-305.

% Authors:       Tobias Ladner
% Written:       25-September-2026

if nargin < 3 || isempty(outDir)
    outDir = 'experiments/results';
end

cfg = loadHeadlineConfig(configPath);
if nargin < 4 || isempty(reps)
    reps = cfg.reps;
end

if strcmp(scheme, 'a')
    linAlg = 'wrapping-free';
    experiment = 'headline-a';
elseif strcmp(scheme, 'b')
    linAlg = 'standard';
    experiment = 'headline-b';
else
    error('run_headline:badScheme', 'scheme must be ''a'' or ''b'', not %s', scheme);
end

A = [cfg.a, cfg.b; -cfg.b, cfg.a];
sys = linearSys(A);

params.R0 = zonotope(cfg.x0c, cfg.x0G);
params.tStart = 0;
params.tFinal = cfg.steps * cfg.dt;

options.timeStep = cfg.dt;
options.taylorTerms = cfg.eta;
options.zonotopeOrder = cfg.rho;
options.reductionTechnique = 'girard';
options.linAlg = linAlg;

samples = zeros(1, reps);
for r = 1:reps
    tic;
    R = reach(sys, params, options);
    samples(r) = toc;
end
medianSec = median(samples);

[~, name, ~] = fileparts(configPath);
outBase = fullfile(outDir, name, experiment, 'cora');

intRecs = recordsFromSet(R.timeInterval.set, R.timeInterval.time, true);
writeRunFiles(outBase, experiment, linAlg, cfg, samples, medianSec, intRecs);

if strcmp(scheme, 'b')
    ptRecs = recordsFromSet(R.timePoint.set, R.timePoint.time, false);
    writeRunFiles([outBase '-timepoint'], experiment, linAlg, cfg, samples, medianSec, ptRecs);
end

fprintf('%s: wrote %s.json/.csv (config %s, median %.6g s over %d rep(s))\n', ...
    experiment, outBase, name, medianSec, reps);

end
