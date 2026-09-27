function run_headline(configPath, scheme, outDir, reps)
% run_headline - runs CORA's `linearSys.reach` on the headline spiral, at
%    scheme (a) ('wrapping-free') or (b) ('standard', CORA's recursive
%    algorithm [1]) -- the MATLAB twin of `lake exe bench headline-a`/`-b`,
%    reading the SAME config JSON. Both schemes export `R.timeInterval` and
%    `R.timePoint` alike, `sets_ti`/`sets_tp` in one file, matching the Lean
%    side's schema; `sets_tp` is written `[]` if `R.timePoint` holds nothing
%    for a scheme.
%
%    `A = [[a, b], [-b, a]]`, no input (`linearSys(A)`), `R0 = zonotope(c, G)`,
%    `options.timeStep`, `options.taylorTerms = eta`, `options.zonotopeOrder =
%    rho`, reduction 'girard' (CORA's default). `options.linAlg` is the one
%    setting that picks the scheme: see `experiments/README.md` for why
%    'wrapping-free' is (a) and 'standard' is (b), read from
%    `contDynamics/@linearSys/reach.m`. The timed call is `reach` alone,
%    median over `reps` (`tic`/`toc`) -- nothing else in this file is timed.
%
%    `configPath` and `outDir` are resolved against this file's own directory
%    (`repoRoot`, from `mfilename('fullpath')`) when they are relative and do
%    not already exist relative to the current directory -- MATLAB startup
%    (a `startup.m` on the path, or CORA's own initialization) can change the
%    working directory after the caller's own `cd`, so a path resolved only
%    against `pwd` at that later point can silently miss.
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
% Last update:   27-September-2026

if nargin < 3 || isempty(outDir)
    outDir = 'experiments/results';
end

here = fileparts(mfilename('fullpath'));
repoRoot = fileparts(fileparts(here));
configPath = resolveRepoPath(repoRoot, configPath);
outDir = resolveRepoPath(repoRoot, outDir);

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

tiRecs = recordsFromSet(R.timeInterval.set, R.timeInterval.time, true);
if isprop(R, 'timePoint') && ~isempty(R.timePoint) && ~isempty(R.timePoint.set)
    tpRecs = recordsFromSet(R.timePoint.set, R.timePoint.time, false);
else
    tpRecs = recordsFromSet({}, {}, false);
end

writeRunFiles(outBase, experiment, linAlg, cfg, samples, medianSec, tiRecs, tpRecs);

fprintf('%s: wrote %s.json/.csv (config %s, %d ti, %d tp steps, median %.6g s over %d rep(s))\n', ...
    experiment, outBase, name, numel(tiRecs), numel(tpRecs), medianSec, reps);

end

function resolved = resolveRepoPath(repoRoot, p)
% resolveRepoPath - `p` unchanged if it already exists relative to the
%    current directory (or is absolute); otherwise `p` anchored at
%    `repoRoot` -- robust to the working directory having drifted since the
%    caller's own `cd` (see the module docstring).
if exist(p, 'file') || exist(p, 'dir') || isAbsolutePath(p)
    resolved = p;
    return
end
resolved = fullfile(repoRoot, p);
end

function tf = isAbsolutePath(p)
% isAbsolutePath - a leading `/` (POSIX) or `<letter>:` (Windows drive).
tf = ~isempty(p) && (p(1) == '/' || p(1) == '\' || (numel(p) >= 2 && p(2) == ':'));
end
