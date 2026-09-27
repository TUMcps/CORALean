function run_all_cora(outDir)
% run_all_cora - runs `run_headline` for every `experiments/config/headline_*.json`
%    at both schemes -- the CORA-side counterpart of `experiments/run_all.sh`,
%    kept a separate, documented step since it needs MATLAB and CORA on the
%    path, neither of which the Lean side's one-command reproduction can
%    assume.
%
%    A relative `outDir` (the default included) is resolved against this
%    file's own directory by `run_headline` itself, robust to the working
%    directory having drifted since the caller's `cd` -- see that file's
%    module docstring.
%
% Syntax:
%    run_all_cora(outDir)
%
% Inputs:
%    outDir - results root (default: 'experiments/results')

% Authors:       Tobias Ladner
% Written:       25-September-2026
% Last update:   27-September-2026

if nargin < 1 || isempty(outDir)
    outDir = 'experiments/results';
end

here = fileparts(mfilename('fullpath'));
repoRoot = fileparts(fileparts(here));
configs = dir(fullfile(repoRoot, 'experiments', 'config', 'headline_*.json'));

for i = 1:numel(configs)
    configPath = fullfile(configs(i).folder, configs(i).name);
    run_headline(configPath, 'a', outDir);
    run_headline(configPath, 'b', outDir);
end

end
