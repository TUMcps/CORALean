% run18: neuralNetwork/verify, refinement_method 'zonotack', on witness networks of CORA.cpp's search
% (nn/witnessNets.py writes nn/witnessNet.m; nn/runWitness.m runs one). Run it once per variant:
% `matlab -batch "repair = {}; run('experiments/cora-bugs/runs/run18.m')"`, then with
% repair = {'dummy'}, {'stale'}, {'center'}: nn/patchVerify.m applies that repair to a copy of
% verify.m. CHECKS_ENABLED is shadowed to false (nn/CHECKS_ENABLED.m).
here = fileparts(fileparts(mfilename('fullpath'))); addpath(here); addpath([here '/nn']);
if ~exist('repair', 'var'), repair = {}; end
if ~isempty(repair), addpath(patchVerify(repair), '-begin'); end
tag = strjoin([{'stock'}, repair], '+');
cases = {14, 'witness'; 10, 'v1'; 31, 'v1'; 14, 'v1'; 52, 'v1'; 5, 'v2'; 40, 'v2'; 53, 'v2'; ...
    14, 'v2'; 52, 'v2'; 7, 'v2-input'; 25, 'v2-input'; 43, 'v2-input'};
for i = 1:size(cases, 1)
    R(sprintf('nn verify %s seed %d %s', tag, cases{i, 1}, cases{i, 2}), ...
        sprintf('out = runWitness(%d, ''%s'');', cases{i, 1}, cases{i, 2}));
end
