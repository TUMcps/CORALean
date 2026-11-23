% run19: nnActivationLayer/evaluateZonotopeBatch under an interval center, at layer level and in
% neuralNetwork/verify ('zonotack'). Run it once per variant:
% `matlab -batch "repair = {}; run('experiments/cora-bugs/runs/run19.m')"`, then with
% repair = {'offset'} and {'dummy', 'stale', 'center', 'offset'}: 'offset' puts nn/patchOffset.m's
% copy of @nnActivationLayer first on the path, the others are nn/patchVerify.m's repairs of verify.m.
% CHECKS_ENABLED is shadowed to false (nn/CHECKS_ENABLED.m).
here = fileparts(fileparts(mfilename('fullpath'))); addpath(here); addpath([here '/nn']);
if ~exist('repair', 'var'), repair = {}; end
vrep = setdiff(repair, {'offset'}, 'stable');
if any(strcmp(repair, 'offset')), addpath(patchOffset(), '-begin'); end
if ~isempty(vrep), addpath(patchVerify(vrep), '-begin'); end
tag = strjoin([{'stock'}, repair], '+');
% One ReLU layer after x -> (x, x, x + 3) on x in [-1, 1], one approximation error as a generator
% (neuron 1), an interval center; the error of neuron 2 stays in the center.
R(sprintf('nn activation offset %s', tag), [ ...
    'nn = neuralNetwork({nnLinearLayer([1;1;1],[0;0;3]), nnReLULayer()}); ' ...
    'o = struct(''nn'', struct(''interval_center'', true, ''train'', struct(''num_approx_err'', 1))); ' ...
    'o = nnHelper.validateNNoptions(o, true); nn.prepareForZonoBatchEval(0, o); ' ...
    '[c, G] = nn.evaluateZonotopeBatch(zeros(1,2), 1, o); ' ...
    'Z = zonotope((c(:,1)+c(:,2))/2, [G diag((c(:,2)-c(:,1))/2)]); y = nn.evaluate(0); ' ...
    'out = sprintf(''center intervals %s, generators %s; evaluate at x = 0 is %s; contains %d'', ' ...
    'mat2str(c, 4), mat2str(G, 4), mat2str(y''), contains(Z, y));']);
cases = {7, 'v2-input'; 25, 'v2-input'; 43, 'v2-input'; 5, 'v2'; 40, 'v2'; 53, 'v2'};
for i = 1:size(cases, 1)
    R(sprintf('nn verify %s seed %d %s', tag, cases{i, 1}, cases{i, 2}), ...
        sprintf('out = runWitness(%d, ''%s'');', cases{i, 1}, cases{i, 2}));
end
