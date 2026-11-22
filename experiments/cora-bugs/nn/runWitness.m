function out = runWitness(seed, cfg)
% runWitness - CORA's verify ('zonotack') on witness network SEED over [-1,1]^2 for the unsafe set
%    [1 -1]*y <= t, and CORA's evaluate at the sampled input xbad. CFG: 'witness' (the options of
%    CORA.cpp's witness search, which crash here), 'v1' (them with every approximation error a
%    generator: no interval center), 'v2' (three errors as generators, so an interval center, and
%    heuristics without gradients), 'v2-input' (v2 with input splits only).
[W, b, t, xbad] = witnessNet(seed);
L = {};
for k = 1:3
    L{end+1} = nnLinearLayer(W{k}, b{k}); %#ok<AGROW>
    if k < 3, L{end+1} = nnReLULayer(); end %#ok<AGROW>
end
o = getDefaultVNNCOMPoptions('witness');
o.nn.falsification_method = 'center';
o.nn.num_neuron_splits = 1;
o.nn.num_relu_constraints = 8;
o.nn.max_verif_iter = 200;
o.nn.train.mini_batch_size = 4;
o.nn.train.num_approx_err = 3;
if strcmp(cfg, 'v1')
    o.nn.train.num_approx_err = inf;
elseif startsWith(cfg, 'v2')
    o.nn.input_generator_heuristic = 'most-sensitive-input-radius';
    o.nn.input_split_heuristic = 'most-sensitive-input-radius';
    o.nn.neuron_split_heuristic = 'least-unstable';
    o.nn.relu_constraint_heuristic = 'least-unstable';
    if strcmp(cfg, 'v2-input')
        o.nn.num_neuron_splits = 0;
        o.nn.num_relu_constraints = 0;
    end
end
try
    res = verify(neuralNetwork(L), [0;0], [1;1], [1 -1], single(t), false, o, 60, false);
    verdict = res.str;
catch ME
    verdict = sprintf('error %s (%s line %d)', ME.message, ME.stack(1).name, ME.stack(1).line);
end
y = evaluate(neuralNetwork(L), xbad);
out = sprintf('%s: verify returns %s; evaluate at xbad = %s is %s, y1 - y2 = %.6g <= t = %.6g', ...
    cfg, verdict, mat2str(xbad', 6), mat2str(y', 6), [1 -1]*y, t);
end
