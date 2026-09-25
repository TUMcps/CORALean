function cfg = loadHeadlineConfig(path)
% loadHeadlineConfig - reads one experiments/config/headline_*.json file with
%    jsondecode and turns its rational strings into doubles, the MATLAB-side
%    twin of CORALean.Bench.Config.loadConfig -- the same file, read by both.
%
% Syntax:
%    cfg = loadHeadlineConfig(path)
%
% Inputs:
%    path - path to a headline config JSON file
%
% Outputs:
%    cfg - struct with fields a, b, dt (doubles), x0c (2x1), x0G (2xh),
%          eta, rho, steps, reps (doubles/integers), raw (the decoded JSON,
%          echoed into the output's meta.config the same way the Lean side
%          echoes it)

% Authors:       Tobias Ladner
% Written:       25-September-2026

text = fileread(path);
raw = jsondecode(text);

cfg.a = parseRational(raw.system.a);
cfg.b = parseRational(raw.system.b);
cfg.dt = parseRational(raw.dt);

cfg.x0c = [parseRational(raw.x0.center{1}); parseRational(raw.x0.center{2})];

h = numel(raw.x0.generators);
G = zeros(2, h);
for j = 1:h
    row = raw.x0.generators{j};
    G(1, j) = parseRational(row{1});
    G(2, j) = parseRational(row{2});
end
cfg.x0G = G;

cfg.eta = raw.eta;
cfg.rho = raw.rho;
cfg.steps = raw.steps;
cfg.reps = raw.reps;
cfg.raw = raw;

end
