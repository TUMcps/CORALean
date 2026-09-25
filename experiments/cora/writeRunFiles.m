function writeRunFiles(outBase, experiment, scheme, cfg, samplesSec, medianSec, recs)
% writeRunFiles - writes <outBase>.json and <outBase>.csv, the same schema
%    `CORALean.Bench.Output.writeRun` writes: `meta` (experiment, scheme,
%    type "double", format "binary64", significand_bits 53, the config
%    echoed back, timings) beside `sets`, one record per step. E is always
%    zero width -- see `recordsFromSet`.
%
% Syntax:
%    writeRunFiles(outBase, experiment, scheme, cfg, samplesSec, medianSec, recs)
%
% Inputs:
%    outBase     - output path with no extension; parent dir is created
%    experiment  - "headline-a" or "headline-b"
%    scheme      - "wrapping-free" or "standard", CORA's own `options.linAlg`
%    cfg         - struct from loadHeadlineConfig
%    samplesSec  - vector of repetition timings, in seconds
%    medianSec   - their median
%    recs        - struct array from recordsFromSet

% Authors:       Tobias Ladner
% Written:       25-September-2026

[outDir, ~, ~] = fileparts(outBase);
if ~isempty(outDir) && ~exist(outDir, 'dir')
    mkdir(outDir);
end

meta.experiment = experiment;
meta.scheme = scheme;
meta.type = 'double';
% MATLAB's `double` is IEEE binary64, the same label the Lean side's
% `--format binary64`/native `Float` runs carry, so the three are directly
% comparable in the paper's tables.
meta.format = 'binary64';
meta.significand_bits = 53;
meta.config = cfg.raw;
meta.eta = cfg.eta;
meta.gitCommit = 'n/a (CORA run, not CORALean)';
meta.coraCommit = getCoraCommit();
meta.matlabVersion = version();
meta.timingsNs = round(samplesSec * 1e9);
meta.medianNs = round(medianSec * 1e9);

sets = struct('k', {}, 't0', {}, 't1', {}, 'c', {}, 'G', {}, 'E', {});
for i = 1:numel(recs)
    sets(i).k = recs(i).k;
    sets(i).t0 = recs(i).t0;
    sets(i).t1 = recs(i).t1;
    sets(i).c = recs(i).c;
    sets(i).G = recs(i).G;
    sets(i).E = struct('inf', recs(i).Einf, 'sup', recs(i).Esup);
end

doc.meta = meta;
doc.sets = sets;
fid = fopen([outBase '.json'], 'w');
fwrite(fid, jsonencode(doc, 'PrettyPrint', true));
fclose(fid);

fid = fopen([outBase '.csv'], 'w');
fprintf(fid, 'k,t,width0,width1,Eradius0,Eradius1\n');
for i = 1:numel(recs)
    w = 2 * sum(abs(recs(i).G), 2);
    fprintf(fid, '%d,%.9g,%.9g,%.9g,0,0\n', recs(i).k, recs(i).t1, w(1), w(2));
end
fclose(fid);

end
