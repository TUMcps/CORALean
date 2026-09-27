function writeRunFiles(outBase, experiment, scheme, cfg, samplesSec, medianSec, tiRecs, tpRecs)
% writeRunFiles - writes <outBase>.json and <outBase>.csv, the same schema
%    `CORALean.Bench.Output.writeRunTiTp` writes: `meta` (status, experiment,
%    scheme, type "double", format "binary64", significand_bits 53, the
%    config echoed back, eta/rho/N/dt, timings, summary) beside two arrays,
%    `sets_ti` (t0 < t1) and `sets_tp` (t0 = t1) -- either may be a 0x0
%    struct array (`recordsFromSet` on an empty/absent CORA set), written as
%    `[]`. E is always zero width -- see `recordsFromSet`.
%
%    Every number is written at full (%.17g) precision, by hand, through
%    numTok/arrTok/matTok below -- `jsonencode`'s own double formatting is
%    not precision-controlled, so this file never calls it on a number, only
%    on `cfg.raw` (already all strings and integers, so lossless).
%
% Syntax:
%    writeRunFiles(outBase, experiment, scheme, cfg, samplesSec, medianSec, tiRecs, tpRecs)
%
% Inputs:
%    outBase     - output path with no extension; parent dir is created
%    experiment  - "headline-a" or "headline-b"
%    scheme      - "wrapping-free" or "standard", CORA's own `options.linAlg`
%    cfg         - struct from loadHeadlineConfig
%    samplesSec  - vector of repetition timings (the `reach` call alone), in
%                  seconds
%    medianSec   - their median
%    tiRecs      - struct array from recordsFromSet(..., true) (time-interval)
%    tpRecs      - struct array from recordsFromSet(..., false) (time-point),
%                  0x0 if CORA's `R.timePoint` held nothing for this scheme

% Authors:       Tobias Ladner
% Written:       25-September-2026
% Last update:   27-September-2026

[outDir, ~, ~] = fileparts(outBase);
if ~isempty(outDir) && ~exist(outDir, 'dir')
    mkdir(outDir);
end

% MATLAB's `double` is IEEE binary64, the same label the Lean side's
% `--format binary64`/native `Float` runs carry, so all three are directly
% comparable in the paper's tables.
metaFields = { ...
    '"status":"ok"', ...
    sprintf('"experiment":"%s"', experiment), ...
    sprintf('"scheme":"%s"', scheme), ...
    '"type":"double"', ...
    '"format":"binary64"', ...
    '"significand_bits":53', ...
    sprintf('"config":%s', jsonencode(cfg.raw)), ...
    sprintf('"eta":%d', cfg.eta), ...
    sprintf('"rho":%d', cfg.rho), ...
    sprintf('"N":%d', cfg.steps), ...
    sprintf('"dt":%s', numTok(cfg.dt)), ...
    '"gitCommit":"n/a (CORA run, not CORALean)"', ...
    sprintf('"coraCommit":"%s"', getCoraCommit()), ...
    sprintf('"matlabVersion":"%s"', version()), ...
    sprintf('"timingsNs":%s', arrTok(round(samplesSec * 1e9))), ...
    sprintf('"medianNs":%s', numTok(round(medianSec * 1e9))), ...
    sprintf('"summary":{"ti":%s,"tp":%s}', summaryTok(tiRecs), summaryTok(tpRecs)) };
metaStr = ['{' strjoin(metaFields, ',') '}'];

doc = sprintf('{"meta":%s,"sets_ti":%s,"sets_tp":%s}', metaStr, setsArrTok(tiRecs), ...
    setsArrTok(tpRecs));
fid = fopen([outBase '.json'], 'w');
fwrite(fid, doc);
fclose(fid);

fid = fopen([outBase '.csv'], 'w');
fprintf(fid, 'set,k,t0,t1,width0,width1,Eradius0,Eradius1\n');
writeCsvRows(fid, 'ti', tiRecs);
writeCsvRows(fid, 'tp', tpRecs);
fclose(fid);

end

function writeCsvRows(fid, tag, recs)
% writeCsvRows - one CSV row per record, `Eradius` columns always `0` (CORA
%    carries no error box), everything else at full (%.17g) precision.
for i = 1:numel(recs)
    w = 2 * sum(abs(recs(i).G), 2);
    fprintf(fid, '%s,%d,%s,%s,%s,%s,0,0\n', tag, recs(i).k, ...
        sprintf('%.17g', recs(i).t0), sprintf('%.17g', recs(i).t1), ...
        sprintf('%.17g', w(1)), sprintf('%.17g', w(2)));
end
end

function s = numTok(x)
% numTok - one double as a JSON number token at full (%.17g) precision, or a
%    quoted special value -- `NaN`/`Infinity`/`-Infinity` are not JSON
%    numbers, the same convention `CORALean.Bench.FloatPrint.floatToJson`
%    uses on the Lean side.
if isnan(x)
    s = '"NaN"';
elseif isinf(x)
    if x < 0
        s = '"-Infinity"';
    else
        s = '"Infinity"';
    end
else
    s = sprintf('%.17g', x);
end
end

function s = arrTok(v)
% arrTok - a 1D vector as a JSON array of numTok's.
parts = arrayfun(@numTok, v(:)', 'UniformOutput', false);
s = ['[' strjoin(parts, ',') ']'];
end

function s = matTok(M)
% matTok - a 2 x h matrix as a JSON array of its rows (each an arrTok) -- row
%    i is dimension i across every generator, the same convention
%    `CORALean.Bench.Output.stepJson`'s `G` field uses.
rows = cell(1, size(M, 1));
for i = 1:size(M, 1)
    rows{i} = arrTok(M(i, :));
end
s = ['[' strjoin(rows, ',') ']'];
end

function s = recTok(rec)
% recTok - one `sets_ti`/`sets_tp` record, `{k, t0, t1, c, G, E: {inf, sup}}`.
s = sprintf('{"k":%d,"t0":%s,"t1":%s,"c":%s,"G":%s,"E":{"inf":%s,"sup":%s}}', ...
    rec.k, numTok(rec.t0), numTok(rec.t1), arrTok(rec.c), matTok(rec.G), ...
    arrTok(rec.Einf), arrTok(rec.Esup));
end

function s = setsArrTok(recs)
% setsArrTok - `recs` (a `recordsFromSet` struct array, possibly 0x0) as a
%    JSON array of `recTok`'s, `[]` if empty.
if isempty(recs)
    s = '[]';
    return
end
parts = cell(1, numel(recs));
for i = 1:numel(recs)
    parts{i} = recTok(recs(i));
end
s = ['[' strjoin(parts, ',') ']'];
end

function s = summaryTok(recs)
% summaryTok - `recs`'s summary object, the fields
%    `CORALean.Bench.Summary.summaryJson` writes: final/max error-box
%    radius, final nominal and total hull width, and the two step markers.
%    `E` is always zero here, so the radius fields are always `0` and the two
%    markers always `null` (a zero radius never exceeds a positive
%    half-width or `1`); `{"empty": true}` on no steps at all.
if isempty(recs)
    s = '{"empty":true}';
    return
end
lastG = recs(end).G;
finalHalfW = sum(abs(lastG), 2)';
finalWidth = 2 * finalHalfW;
zero2 = [0, 0];
s = sprintf(['{"finalEradius":%s,"maxEradius":%s,"finalWidth":%s,' ...
    '"finalTotalWidth":%s,"firstErrorDominantStep":null,"firstBlowupStep":null}'], ...
    arrTok(zero2), arrTok(zero2), arrTok(finalWidth), arrTok(finalWidth));
end
