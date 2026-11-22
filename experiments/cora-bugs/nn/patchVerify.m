function d = patchVerify(repairs)
% patchVerify - a copy of CORA's @neuralNetwork in a temporary folder with REPAIRS (a cell of 'dummy',
%    'stale', 'center') applied to its verify.m; put the folder first on the path to use it.
d = tempname; mkdir(d);
copyfile(fullfile(CORAROOT, 'nn', '@neuralNetwork'), fullfile(d, '@neuralNetwork'));
f = fullfile(d, '@neuralNetwork', 'verify.m');
s = fileread(f);
for i = 1:numel(repairs)
    switch repairs{i}
        case 'dummy'  % the children of a dummy split are refined, not counted as verified
            s = rep(s, 'isVerified = any(isnan(li),1) | any(isnan(ui),1) | isDummySplit;', ...
                'isVerified = any(isnan(li),1) | any(isnan(ui),1); isDummySplit(:) = false;');
        case 'stale'  % after iteration 1 the split and ReLU rows keep only the input factors
            s = rep(s, sprintf('        [d,C] = aux_scaleAndOffsetZonotope(d,C,-bc,br);\n'), ...
                sprintf(['        [d,C] = aux_scaleAndOffsetZonotope(d,C,-bc,br);\n' ...
                '        if refIter == 2, k0 = size(Gx,2); d = d + reshape(sum(abs(C(:,k0+1:end,:)),2),size(d)); C(:,k0+1:end,:) = 0; end\n']));
            s = rep(s, sprintf('            [bt,At] = aux_scaleAndOffsetZonotope(bt,At,-bc,br);\n'), ...
                sprintf(['            [bt,At] = aux_scaleAndOffsetZonotope(bt,At,-bc,br);\n' ...
                '            if refIter == 2, k0 = size(Gx,2); bt = bt + reshape(sum(abs(At(:,k0+1:end,:)),2),size(bt)); At(:,k0+1:end,:) = 0; end\n']));
        case 'center'  % no split bound is remembered under an interval center
            s = rep(s, 'if ~isempty(nrSplitIdx) && size(bs,2) == 1', ...
                'if ~isempty(nrSplitIdx) && size(bs,2) == 1 && ~options.nn.interval_center');
    end
end
fid = fopen(f, 'w'); fwrite(fid, s); fclose(fid);
end

function s = rep(s, a, b)
assert(numel(strfind(s, a)) == 1, 'patchVerify: the text to replace is not unique');
s = strrep(s, a, b);
end
