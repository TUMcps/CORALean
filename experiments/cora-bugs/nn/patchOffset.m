function d = patchOffset()
% patchOffset - a copy of CORA's @nnActivationLayer in a temporary folder whose evaluateZonotopeBatch
%    takes the indices of the errors without a generator (notdDimsIdx) before dDimsIdx is cut to its
%    first dn rows (CORA cuts first, so notdDimsIdx is empty); put the folder first on the path.
d = tempname; mkdir(d);
copyfile(fullfile(CORAROOT, 'nn', 'layers', 'nonlinear', '@nnActivationLayer'), fullfile(d, '@nnActivationLayer'));
f = fullfile(d, '@nnActivationLayer', 'evaluateZonotopeBatch.m');
s = fileread(f);
a = sprintf('    notdDimsIdx = dDimsIdx(dn+1:end,:);\n');
c = sprintf('    dDimsIdx = dDimsIdx(1:dn,:);\n');
assert(numel(strfind(s, a)) == 1 && numel(strfind(s, c)) == 1, 'patchOffset: the text is not unique');
s = strrep(s, a, '');
s = strrep(s, c, [a c]);
fid = fopen(f, 'w'); fwrite(fid, s); fclose(fid);
end
