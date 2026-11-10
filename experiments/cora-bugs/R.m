function R(id, code)
% evaluate the string CODE (may assign variable out); print "RES|id|text". Errors are caught.
warning('off','all');
out = '';
try
    evalc(code);   % assignments in code land in this workspace
catch ME
    out = ['ERROR(' ME.identifier '): ' strtok(ME.message, newline)];
end
if ~ischar(out), out = mat2str(out); end
out = regexprep(out, '<[^>]*>', '');
fprintf('RES|%s|%s\n', id, strrep(out, newline, ' '));
end
