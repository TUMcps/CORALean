function commit = getCoraCommit()
% getCoraCommit - the checked-out CORA's git commit, found from wherever
%    `linearSys` resolves on the MATLAB path -- so pinning is read from the
%    actual tree a run used, not typed in by hand. "unknown" if `git` is not
%    on PATH, the tree is not a git checkout, or `linearSys` is not found.
%
% Syntax:
%    commit = getCoraCommit()
%
% Outputs:
%    commit - the commit hash, trimmed, or "unknown"

% Authors:       Tobias Ladner
% Written:       25-September-2026

commit = 'unknown';
loc = which('linearSys');
if isempty(loc)
    return
end
% `linearSys.m` sits at <CORA root>/contDynamics/@linearSys/linearSys.m.
coraRoot = fileparts(fileparts(fileparts(loc)));
[status, out] = system(sprintf('git -C %s rev-parse HEAD', coraRoot));
if status == 0
    commit = strtrim(out);
end

end
