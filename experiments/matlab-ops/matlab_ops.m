function matlab_ops()
% MATLAB results for inputs.json: built-in routines and plain sequential loops, as hex bit patterns.
in = jsondecode(fileread('inputs.json'));
h = @(c) hex2num(char(c));                        % hex strings -> doubles
v = h(in.v1e4); w = h(in.w1e4); c = h(in.cancel);
out = struct();
out.sum_v_builtin = num2hex(sum(v));
out.sum_v_loop = num2hex(seqsum(v));
out.sum_cancel_builtin = num2hex(sum(c));
out.sum_cancel_loop = num2hex(seqsum(c));
out.dot_vw_builtin = num2hex(v' * w);
out.dot_vw_loop = num2hex(seqdot(v, w));
for n = [100 500]
    A = reshape(h(in.(sprintf('A%d', n))), n, n)';  % row-major input
    B = reshape(h(in.(sprintf('B%d', n))), n, n)';
    C = A * B;
    L = zeros(n);
    for i = 1:n
        for j = 1:n
            L(i, j) = seqdot(A(i, :)', B(:, j));
        end
    end
    out.(sprintf('mtimes%d_builtin', n)) = cellstr(num2hex(reshape(C', [], 1)));
    out.(sprintf('mtimes%d_loop', n)) = cellstr(num2hex(reshape(L', [], 1)));
end
out.matlab_version = version;
out.blas = version('-blas');
fid = fopen('matlab_results.json', 'w'); fwrite(fid, jsonencode(out)); fclose(fid);
end

function s = seqsum(x)
% left-to-right summation, one rounding per addition
s = 0;
for k = 1:numel(x)
    s = s + x(k);
end
end

function s = seqdot(x, y)
% left-to-right dot product, separate rounding of product and sum (no fused multiply-add)
s = 0;
for k = 1:numel(x)
    p = x(k) * y(k);
    s = s + p;
end
end
