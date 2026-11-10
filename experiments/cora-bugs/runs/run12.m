here = fileparts(fileparts(mfilename('fullpath'))); addpath(here); addpath([here '/em']);
R('encloseMany copy', 'try, encloseMany({zonotope([0;0],eye(2)),zonotope([1;1],eye(2))},[1;0]); out="ran"; catch ME, out=char(ME.message + " @ " + ME.stack(1).name + ":" + ME.stack(1).line); end');
R('splitFirstGen', 'try, r=splitFirstGen(zonotope([0;0],[1 0 1;0 1 1])); out=class(r); catch ME, out=char(ME.message + " @ " + ME.stack(1).name + ":" + ME.stack(1).line); end');
R('splitFirstGen2', 'try, r=splitFirstGen(zonotope([0;0],[1 0 1;0 1 1]),3); out=class(r); catch ME, out=char(ME.message + " @ " + ME.stack(1).name + ":" + ME.stack(1).line); end');
R('tensorMult', 'Z=zonotope([0;0],eye(2)); M=cell(2,1); M{1}=eye(2); M{2}=eye(2); try, r=tensorMultiplication(Z,M); out=class(r); catch ME, out=char(ME.message + " @ " + ME.stack(1).name + ":" + ME.stack(1).line); end');
R('zoo times', 'z=zoo(interval(1,2),{"interval"}); try, r=z.*z; out=class(r); catch ME, out=char(ME.message + " @ " + ME.stack(1).name + ":" + ME.stack(1).line); end');
R('zoo rdivide', 'z=zoo(interval(1,2),{"interval"}); try, r=z./z; out=class(r); catch ME, out=char(ME.message + " @ " + ME.stack(1).name + ":" + ME.stack(1).line); end');
R('zoo mtimes', 'z=zoo(interval(1,2),{"interval"}); try, r=z*z; out=class(r); catch ME, out=char(ME.message + " @ " + ME.stack(1).name + ":" + ME.stack(1).line); end');
R('zB reduceCombined', 'zB=zonoBundle({zonotope([0;0],rand(2,6)),zonotope([0;0],rand(2,6))}); try, r=reduceCombined(zB,"methC"); out=class(r); catch ME, out=char(ME.message + " @ " + ME.stack(1).name + ":" + ME.stack(1).line); end');
