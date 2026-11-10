here = fileparts(fileparts(mfilename('fullpath'))); addpath(here); addpath([here '/em']);
R('encl', 'cd("/home/ladnert/CORA/contSet/@zonotope"); try, encloseMany({zonotope([0;0],eye(2)),zonotope([1;1],eye(2))},[1;0]); out="ran"; catch ME, out=char(ME.message + " @ " + ME.stack(1).name + ":" + ME.stack(1).line); end; cd("/tmp");');
