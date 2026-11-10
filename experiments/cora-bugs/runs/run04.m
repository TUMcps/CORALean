here = fileparts(fileparts(mfilename('fullpath'))); addpath(here); addpath([here '/em']);
R('levelSet isIntersecting', 'syms x; ls=levelSet(x,x,{''==''}); out=num2str(isIntersecting(ls,interval(0,1),''approx''));');
R('levelSet isIntersecting2', 'syms x; ls=levelSet(x,x,''==''); out=num2str(isIntersecting(ls,interval(0,1),''approx''));');
