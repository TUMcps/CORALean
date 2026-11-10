here = fileparts(fileparts(mfilename('fullpath'))); addpath(here); addpath([here '/em']);
R('m1', 'P=conPolyZono(0,1,1,1,1,2); r=minkDiff(P,zonotope(0,1)); out=sprintf(''c=%s G=%s E=%s A=%s b=%s EC=%s'',mat2str(r.c),mat2str(r.G),mat2str(r.E),mat2str(r.A),mat2str(r.b),mat2str(r.EC));');
R('m2', 'P=conPolyZono(0,1,1,1,1,2); r=minkDiff(P,zonotope(0,1)); out=num2str(representsa(r,''emptySet''));');
R('m3', 'P=conPolyZono(0,1,1,1,1,2); r=minkDiff(P,zonotope(0,1)); out=sprintf(''GI=%s id=%s'',mat2str(r.GI),mat2str(r.id));');
R('contains point', 'p=conPolyZono(0,1,1,1,0,1); out=num2str(contains(p,0));');
