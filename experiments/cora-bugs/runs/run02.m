here = fileparts(fileparts(mfilename('fullpath'))); addpath(here); addpath([here '/em']);
R('ell priv', 'E1=ellipsoid(diag([1,0])); E2=ellipsoid(diag([0.25,0]),[0;1]); cd(''/home/ladnert/CORA/contSet/@ellipsoid/private''); [r,c,s]=priv_containsEllipsoid(E1,E2,1e-10); cd(''/tmp''); out=mat2str([r c s]);');
R('ell contains', 'E1=ellipsoid(diag([1,0])); E2=ellipsoid(diag([0.25,0]),[0;1]); out=num2str(contains(E1,E2));');
R('ell rep', 'E1=ellipsoid(diag([1,0])); E2=ellipsoid(diag([0.25,0]),[0;1]); out=mat2str([representsa(E1,''point'') representsa(E2,''point'')]);');
R('cpz minkDiff', 'r=minkDiff(conPolyZono(0,1,1,1,1,2),zonotope(0,1)); out=[class(r) '' '' num2str(contains(r,0,''approx''))];');
R('cZ supp', 'cZ=conZonotope(0,1,0,1); out=[mat2str(cZ.A) mat2str(cZ.b) '' '' num2str(supportFunc_(cZ,1,''upper''))];');
