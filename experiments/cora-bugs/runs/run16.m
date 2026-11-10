here = fileparts(fileparts(mfilename('fullpath'))); addpath(here); addpath([here '/em']);
% polytope compact_: the aligned-row and the 1-D merge claims, at the types that reach them
R('compact aligned zero row', 'P=polytope([],[],[0 0;1 0],[0;1]); Q=compact(P,''aligned''); out=sprintf(''Ae=%s empty=%d'',mat2str(Q.Ae),representsa(Q,''emptySet''));');
R('compact Ae zero row', 'P=polytope([],[],[0 0;1 0],[0;1]); Q=compact(P,''Ae''); out=sprintf(''Ae=%s empty=%d'',mat2str(Q.Ae),representsa(Q,''emptySet''));');
R('compact aligned zero row b=0', 'P=polytope([],[],[0 0;1 0],[0;0]); Q=compact(P,''aligned''); out=sprintf(''Ae=%s be=%s fullspace=%d'',mat2str(Q.Ae),mat2str(Q.be),representsa(Q,''fullspace''));');
R('compact all antialigned', 'P=polytope([],[],[2;-2],[1;-1]); Q=compact(P,''all''); out=sprintf(''Ae=%s be=%s'',mat2str(Q.Ae),mat2str(Q.be));');
R('compact all duplicate', 'P=polytope([],[],[2;2],[1;1]); Q=compact(P,''all''); out=sprintf(''Ae=%s be=%s'',mat2str(Q.Ae),mat2str(Q.be));');
R('vertices 1D duplicate', 'P=polytope([],[],[2;2],[1;1]); out=mat2str(vertices(P));');
R('vertices 1D offsets 0 and 1', 'out=mat2str(vertices(polytope([],[],[1;1],[1;0])));');
R('representsa emptySet offsets 0 and 1', 'out=num2str(representsa(polytope([],[],[1;1],[1;0]),''emptySet''));');
R('vertices 1D antialigned', 'P=polytope([],[],[2;-2],[1;-1]); out=mat2str(vertices(P));');
% polytope mldivide: the result for further inputs, and the filterOut it feeds
R('mldivide P2 disjoint', 'r=mldivide(polytope([1;-1],[2;0]),polytope(1,-5)); out=sprintf(''A=%s fullspace=%d'',mat2str(r.A),representsa(r,''fullspace''));');
R('mldivide 2D', 'B=[1 0;-1 0;0 1;0 -1]; r=mldivide(polytope(B,[1;0;1;0]),polytope(B,[3;-1;3;-1])); out=sprintf(''A=%s fullspace=%d'',mat2str(r.A),representsa(r,''fullspace''));');
R('filterOut', 'Z={zonotope(0.5,0.5),zonotope(1.5,0.5)}; r=filterOut(Z); out=num2str(numel(r));');
R('filterOut equal cells', 'Z={zonotope(0.5,0.5),zonotope(0.5,0.5)}; r=filterOut(Z); out=num2str(numel(r));');
R('filterOut chebyball', 'out=num2str(exist(''chebyball''));');
% conZonotope supportFunc_: the recursion and its entry points
R('cZ supportFunc public', 'out=num2str(supportFunc(conZonotope(0,1,0,1),1,''upper''));');
R('cZ supportFunc A=0 b=0', 'out=num2str(supportFunc_(conZonotope(0,1,0,0),1,''upper''));');
R('cZ interval', 'out=mat2str(interval(conZonotope(0,1,0,1)));');
R('cZ contains', 'out=num2str(contains(conZonotope(0,1,0,1),0));');
R('cZ representsa emptySet', 'out=num2str(representsa(conZonotope(0,1,0,1),''emptySet''));');
% polygon isequal: the constructor splits a repeated vertex; isequal fails on a multi-part polygon
R('polygon pinched', 'P1=polygon([0 1 1 0 -1 -1],[0 1 -1 0 -1 1]); out=mat2str(P1.vertices_());');
R('polygon isequal(P,P) pinched', 'P1=polygon([0 1 1 0 -1 -1],[0 1 -1 0 -1 1]); out=num2str(isequal(P1,P1));');
R('polygon isequal(P,P) holes', 'H=polygon([0 4 4 0],[0 0 4 4]); G=polygon([1 1 3 3],[1 3 3 1]); M=H\G; out=num2str(isequal(M,M));');
R('polygon isequal near-repeat', 'P1=polygon([0 1 1 1e-9 -1 -1],[0 1 -1 0 -1 1]); P2=polygon([1e-9 -1 -1 0 1 1],[0 -1 1 0 1 -1]); out=sprintf(''isequal=%d, same start after removeCollinearPoints: %d'',isequal(P1,P2,1e-8),isequal(vertices_(removeCollinearPoints(P1,1e-8)),vertices_(removeCollinearPoints(P2,1e-8))));');
% zonotope contains_ sampling:dual: the undefined variable, and the scaling with Z2 repaired to Z
R('sampling:dual', 'out=num2str(contains(zonotope([0;0],2*eye(2)),ellipsoid(eye(2),[0;1.5]),''sampling:dual''));');
R('sampling:dual Z2->Z', '[res,cert,sc]=priv_zonotopeContainment_ellipsoidSamplingDual(ellipsoid(eye(2),[0;1.5]),zonotope([0;0],2*eye(2)),1e-6,100,true); out=sprintf(''res=%d scaling=%g (true scaling 1.25)'',res,sc);');
R('zonotope contains point container', 'out=num2str(contains(zonotope([0;0]),zonotope([0;0],[1;0])));');
% zonotope enclosePoints 'maiga': a single point (r = 0), and the cloud of the note
R('maiga single point', 'Z=zonotope.enclosePoints([1;2],''maiga''); out=mat2str(Z.G);');
R('maiga cloud 1', 'Z=zonotope.enclosePoints([1 -1 0;-1 1 0],''maiga''); out=mat2str(Z.G);');
R('maiga cloud 2', 'X=[1 -1;-1 1]; [U,~]=svd(X); out=sprintf(''dot(u,r)=%g'',dot(U(:,1),[1;1]));');
% conPolyZono contains_: a witness whose extended set is full-dimensional, so that 'approx' decides
R('cPZ contains', 'cPZ=conPolyZono(0,[1 1],[1 0;0 1],1,-0.5,[0;1]); out=sprintf(''set=%s; p=1: %d, p=0.2: %d, p=-1: %d, p=-0.5: %d'',mat2str([infimum(interval(cPZ)) supremum(interval(cPZ))]),contains(cPZ,1,''approx''),contains(cPZ,0.2,''approx''),contains(cPZ,-1,''approx''),contains(cPZ,-0.5,''approx''));');
