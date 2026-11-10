here = fileparts(fileparts(mfilename('fullpath'))); addpath(here); addpath([here '/em']);
R('mldiv1', 'P1=polytope([1;-1],[2;0]); P2=polytope([1;-1],[3;-1]); r=mldivide(P1,P2); out=sprintf(''%s ; isequal(r,P1\P1-ish)=%d  vertices %s'',class(r),0,mat2str(vertices(r)));');
R('mldiv2', 'P1=polytope([1;-1],[2;0]); P2=polytope([1;-1],[3;-1]); r=mldivide(P1,P2); out=sprintf(''A=%s b=%s'',mat2str(r.A),mat2str(r.b));');
R('compact aligned', 'P=polytope([],[],[0 0;1 0;0 1],[0;1;1]); Q=compact(P); out=sprintf(''Ae=%s be=%s'',mat2str(Q.Ae),mat2str(Q.be));');
R('compact aligned2', 'P=polytope([],[],[0 0;1 0],[0;1]); Q=compact(P); out=sprintf(''Ae=%s be=%s empty=%d'',mat2str(Q.Ae),mat2str(Q.be),representsa(Q,''emptySet''));');
R('compact aligned3', 'P=polytope([1 0;0 1;-1 0;0 -1],[1;1;1;1],[0 0;1 0],[0;1]); Q=compact(P); out=sprintf(''Ae=%s be=%s'',mat2str(Q.Ae),mat2str(Q.be));');
R('compact 1D', 'P=polytope([],[],[2;2],[1;1]); Q=compact(P,''all''); out=sprintf(''Ae=%s be=%s'',mat2str(Q.Ae),mat2str(Q.be));');
R('polytope isequal2', 'P1=polytope([1;1;-1],[1;1;0]); out=sprintf(''A=%s'',mat2str(P1.A)); P2=polytope(-1,0);');
R('polytope isequal3', 'P1=polytope([1 0;1 0;-1 0;0 1;0 -1],[1;1;0;1;0]); P2=polytope([-1 0;0 1;0 -1],[0;1;0]); out=num2str(isequal(P1,P2));');
