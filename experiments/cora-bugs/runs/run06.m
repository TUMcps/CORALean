here = fileparts(fileparts(mfilename('fullpath'))); addpath(here); addpath([here '/em']);
R('dbg1', 'E=ellipsoid(eye(2)); P=polygon(E); V=P.vertices_(); out=sprintf(''nV=%d first=%s second=%s area=%g'',size(V,2),mat2str(V(:,1)'',6),mat2str(V(:,2)'',6),area(P.set));');
R('dbg2', 'E=ellipsoid(eye(2)); P=polygon(E); Q=polygon(E); u=union(P.set,Q.set); out=sprintf(''A1=%.17g Au=%.17g'',area(P.set),area(u));');
R('dbg3', 'E=ellipsoid(eye(2)); P=polygon(E); out=sprintf(''contains with tol 1e-6: %d ; isequal(P,polygon(E))=%d'',contains(P,E,''exact'',1e-6),isequal(P,polygon(E)));');
R('polygon isIntersecting2', 'E=ellipsoid(eye(2)); P0=polygon(E); V=P0.vertices_(); a=V(:,10); b=V(:,11); m=(a+b)/2; z=m/norm(m); r=1e-7; P=polygon(z(1)+[-r r r -r],z(2)+[-r -r r r]); out=sprintf(''z=%s dist-to-chord=%g  isIntersecting=%d  contains(E,z)=%d'',mat2str(z'',6),1-norm(m),isIntersecting(P,E),contains(E,z));');
R('pg eq', 'P1=polygon([0 1 1 0 -1 -1],[0 1 -1 0 -1 1]); out=[num2str(size(P1.vertices_(),2)) mat2str(P1.vertices_())];');
