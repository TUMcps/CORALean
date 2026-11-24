here = fileparts(fileparts(mfilename('fullpath'))); addpath(here); addpath([here '/em']);
% specification/robustness: equality constraints ignored (safe set 0<=x1<=1, x2=0; point (0.5,1))
R('specification robustness equality', ['P=polytope([1 0;-1 0],[1;0],[0 1],0); sp=specification(P,''safeSet''); r1=robustness(sp,[0.5;1]); r2=robustness(sp,[0.5;0]); r3=robustness(sp,[0.5;-3]);' ...
 'out=sprintf("safe set 0<=x1<=1, x2=0: robustness at (0.5,1) = %g, at (0.5,0) (inside) = %g, at (0.5,-3) = %g; distance of (0.5,1) to the set is 1, so -1 is correct",r1,r2,r3);']);
% specification/isequal: custom specs with different functions
R('specification isequal custom', ['a=specification(@(S) true,''custom''); b=specification(@(S) false,''custom''); out=sprintf("isequal(custom true, custom false) = %d",isequal(a,b));']);
R('specification isequal parallel locations', ['a=specification(interval(0,1),''safeSet'',{1,2}); b=specification(interval(0,1),''safeSet'',{1,3}); out=sprintf("isequal with locations {1,2} vs {1,3} = %d",isequal(a,b));']);
R('specification isequal parallel locations 2', ['a=specification(interval(0,1),''safeSet'',{1,2}); b=specification(interval(0,1),''safeSet'',{1,2}); out=sprintf("isequal(identical {1,2}) = %d",isequal(a,b));']);
% specification/check on a reachSet without timeInterval
R('specification check reachSet timePoint', ['tp.set={zonotope([1;1],0.1*eye(2)),zonotope([2;2],0.1*eye(2))}; tp.time={0,1}; Rs=reachSet(tp); sp=specification(interval([0;0],[5;5]),''safeSet''); out=sprintf("isempty(Rs.timeInterval)=%d",isempty(Rs.timeInterval)); out=out+sprintf("; timePoint sets: %d, both inside the safe set; ",numel(Rs.timePoint.set)); try, v=check(sp,Rs); out=out+sprintf("check(sp,Rs) = %d",v); catch ME, out=out+sprintf("check(sp,Rs) errors in %s line %d: %s",ME.stack(1).name,ME.stack(1).line,ME.message); end']);
% taylm asin (already recorded)
R('taylm asin', ['T=asin(taylm(interval(-1,1),7)); I=interval(T); out=sprintf("[%g,%g], pi/2 = %g",I.inf,I.sup,pi/2);']);
% stl/modelCheckTrace on a power
R('stl modelCheckTrace power', ['x=stl(''x'',1); t=(0:0.1:1)''; xt=0.5*ones(numel(t),1); out=sprintf("%d",modelCheckTrace(x(1)^2 < 1,xt,t));']);
R('stl modelCheckTrace no power', ['x=stl(''x'',1); t=(0:0.1:1)''; xt=0.5*ones(numel(t),1); out=sprintf("%d",modelCheckTrace(x(1)+x(1) < 3,xt,t));']);
