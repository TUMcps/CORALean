here = fileparts(fileparts(mfilename('fullpath'))); addpath(here); addpath([here '/em']);
R('expm', 'M=intervalMatrix(-1,0); try, r=expmDifferentAlgorithms(M,2,0); out=sprintf("[%g]",r.int.inf); catch ME, out=char(ME.message + " @ " + ME.stack(1).name + ":" + ME.stack(1).line+" / "+ME.stack(2).name+":"+ME.stack(2).line); end');
R('expm2', 'M=intervalMatrix(-1,0); try, r=expmTaylorHornerScaling(M,2,0); out=sprintf("[%g]",r.int.inf); catch ME, out=char(ME.message + " @ " + ME.stack(1).name + ":" + ME.stack(1).line+" / "+ME.stack(2).name+":"+ME.stack(2).line); end');
R('exp std', 'M=intervalMatrix(-1,0); try, r=expm(M,2); out=sprintf("[%g,%g]",r.int.inf,r.int.sup); catch ME, out=char(ME.message + " @ " + ME.stack(1).name + ":" + ME.stack(1).line); end');
