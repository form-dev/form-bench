#: smallsize 100M
#: largesize 500M
#: termsinsmall 2M
#: SortIOsize 200K
#: ScratchSize 116M
Off Statistics;
#ifndef `NUM'
#define NUM "14"
#endif
*On Compress gzip 6;
#message Trace of `NUM' gamma matrices in 4 dimensions
S	x,j;
CF	f;
L	FF = sum_(j,1,1000,f(j));
.sort
I	m1,...,m`NUM';
id	f(x?) = 1;
Multiply G_(1,m1,...,m`NUM');
Trace4,1;
.end
