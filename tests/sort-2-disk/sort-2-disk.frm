#-

#: MaxNumberSize 10K
#: MaxTermSize 150K
#: SmallSize 200M
#: LargeSize 600M
#: ScratchSize 7300M
#: HideSize 1M

On fewerstats,0;
Off threadstats;
On humanstats;
On sortverbose;

#include ../sort-2-large/sort-2-test.h

#ifndef `DIFFICULTY'
	#define DIFFICULTY "1"
#endif

#if `DIFFICULTY' == 1
	#define TERMS "12000"
#else
	#define TERMS "15000"
#endif

#call sort2test(`TERMS',4)

.end
