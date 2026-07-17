#-

#: MaxNumberSize 10K
#: MaxTermSize 50K
#: SmallSize 100M
#: LargeSize 3G
#: ScratchSize 1300M
#: HideSize 1M

On fewerstats,0;
Off threadstats;
On humanstats;
On sortverbose;

#include ../sort-2-large/sort-2-test.h

#call sort2test(6000,4)

.end
