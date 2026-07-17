#-

#: TermsInSmall 6300K
#: SmallSize 1G
#: ScratchSize 300M
#: HideSize 1M

On fewerstats,0;
Off threadstats;
On humanstats;
On sortverbose;

#include ../sort-2-large/sort-2-test.h

#call sort2test(2500,4)

.end
