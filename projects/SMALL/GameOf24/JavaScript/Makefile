#
# A simple Makefile
#

######

NODEJS=nodejs

######

PATSCC=${PATSHOME}/bin/patscc
ATSCC2JS=${PATSHOME}/bin/atscc2js

######
#
all:: \
GameOf24_js_dats.js
#
GameOf24_js_dats.c: GameOf24_js.dats; ${PATSCC} -ccats $<
GameOf24_js_dats.js: GameOf24_js_dats.c; ${ATSCC2JS} -o $@ -i $<
#
######

regress:: ; $(NODEJS) mytest.js

######

RMF=rm -f
RMRF=rm -rf

######

CPRF=cp -rf

######
#
libatscc2js:: ; \
$(CPRF) $(PATSHOME_contrib)/contrib/libatscc/libatscc2js/CATS libatscc2js/.
libatscc2js:: ; \
$(CPRF) $(PATSHOME_contrib)/contrib/libatscc/libatscc2js/output/DATS libatscc2js/.
#
######

testall:: all
testall:: libatscc2js
testall:: regress
testall:: cleanall

######

clean:: ; $(RMF) GameOf24_js_dats.c

######

cleanall:: clean
cleanall:: ; $(RMF) GameOf24_js_dats.js
cleanall:: ; $(RMRF) libatscc2js/CATS
cleanall:: ; $(RMRF) libatscc2js/DATS

###### end of [Makefile] ######
