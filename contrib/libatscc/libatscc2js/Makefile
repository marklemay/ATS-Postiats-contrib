#
# For generating libatscc2js
#

######

PATSOPT=$(PATSHOME)/bin/patsopt
ATSCC2JS=$(PATSHOME)/bin/atscc2js

######

CAT=cat
CPF=cp -f
RMF=rm -f
SCPR=scp -r

######

all::
all_in_one::

######
#
all:: ; \
$(PATSOPT) -d ./DATS/basics.dats | \
$(ATSCC2JS) -o ./output/DATS/basics_dats.js -i
#
all:: ; \
$(PATSOPT) -d ./DATS/list.dats | \
$(ATSCC2JS) -o ./output/DATS/list_dats.js -i
all:: ; \
$(PATSOPT) -d ./DATS/option.dats | \
$(ATSCC2JS) -o ./output/DATS/option_dats.js -i
all:: ; \
$(PATSOPT) -d ./DATS/stream.dats | \
$(ATSCC2JS) -o ./output/DATS/stream_dats.js -i
all:: ; \
$(PATSOPT) -d ./DATS/gvalue.dats | \
$(ATSCC2JS) -o ./output/DATS/gvalue_dats.js -i
all:: ; \
$(PATSOPT) -d ./DATS/intrange.dats | \
$(ATSCC2JS) -o ./output/DATS/intrange_dats.js -i
#
all:: ; \
$(PATSOPT) -d ./DATS/reference.dats | \
$(ATSCC2JS) -o ./output/DATS/reference_dats.js -i
#
all:: ; \
$(PATSOPT) -d ./DATS/arrayref.dats | \
$(ATSCC2JS) -o ./output/DATS/arrayref_dats.js -i
all:: ; \
$(PATSOPT) -d ./DATS/matrixref.dats | \
$(ATSCC2JS) -o ./output/DATS/matrixref_dats.js -i
all:: ; \
$(PATSOPT) -d ./DATS/gmatrixref.dats | \
$(ATSCC2JS) -o ./output/DATS/gmatrixref_dats.js -i
#
######
#
all:: ; \
$(PATSOPT) -d ./DATS/ML/list0.dats | \
$(ATSCC2JS) -o ./output/DATS/ML/list0_dats.js -i
all:: ; \
$(PATSOPT) -d ./DATS/ML/array0.dats | \
$(ATSCC2JS) -o ./output/DATS/ML/array0_dats.js -i
#
######
#
all:: ; \
$(PATSOPT) -d ./DATS/Bacon.js/baconjs_ext.dats | \
$(ATSCC2JS) -o ./output/DATS/Bacon.js/baconjs_ext_dats.js -i
#
######

all_in_one:: libatscc2js_all
all_in_one:: libatscc2js_baconjs_all

######
#
DATE=/bin/date
ECHO=/bin/echo -en
#
libatscc2js_all:: ; \
$(ECHO) | $(CAT) - >libatscc2js_all.js
libatscc2js_all:: ; \
$(ECHO) '/*\n' | $(CAT) - >>libatscc2js_all.js
libatscc2js_all:: ; \
$(ECHO) 'Time of Generation:\n' | $(CAT) - >>libatscc2js_all.js
libatscc2js_all:: ; \
$(DATE) | $(CAT) - >>libatscc2js_all.js
libatscc2js_all:: ; \
$(ECHO) '*/\n\n' | $(CAT) - >>libatscc2js_all.js
#
libatscc2js_all:: ; \
$(CAT) >>libatscc2js_all.js \
CATS/basics_cats.js \
CATS/integer_cats.js \
CATS/bool_cats.js \
CATS/float_cats.js \
CATS/string_cats.js \
CATS/gvalue_cats.js \
CATS/JSmath_cats.js \
CATS/JSdate_cats.js \
CATS/JSarray_cats.js \
CATS/JSglobal_cats.js \
CATS/Ajax/Ajax_cats.js \
CATS/HTML/canvas-2d/canvas2d_cats.js
#
libatscc2js_all:: ; \
$(CAT) >>libatscc2js_all.js \
output/DATS/basics_dats.js \
output/DATS/list_dats.js \
output/DATS/option_dats.js \
output/DATS/stream_dats.js \
output/DATS/gvalue_dats.js \
output/DATS/intrange_dats.js \
output/DATS/reference_dats.js \
output/DATS/arrayref_dats.js \
output/DATS/matrixref_dats.js \
output/DATS/gmatrixref_dats.js \
output/DATS/ML/list0_dats.js \
output/DATS/ML/array0_dats.js
#
libatscc2js_all:: ; \
$(ECHO) '\n/* ****** ****** */\n' | $(CAT) - >>libatscc2js_all.js
libatscc2js_all:: ; \
$(ECHO) '\n/* end of [libatscc2js_all.js] */\n' | $(CAT) - >>libatscc2js_all.js
#
######
#
libatscc2js_baconjs_all:: ; \
$(CAT) \
>libatscc2js_baconjs_all.js \
CATS/Bacon.js/baconjs_cats.js \
output/DATS/Bacon.js/baconjs_ext_dats.js
#
######
#
upload_source:: ; \
$(SCPR) \
basics_js.sats \
staloadall.hats \
CATS SATS DATS \
ats-hwxi,ats-lang@web.sourceforge.net:htdocs/LIBRARY/contrib/libatscc/libatscc2js/.
#
upload_libatscc2js:: ; \
$(SCPR) \
libatscc2js_all.js \
libatscc2js_baconjs_all.js \
ats-hwxi,ats-lang@web.sourceforge.net:htdocs/LIBRARY/contrib/libatscc/libatscc2js/.
#
######

clean:: ; $(RMF) *~ */*~

######

cleanall:: clean
cleanall:: ; $(RMF) libatscc2js_all.js

######

###### end of [Makefile] ######
