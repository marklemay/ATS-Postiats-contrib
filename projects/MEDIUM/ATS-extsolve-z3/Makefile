##
## ATS-extsolve-z3:
## Solving ATS-constraints with Z3
##

######
##
## Author: Hongwei Xi
## Authoremail: gmhwxiATgmailDOTcom
##
## Start time: May, 2015
##
######

CC=gcc

######

ifdef PATSHOME
  PATSHOMEQ="$(PATSHOME)"
else
ifdef ATSHOME
  PATSHOMEQ="$(ATSHOME)"
else
  PATSHOMEQ="/usr/local/lib/ats2-postiats"
endif
endif

######

ifdef PATSHOMERELOC
  PATSHOMERELOCQ="$(PATSHOMERELOC)"
else
ifdef ATSHOMERELOC
  PATSHOMERELOCQ="$(ATSHOMERELOC)"
else
  PATSHOMERELOCQ="/usr/local/lib/ats2-postiats"
endif
endif

######

PATSCC=$(PATSHOMEQ)/bin/patscc
PATSOPT=$(PATSHOMEQ)/bin/patsopt

######

all::

######
#
CFLAGS :=
CFLAGS += -DATS_MEMALLOC_LIBC
#
CFLAGS2 :=
CFLAGS2 +=-DATS_MEMALLOC_LIBC
CFLAGS2 +=-I${PATSHOMERELOC}/contrib
CFLAGS2 +=-I${PATSHOMERELOC}/contrib/SMT
CFLAGS2 += $(shell pkg-config --cflags json-c)
#
######

EXTRA_CFLAGS :=

######

PATSCC2=$(PATSCC) $(CFLAGS2) $(EXTRA_CFLAGS)

######

LDFLAGS :=
LDFLAGS += $(shell pkg-config --libs json-c)
LDFLAGS +=-lz3
LDFLAGS +=-lgc

######

INCLUDE :=
INCLUDE += -I$(PATSHOMEQ)
INCLUDE += -I$(PATSHOMEQ)/ccomp/runtime

######

PATSOLVE=./.ATS-extsolve

######

SOURCES_SATS= \
  $(PATSOLVE)/patsolve_cnstrnt.sats \
  $(PATSOLVE)/patsolve_parsing.sats \

######

SOURCES_CATS= \
  $(PATSOLVE)/patsolve_cnstrnt_dats.c \
  $(PATSOLVE)/patsolve_parsing_dats.c \

######

SOURCES_DATS :=
SOURCES_DATS += patsolve_z3_main.dats
SOURCES_DATS += patsolve_z3_mylib.dats
SOURCES_DATS += patsolve_z3_commarg.dats
SOURCES_DATS += patsolve_z3_solving.dats

######

TARGETS_DATS_O = \
  $(patsubst %.dats, %_dats.o, $(SOURCES_DATS))

######
#
all:: \
patsolve_z3
patsolve_z3: \
$(TARGETS_DATS_O); \
$(PATSCC2) -O2 -o $@ \
  $(SOURCES_SATS) $(SOURCES_CATS) $(TARGETS_DATS_O) $(LDFLAGS)
#
cleanall:: ; $(RMF) patsolve_z3
#
######

%_dats.o: %.dats; $(PATSCC2) -c $<

######
#
-include .depend
#
depend:: ; $(RMF) .depend
#
ifeq ("$(strip $(SOURCES_SATS))","")
else
depend:: ; $(PATSOPT) --output-a .depend --depgen -s $(SOURCES_SATS)
endif
ifeq ("$(strip $(SOURCES_DATS))","")
else
depend:: ; $(PATSOPT) --output-a .depend --depgen -d $(SOURCES_DATS)
endif
#
######
#
PATSOLVE_source=\
$(PATSHOMERELOC)/projects/MEDIUM/ATS-extsolve
#
pkgreloc:: ; \
$(CPF) $(PATSOLVE_source)/patsolve_cnstrnt.sats $(PATSOLVE)/.
pkgreloc:: ; \
$(CPF) $(PATSOLVE_source)/patsolve_parsing.sats $(PATSOLVE)/.
pkgreloc:: ; \
$(CPF) $(PATSOLVE_source)/CATS/patsolve_cnstrnt_dats.c $(PATSOLVE)/.
pkgreloc:: ; \
$(CPF) $(PATSOLVE_source)/CATS/patsolve_parsing_dats.c $(PATSOLVE)/.
#
######

build:: pkgreloc
build:: patsolve_z3

######

testall:: all
testall:: cleanall

######

CPF=cp -f
RMF=rm -f

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.o
clean:: ; $(RMF) *_?ats.c

######

cleanall:: clean
cleanall:: ; $(RMF) .depend

######

## end of [Makefile] ##
