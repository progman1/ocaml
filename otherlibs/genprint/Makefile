#**************************************************************************
#*                                                                        *
#*                                 OCaml                                  *
#*                                                                        *
#*            Xavier Leroy, projet Cristal, INRIA Rocquencourt            *
#*                                                                        *
#*   Copyright 1999 Institut National de Recherche en Informatique et     *
#*     en Automatique.                                                    *
#*                                                                        *
#*   All rights reserved.  This file is distributed under the terms of    *
#*   the GNU Lesser General Public License version 2.1, with the          *
#*   special exception on linking described in the file LICENSE.          *
#*                                                                        *
#**************************************************************************

# Makefile for the genprint library

LIBNAME=genprint
CAMLOBJS=genprint.cmo
CAMLOBJS_NAT=$(CAMLOBJS:.cmo=.cmx)
COMPILEROBJS=../../typing/oprint.cmo 
COMPILEROBJS_NAT=$(COMPILEROBJS:.cmo=.cmx)
EXTRACAMLFLAGS= -I ../../parsing -I ../../typing -I ../../util -I ../../bytecomp


#include ../Makefile
ROOTDIR=../..
include $(ROOTDIR)/config/Makefile
include $(ROOTDIR)/Makefile.common

CAMLRUN ?= $(ROOTDIR)/boot/ocamlrun

CAMLC=$(CAMLRUN) $(ROOTDIR)/ocamlc -nostdlib -I $(ROOTDIR)/stdlib
CAMLOPT=$(CAMLRUN) $(ROOTDIR)/ocamlopt -nostdlib \
        -I $(ROOTDIR)/stdlib
COMPFLAGS+= $(EXTRACAMLFLAGS)

# Compilation options
xCOMPFLAGS=-absname -w +a-4-9-41-42-44-45-48 -warn-error A -bin-annot -g \
          -safe-string -strict-sequence -strict-formats $(EXTRACAMLFLAGS)



all: $(LIBNAME).cma $(CMIFILES)

allopt: $(LIBNAME).cmxa $(CMIFILES)


genprint.cma: $(CAMLOBJS)
	$(CAMLC) -a -o $@ \
	         $(COMPILEROBJS) $(CAMLOBJS) $(LINKOPTS)

genprint.cmx: $(CAMLOBJS_NAT)
	$(CAMLOPT) -a -o $@ \
	         $(COMPILEROBJS_NAT) $(CAMLOBJS_NAT) $(LINKOPTS)

install:
	$(INSTALL_DATA) genprint.cmi genprint.cmti genprint.cma genprint.mli "$(INSTALL_LIBDIR)"

installopt:
	$(INSTALL_DATA) genprint.cmi genprint.cmxa "$(INSTALL_LIBDIR)"

partialclean:
	rm -f *.cm[ioaxt] *.cmti *.cmxa

clean: partialclean

.SUFFIXES: .ml .mli .cmi .cmo .cmx

.mli.cmi:
	$(CAMLC) -c $(COMPFLAGS) $<

.ml.cmo:
	$(CAMLC) -c $(COMPFLAGS) $<

.ml.cmx:
	$(CAMLOPT) -c $(COMPFLAGS) $(OPTCOMPFLAGS) $<

depend:

include .depend


