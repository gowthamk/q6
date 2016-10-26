# The main Makefile, fragments shared between Makefile and Makefile.nt
include config/Makefile
# CAMLYACC ?= boot/ocamlyacc
CAMLC=ocamlc
CAMLOPT=ocamlopt
CAMLYACC=ocamlyacc
YACCFLAGS=-v --strict
YACCFLAGS=-v
CAMLLEX=ocamllex
CAMLDEP=ocamlde
DEPFLAGS=$(INCLUDES)
COMPFLAGS=-strict-sequence -principal -absname \
          -bin-annot -safe-string -strict-formats $(INCLUDES)
LINKFLAGS=

OCAMLBUILDBYTE=$(WITH_OCAMLBUILD:=.byte)
OCAMLBUILDNATIVE=$(WITH_OCAMLBUILD:=.native)

INCLUDES=-I utils -I parsing -I typing -I extraction -I driver

UTILS=utils/config.cmo utils/misc.cmo \
  utils/identifiable.cmo utils/numbers.cmo utils/arg_helper.cmo \
  utils/clflags.cmo utils/tbl.cmo utils/timings.cmo \
  utils/terminfo.cmo utils/ccomp.cmo utils/warnings.cmo \
  utils/consistbl.cmo \
  utils/strongly_connected_components.cmo

PARSING=parsing/location.cmo parsing/longident.cmo \
  parsing/docstrings.cmo parsing/ast_helper.cmo \
  parsing/syntaxerr.cmo parsing/parser.cmo \
  parsing/lexer.cmo parsing/parse.cmo parsing/printast.cmo \
  parsing/pprintast.cmo \
  parsing/ast_mapper.cmo parsing/ast_iterator.cmo parsing/attr_helper.cmo \
  parsing/builtin_attributes.cmo parsing/ast_invariants.cmo

TYPING=typing/ident.cmo typing/path.cmo \
  typing/primitive.cmo typing/types.cmo \
  typing/btype.cmo typing/oprint.cmo \
  typing/subst.cmo typing/predef.cmo \
  typing/datarepr.cmo typing/cmi_format.cmo typing/env.cmo \
  typing/typedtree.cmo typing/printtyped.cmo typing/ctype.cmo \
  typing/printtyp.cmo typing/includeclass.cmo \
  typing/mtype.cmo typing/envaux.cmo typing/includecore.cmo \
  typing/typedtreeIter.cmo typing/typedtreeMap.cmo \
  typing/tast_mapper.cmo \
  typing/cmt_format.cmo typing/untypeast.cmo \
  typing/includemod.cmo typing/typetexp.cmo typing/parmatch.cmo \
  typing/stypes.cmo typing/typedecl.cmo typing/typecore.cmo \
  typing/typeclass.cmo \
  typing/typemod.cmo 

#EXTRACTION=extraction/utils.cmo extraction/rdtspec.cmo \
#  extraction/rdtextract.cmo extraction/speclang.cmo

EXTRACTION= \

COMP=driver/pparse.cmo driver/main_args.cmo \
  driver/compenv.cmo driver/compmisc.cmo	\
	driver/compile.cmo driver/main.cmo 

# Top-level
ALLOBJS=$(UTILS) $(PARSING) $(TYPING)  # $(EXTRACTION) $(COMP) 

default: q6.opt
	cp q6.opt ./examples/q6

MYFILES=extraction/utils.cmx extraction/rdtspec.cmx extraction/rdtextract.cmi \
				extraction/rdtextract.cmx extraction/speclang.cmx extraction/light_env.cmi \
				extraction/light_env.cmx extraction/specelab.cmi extraction/specelab.cmx \
				extraction/specverify.cmi extraction/specverify.cmx 
MYCMX=extraction/utils.cmx extraction/rdtspec.cmx extraction/rdtextract.cmx \
			extraction/speclang.cmx extraction/light_env.cmx extraction/specelab.cmx \
			extraction/specverify.cmx

q6.byte: $(ALLOBJS)
	$(CAMLC) $(LINKFLAGS) -custom -o q6.byte str.cma unix.cma nums.cma $(ALLOBJS)

q6.opt: $(ALLOBJS:.cmo=.cmx) $(MYFILES) $(COMP:.cmo=.cmx)
	$(CAMLOPT) $(LINKFLAGS) -o q6.opt str.cmxa unix.cmxa nums.cmxa $(ALLOBJS:.cmo=.cmx) $(MYCMX) $(COMP:.cmo=.cmx)

reconfigure:
	./configure $(CONFIGURE_ARGS)

depend: beforedepend
	(for d in utils parsing typing extraction driver; \
	 do $(CAMLDEP) $(DEPFLAGS) $$d/*.mli $$d/*.ml; \
	 done) > .depend
	$(CAMLDEP) $(DEPFLAGS) -native \
		-impl driver/compdynlink.mlopt >> .depend
	$(CAMLDEP) $(DEPFLAGS) -bytecode \
		-impl driver/compdynlink.mlbyte >> .depend

alldepend:: depend

clean: partialclean
	(for d in utils parsing typing extraction driver; \
	  do rm -f $$d/*.cm[ioxt] $$d/*.cmti $$d/*.annot $$d/*.[so] $$d/*~; done);
	rm -f *~

localclean:
	(for d in extraction; \
	  do rm -f $$d/*.cm[ioxt] $$d/*.cmti $$d/*.annot $$d/*.[so] $$d/*~; done);

distclean:
	$(MAKE) clean
	rm -f config/Makefile config/m.h config/s.h
	rm -f tools/*.bak

utils/config.ml: utils/config.mlp config/Makefile
	@rm -f utils/config.ml
	sed -e 's|%%LIBDIR%%|$(LIBDIR)|' \
	    -e 's|%%BYTERUN%%|$(BINDIR)/ocamlrun|' \
	    -e 's|%%CCOMPTYPE%%|cc|' \
	    -e 's|%%BYTECC%%|$(BYTECC) $(BYTECCCOMPOPTS) $(SHAREDCCCOMPOPTS)|' \
	    -e 's|%%NATIVECC%%|$(NATIVECC) $(NATIVECCCOMPOPTS)|' \
	    -e '/c_compiler =/s| -Werror||' \
	    -e 's|%%PACKLD%%|$(PACKLD)|' \
	    -e 's|%%BYTECCLIBS%%|$(BYTECCLIBS)|' \
	    -e 's|%%NATIVECCLIBS%%|$(NATIVECCLIBS)|' \
	    -e 's|%%RANLIBCMD%%|$(RANLIBCMD)|' \
	    -e 's|%%ARCMD%%|$(ARCMD)|' \
	    -e 's|%%CC_PROFILE%%|$(CC_PROFILE)|' \
	    -e 's|%%ARCH%%|$(ARCH)|' \
	    -e 's|%%MODEL%%|$(MODEL)|' \
	    -e 's|%%SYSTEM%%|$(SYSTEM)|' \
	    -e 's|%%EXT_OBJ%%|.o|' \
	    -e 's|%%EXT_ASM%%|.s|' \
	    -e 's|%%EXT_LIB%%|.a|' \
	    -e 's|%%EXT_DLL%%|$(EXT_DLL)|' \
	    -e 's|%%SYSTHREAD_SUPPORT%%|$(SYSTHREAD_SUPPORT)|' \
	    -e 's|%%ASM%%|$(ASM)|' \
	    -e 's|%%ASM_CFI_SUPPORTED%%|$(ASM_CFI_SUPPORTED)|' \
	    -e 's|%%WITH_FRAME_POINTERS%%|$(WITH_FRAME_POINTERS)|' \
	    -e 's|%%WITH_SPACETIME%%|$(WITH_SPACETIME)|' \
	    -e 's|%%PROFINFO_WIDTH%%|$(PROFINFO_WIDTH)|' \
	    -e 's|%%LIBUNWIND_AVAILABLE%%|$(LIBUNWIND_AVAILABLE)|' \
	    -e 's|%%LIBUNWIND_LINK_FLAGS%%|$(LIBUNWIND_LINK_FLAGS)|' \
	    -e 's|%%MKDLL%%|$(MKDLL)|' \
	    -e 's|%%MKEXE%%|$(MKEXE)|' \
	    -e 's|%%MKMAINDLL%%|$(MKMAINDLL)|' \
	    -e 's|%%HOST%%|$(HOST)|' \
	    -e 's|%%TARGET%%|$(TARGET)|' \
	    -e 's|%%FLAMBDA%%|$(FLAMBDA)|' \
	    -e 's|%%SAFE_STRING%%|$(SAFE_STRING)|' \
	    utils/config.mlp > utils/config.ml

partialclean::
	rm -f utils/config.ml

beforedepend:: utils/config.ml

# The parser

parsing/parser.mli parsing/parser.ml: parsing/parser.mly
	$(CAMLYACC) $(YACCFLAGS) parsing/parser.mly

partialclean::
	rm -f parsing/parser.mli parsing/parser.ml parsing/parser.output

beforedepend:: parsing/parser.mli parsing/parser.ml

# The lexer

parsing/lexer.ml: parsing/lexer.mll
	$(CAMLLEX) parsing/lexer.mll

partialclean::
	rm -f parsing/lexer.ml

beforedepend:: parsing/lexer.ml

# Default rules

.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	$(CAMLC) $(COMPFLAGS) -c $<

.mli.cmi:
	$(CAMLC) $(COMPFLAGS) -c $<

.ml.cmx:
	$(CAMLOPT) $(COMPFLAGS) -c $<

world: q6.byte q6.opt

include .depend
