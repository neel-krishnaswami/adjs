OCAMLC=ocamlc
OCAMLLEX=ocamllex
OCAMLYACC=ocamlyacc
OPTS=-g -annot
BASE=base.mli base.ml
UNITTEST=unittest.mli unittest.ml
LAMBDA=lambda.mli lambda.ml
PP=pp.mli pp.ml
JS=js.mli js.ml
CONTEXT=context.mli context.ml
SUBTYPE=subtype.mli subtype.ml 
TRANSLATE=translate.mli translate.ml
AST=ast.mli ast.ml
POLY=poly.mli poly.ml
PARSELOC=parseloc.mli parseloc.ml
TOPLEVEL=toplevel.mli toplevel.ml
KINDING=kinding.mli kinding.ml
OBJS=unittest.cmo base.cmo ast.cmo parser.cmo lexer.cmo parseloc.cmo lambda.cmo context.cmo kinding.cmo subtype.cmo poly.cmo pp.cmo js.cmo translate.cmo toplevel.cmo


compiler: jscomp.cma
	ocamlc -o adjsc jscomp.cma adjsc.ml

lib: jscomp.cma

jscomp.cma: $(OBJS)
	$(OCAMLC) $(OPTS)  -a -o jscomp.cma $(OBJS)

unittest.cmo: $(UNITTEST)
	$(OCAMLC) $(OPTS) $(UNITTEST)

lambda.cmo: base.cmo $(LAMBDA)
	$(OCAMLC) $(OPTS)  base.cmo $(LAMBDA)

pp.cmo: $(PP)
	$(OCAMLC) $(OPTS) $(PP)

js.cmo: base.cmo pp.cmo $(JS)
	$(OCAMLC) $(OPTS) base.cmo pp.cmo $(JS)

context.cmo: base.cmo ast.cmo lambda.cmo $(CONTEXT)
	$(OCAMLC) $(OPTS) base.cmo ast.cmo $(CONTEXT)

kinding.cmo: base.cmo ast.cmo lambda.cmo context.cmo $(KINDING)
	$(OCAMLC) $(OPTS) base.cmo ast.cmo lambda.cmo context.cmo $(KINDING)


subtype.cmo: base.cmo ast.cmo lambda.cmo context.cmo kinding.cmo $(SUBTYPE)
	$(OCAMLC) $(OPTS) base.cmo ast.cmo lambda.cmo context.cmo kinding.cmo $(SUBTYPE)

poly.cmo: base.cmo ast.cmo lambda.cmo context.cmo kinding.cmo subtype.cmo $(POLY)
	$(OCAMLC) $(OPTS)  base.cmo ast.cmo lambda.cmo context.cmo kinding.cmo subtype.cmo $(POLY)

translate.cmo: base.cmo pp.cmo js.cmo lambda.cmo $(TRANSLATE)
	$(OCAMLC) $(OPTS)  base.cmo pp.cmo js.cmo lambda.cmo $(TRANSLATE)

toplevel.cmo: base.cmo ast.cmo lambda.cmo context.cmo kinding.cmo subtype.cmo poly.cmo pp.cmo js.cmo translate.cmo $(TOPLEVEL)
	$(OCAMLC) $(OPTS) base.cmo ast.cmo lambda.cmo context.cmo kinding.cmo subtype.cmo poly.cmo pp.cmo js.cmo translate.cmo $(TOPLEVEL)

base.cmo: $(BASE)
	$(OCAMLC) $(OPTS) $(BASE)

ast.cmo: base.cmo $(AST)
	$(OCAMLC) $(OPTS)  base.cmo $(AST)

lexer.cmo: lexer.ml base.cmo ast.cmo parser.cmo 
	$(OCAMLC) $(OPTS) base.cmo ast.cmo parser.cmo lexer.mli lexer.ml

lexer.ml: lexer.mll
	$(OCAMLLEX) lexer.mll

parser.cmo: base.cmo ast.cmo parser.ml
	$(OCAMLC) $(OPTS)  base.cmo ast.cmo parser.mli parser.ml 

parser.ml: parser.mly
	$(OCAMLYACC) -v parser.mly

parseloc.cmo: lexer.cmo parser.cmo $(PARSELOC)
	$(OCAMLC) $(OPTS) base.cmo ast.cmo parser.cmo lexer.cmo parseloc.mli parseloc.ml

clean:
	rm *~ *.cmi *.cmo *.cma *.annot parser.mli parser.ml lexer.ml parser.output *.cmt *.cmti *.o *.cmx *.cmxi *.cmxa
