%{
open Base
open Ast

let getpos () = (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())
let rangepos n m = (Parsing.rhs_start_pos n, Parsing.rhs_end_pos m)

let pos (p, _) = p 

let rec make_forall xs tp =
  match xs with
  | [] -> tp
  | (b, k) :: bs -> Forall(b, k, make_forall bs tp)

let rec make_exists xs tp =
  match xs with
  | [] -> tp
  | (b,k) :: bs -> Exists(b, k, make_exists bs tp)
    

let rec make_fun(pos, ps, e) =
  match ps with
  | [] -> e
  | p :: ps -> (pos, ELam(p, make_fun(pos, ps, e)))

let rec make_app(f, args) =
  match args with
  | [] -> f
  | e :: es -> (merge(pos f, pos e), EApp(make_app(f, es), e))

let make_decl_list decls body =
  List.fold_left
    (fun acc (loc, x, term, tp) -> (pos term, ELet((loc, PVar x), (pos term, EAnnot(term, tp)), acc)))
    body
    decls

let make_pure_decl_list decls body =
  List.fold_left
    (fun acc (ppos, x, term, tp) ->
      let annot (e, tp) = (pos term, EAnnot(e, tp)) in 
      let elet(p, e1, e2) = (pos term, ELet(p, e1, e2)) in
      let bang e = (pos term, EBang e) in
      let pbang x = (ppos, PBang x) in 
      elet(pbang x, annot(bang term, Pure tp), acc))
    body
    decls

%}
%token TYPE 
%token FORALL
%token EXISTS
%token OF 
%token DOT 
%token VAL
%token REC 
%token NEXT
%token CONS
%token RPAREN
%token LPAREN
%token COMMA
%token UNDERSCORE
%token BANG
%token F
%token FUN
%token TO
%token PLUS
%token MINUS
%token AST
%token ANDAND
%token OR
%token LET
%token COLON
%token EQUAL
%token LT
%token LEQ
%token GT
%token GEQ 
%token IN
%token G
%token FIX
%token LOOP
%token TRUE
%token FALSE
%token IF
%token THEN
%token ELSE
%token RUN
%token INT
%token LIN
%token STREAMTYPE
%token AND
%token STRINGTYPE
%token NUMTYPE
%token BOOLTYPE
%token LOLLI
%token DOM
%token FRAME
%token SVG
%token UNITTYPE
%token MATCH
%token WITH
%token BEGIN
%token END
%token BAR 
%token DOUBLECOLON 
%token <string> CONID
%token I 
%token <float> NUM 
%token <string> STRING 
%token <string> IDENT 
%token EOF

%nonassoc below_TO
%right TO LOLLI
%nonassoc below_AND
%right AND AST 
%nonassoc NEXT BANG STREAMTYPE G F 


%nonassoc IN
%nonassoc THEN ELSE
%nonassoc IF
%nonassoc LET 
%right CONS 
%left COLON
%right DOUBLECOLON
%right OR 
%right ANDAND
%left EQUAL LT LEQ GEQ GT 
%left PLUS MINUS
%left TIMES  




%type <Ast.tp> tp 
%type <Ast.pat> pat
%type <Ast.exp> exp
%type <Ast.decl> toplevel_decl
%type <Ast.program> program 
%type <Ast.signature> signature
%type <Ast.signature_elt> signature_decl

%type <Ast.tp> test_tp 
%type <Ast.pat> test_pat
%type <Ast.exp> test_exp 
%type <Ast.decl> test_toplevel_decl
%type <Ast.program> test_program
%type <Ast.signature> test_signature
%type <Ast.signature_elt> test_signature_decl


%start test_tp test_pat test_exp test_toplevel_decl test_program test_signature test_signature_decl tp pat exp toplevel_decl program signature signature_decl


%%

/* Syntax of kinds */

kind : 
  LIN                      {Lin}
| INT                      {Int}


/* Syntax of types */

tp_atom :
  I                         { Tensor [] }
| NUMTYPE         	    { Num }
| BOOLTYPE        	    { Bool }
| STRINGTYPE      	    { String }
| UNITTYPE                  { Product [] }
| IDENT                     { TVar $1 }
| LPAREN tp RPAREN          { $2 }
;

tp_atom_list : 
  tp_atom                { [$1] }
| tp_atom tp_atom_list   { $1 :: $2 }
;

tp_app :
| tp_atom                { $1 }
| tp_atom tp_atom_list     { TApp($1, $2) }
| DOM tp_atom            { Dom $2 }
| SVG tp_atom            { Svg $2 }
| FRAME tp_atom          { Frame $2 }
| G tp_atom              { G $2 }
| F tp_atom              { F $2 }
| NEXT tp_atom      	 { Next $2 }
| BANG tp_atom      	 { Pure $2 }
| STREAMTYPE tp_atom	 { Stream $2 }
;

product_tp : 
  tp_app %prec below_AND { $1 }
| tp_app and_tps       { Product ($1 :: $2) }
| tp_app star_tps      { Tensor ($1 :: $2) }
;

and_tps :
  AND tp_app and_tps     { $2 :: $3 }
| AND tp_app             { [$2] }
;

star_tps :
  AST tp_app star_tps    { $2 :: $3 }
| AST tp_app             { [$2] }
;

mono_tp :
| product_tp %prec below_TO   { $1 }
| product_tp TO tp            { Arrow($1, $3) }
| product_tp LOLLI tp         { Lolli($1, $3) }
;


ident_list : 
                         { [] }
| IDENT ident_list       { ($1, None) :: $2 }
| LPAREN IDENT COLON kind RPAREN ident_list { ($2, Some $4) :: $6 }
;

tp :
  FORALL ident_list DOT tp    { make_forall $2 $4 }
| EXISTS ident_list DOT tp    { make_exists $2 $4 }
| mono_tp                     { $1 }
| error                       { failwith "type" }
;


/* pattern test */



/* Syntax of expressions */

pat_atom :
  IDENT                       { (getpos(), PVar $1) }
| UNDERSCORE                  { (getpos(), PTop) }
| LPAREN RPAREN               { (getpos(), PTuple []) }
| LPAREN pattern RPAREN       { $2 }
| LPAREN comma_pats RPAREN    { (getpos(), PTuple $2) }
| BANG pat_atom               { (getpos(), PBang $2) }
| NEXT pat_atom               { (getpos(), PNext $2) }
| F pat_atom                  { (getpos(), PF $2) }
| CONID                       { let pos = getpos() in (pos, PCon($1, (pos, PTuple []))) }
;

pattern :
  pat_atom                      { $1 } 
| pat_atom DOUBLECOLON pat_atom { (getpos(), PCons($1, $3)) }
| CONID pat_atom                { (getpos(), PCon($1, $2)) }
;

comma_pats : 
  pattern COMMA pattern    { [$1; $3] }
| pattern COMMA comma_pats { $1 :: $3 }
;

pat : 
  pattern { $1 }
| error   { failwith "pattern" }


pat_list : 
  pat_atom          { [$1] }
| pat_atom pat_list { $1 :: $2 }
;



exp_atom : 
| IDENT                      { (getpos(), EVar $1) } 
| TRUE                       { (getpos(), EBool true) } 
| FALSE                      { (getpos(), EBool false) }
| NUM                        { (getpos(), ENum $1) }
| STRING                     { (getpos(), EString $1) }
| exp_tuple_or_paren         { $1 }
;

exp_tuple_or_paren :
| LPAREN RPAREN                      { (getpos(), ETuple []) }
| LPAREN exp RPAREN                  { (getpos(), snd($2)) }
| LPAREN exp exp_comma_list RPAREN   { (getpos(), ETuple ($2 :: $3)) }
;

exp_comma_list :
| COMMA exp                     { [$2] }
| COMMA exp exp_comma_list      { $2 :: $3 }
;

exp_app : 
| BANG exp_atom              { (getpos(), EBang $2) }
| RUN exp_atom exp_atom_list { make_app((getpos(), ERun $2), $3) } 
| CONS LPAREN exp COMMA 
              exp RPAREN     { (getpos(), ECons($3, $5)) }
| G exp_atom                 { (getpos(), EG $2) }
| F exp_atom                 { (getpos(), EF $2) }
| NEXT exp_atom              { (getpos(), ENext $2) }
| exp_atom exp_atom_list     { make_app($1, $2) }
| CONID exp_atom_list        { match $2 with
                              | [] -> (getpos(), ECon($1, (getpos(), ETuple [])))
                              | [e] -> (getpos(), ECon($1, e))
                              | _ :: _ -> raise (SyntaxError(getpos(), "Constructor has multiple arguments")) }
;

exp_atom_list : 
|                          { [] }
| exp_atom_list exp_atom   { $2 :: $1 }
;

exp : 
| exp_app                    	       { $1 }
| block_decl IN exp          	       { let (pos, x, e, tp) = $1 in
                             	          (getpos(), ELet((pos, PVar x),
			     	       			(exp_pos e, EAnnot(e, tp)), $3)) }
| LET pat EQUAL exp IN exp             { (getpos(), ELet($2, $4, $6)) }
| LET pat COLON tp EQUAL exp IN exp    { (getpos(), ELet($2, (fst $6, EAnnot($6, $4)), $8))}
| IF exp THEN exp ELSE exp             { (getpos(), EIf($2, $4, $6)) }
| FUN pat_list TO exp          	       { make_fun(getpos(), $2, $4) }
| FIX IDENT pat_list TO exp	       { (getpos(), EFix($2, make_fun(getpos(), $3, $5))) }
| FUN LOOP IDENT pat TO exp            { (getpos(), ELoop($3, $4, $6)) }
| exp PLUS exp         		       { (getpos(), EOp(Plus, $1, $3)) }
| exp MINUS exp        		       { (getpos(), EOp(Minus, $1, $3)) }
| exp AST exp %prec TIMES              { (getpos(), EOp(Times, $1, $3)) }
| exp LT exp           		       { (getpos(), EOp(Lt, $1, $3)) }
| exp LEQ exp          		       { (getpos(), EOp(Leq, $1, $3)) }
| exp GT exp           		       { (getpos(), EOp(Gt, $1, $3)) }
| exp GEQ exp          		       { (getpos(), EOp(Geq, $1, $3)) }
| exp EQUAL exp        		       { (getpos(), EOp(Equal, $1, $3)) }
| exp ANDAND exp       		       { (getpos(), EOp(And, $1, $3)) }
| exp OR exp           		       { (getpos(), EOp(Or, $1, $3)) }
| exp DOUBLECOLON exp     	       { (getpos(), ECons($1, $3)) }
| exp COLON    tp                      { (getpos(), EAnnot($1, $3)) }
| MATCH exp 
  BEGIN branches END                   { (getpos(), ECase($2, $4)) }
| error                                { failwith "syntax error" }
| LPAREN error RPAREN                  { failwith "syntax error" }
| LPAREN error                         { failwith "missing close paren" }
| error RPAREN                         { failwith "missing open paren" }
;


branch :
  pat TO exp    { ($1, $3) }
;

bar_opt : 
       { () }
| BAR  { () }
;

branch_list : 
| branch                  { [$1] }
| branch BAR branch_list  { $1 :: $3 }
;

branches : bar_opt branch_list { $2 };

value_decl :
| VAL IDENT COLON tp  { (rangepos 2 2, $2, $4) }
;

value_bind :
| LET IDENT EQUAL exp                   { ($2, $4) }
| LET IDENT pat_list EQUAL exp          { ($2, make_fun(getpos(), $3, $5)) }
| LET REC IDENT pat_list EQUAL exp  { ($3, (getpos(), EFix($3, make_fun(getpos(), $4, $6)))) }
| LET LOOP IDENT pat EQUAL exp          { ($3, (getpos(), ELoop($3, $4, $6))) }
;

block_decl :
| value_decl value_bind { let (pos, x, tp) = $1 in
                          let (x', e) = $2 in
 			  if x = x' then
			    (pos, x, e, tp)
			  else
			    raise (SyntaxError(pos,
			 	 	       "Declaration and binding identifiers don't match")) }
;


idents : 
                { [] }
| IDENT idents  { $1 :: $2 }
;

constructor_decl : 
  CONID OF tp      { ($1, $3) }
| CONID            { ($1, Product []) }
;


constructors : 
  constructor_decl                  { [$1] }
| constructor_decl BAR constructors { $1 :: $3 }
;

constructor_decl_list : bar_opt constructors { $2 };

datatype_decl :
 TYPE IDENT idents EQUAL constructor_decl_list  {
   let rec mkarrow = function
     | [] -> Int
     | _ :: ids -> KArrow(Int, mkarrow ids)
   in 
   (getpos(), $2, (mkarrow $3, List.map (fun a -> (a, Int)) $3, $5)) }

type_decl : 
| TYPE IDENT COLON kind { (rangepos 2 2, $2, $4) }
;

type_bind : 
| LET IDENT EQUAL tp { (rangepos 4 4, $2, $4) }
;


type_def :
| type_decl type_bind 
                  { let (pos, a, kind) = $1 in 
                    let (pos', a', tp)  = $2 in 
                    if a = a' then 
                      TypeBind(pos', a, tp, kind)
                    else
                      raise (SyntaxError(pos, "Type declaration and definition identifiers don't match")) }
;

toplevel_decl : 
  block_decl      { ValueBind ($1) }
| value_decl      { let (pos, id, tp) = $1 in ValueDecl(pos, id, tp) }
| type_decl       { let (pos, id, kind) = $1 in TypeDecl(pos, id, kind) }
| type_def        { $1 }
| datatype_decl   { let (pos, id, data) = $1 in DataBind(pos, id, data) }
;

toplevel_decl_list : 
                                   { [] }
| toplevel_decl toplevel_decl_list { $1 :: $2 }
;

signature_decl : 
  value_decl        { let (pos, id, tp) = $1 in SigTypeDecl(pos, id, tp) }
| datatype_decl    { let (pos, id, data) = $1 in DataDecl(pos, id, data) } 
;

signature : 
      { [] }
| signature_decl signature  { $1 :: $2 }
;

program : 
  toplevel_decl_list IN exp { ($1, $3) }
;

test_tp : tp EOF {$1};
test_pat : pat EOF {$1}; 
test_exp : exp EOF {$1};  
test_toplevel_decl : toplevel_decl EOF {$1};
test_program : program EOF {$1};
test_signature : signature EOF {$1}; 
test_signature_decl : signature_decl EOF {$1};

