%{
  open Command
  (* ここに書いたものは，ExampleParser.mliに入らないので注意 *)
  let count = ref 0
  (*match e with 
   | `EFun ((_: int), (_: string), (_: expr)) as e'-> (var, e') 
   | _ -> failwith "Syntax error: right hand side of let rec must be a function"*)
%}

%token <int>    INT
%token <bool>   BOOL
%token <string> ID
%token LET IN LETAND
%token PLUS "+" TIMES "*" MINUS "-" DIV "/" MOD "mod"
%token COMMA ","
%token AND "&&" OR "||" CONS "::"
%token EQ "=" LT "<" LE "<=" GT ">" GE ">="
%token IF THEN ELSE
%token LPAR "(" RPAR ")" LBRACK "[" RBRACK "]"
%token MATCH WITH MIDDLEBAR "|"
%token FUN ARROW "->"
%token FUNCTION "function"
%token REC
%token SEMI ";"
%nonassoc NOCOMMA 
%nonassoc COMMA
%nonassoc NOBAR
%nonassoc MIDDLEBAR


%token SEMISEMI ";;"

%start toplevel
%type <Expr.t0 Command.command list> toplevel
%%

toplevel:
  | ";;" {[]}
  | expr ";;"                                   { [CExp $1] }
  | lets=nonempty_list(let_bindings {CDecls $1} ); ";;"          {  lets }
  | lets=nonempty_list(let_rec_bindings {CRecDecls $1} ); ";;"       { lets }
;

let_bindings:
  LET; separated_nonempty_list(LETAND, let_binding {$1}) { List.split $2}

let_rec_bindings:
  LET; REC; separated_nonempty_list(LETAND, let_rec_binding {$1}) {List.split $3}


let_binding:
  var=ID; e=let_expr {(var, e)}

 let_rec_binding:
  var=ID; e=let_expr; {(var, e)}


let_expr:
  | "=" expr                      { $2 }
  | ID let_expr                   { count:=(!count)+1; `EFun(!count, $1, $2) }

expr:
  | tuple_excluded_expr %prec NOCOMMA { $1 }
  | tuple_expr { $1 }
;
%inline tuple_expr:
  | tuple_excluded_expr "," tuple_excluded_expr_list { `ETuple($1::$3) }
;

tuple_excluded_expr_list:
  | tuple_excluded_expr %prec NOCOMMA { [$1] }
  | tuple_excluded_expr "," tuple_excluded_expr_list { $1::$3 }
;

%inline tuple_excluded_expr:
  | bindings=let_bindings; IN; e2=expr            {`ELet(bindings,e2) }
  | bindings=let_rec_bindings; IN; e2=expr        {`ELetRec(bindings,e2)}
  | FUN fun_abbr                                  { $2 }
  | FUNCTION "|"? qs=clauses                      { count:=(!count)+1; let var = "$" ^ string_of_int !count in `EFun(!count, var, `EMatch (`EVar var, qs))}
  | IF; e1=expr; THEN; e2=expr; ELSE; e3=expr     { `EIf (e1, e2, e3) }
  | MATCH; e=expr; WITH; "|"? qs=clauses { `EMatch (e, qs) }
  | bool_expr { $1 }  
;

clause:
  | pat=pattern; ARROW; e=expr { (pat, e) }

clauses:
  | q=clause; "|" qs=clauses { q::qs }
  | q=clause %prec NOBAR { [q] }

pattern:
  | tuple_pattern { $1 }
;
tuple_pattern:
  | p=cons_pattern { p }
  | p=cons_pattern; "," ps=separated_nonempty_list(",", cons_pattern) { Pattern.PCon ("tuple", p::ps) }
;
cons_pattern:
  | p=atomic_pattern "::" ps=cons_pattern { Pattern.PCon ("::", [p; ps]) }
  | p=atomic_pattern { p }

atomic_pattern:
  | INT { Pattern.PInt $1 }
  | BOOL { Pattern.PBool $1 }
  | ID { Pattern.PVar $1 }
  | "[" "]" { Pattern.PCon ("[]", []) }
  | "(" p=pattern ")" { p }


fun_abbr:
  |ID ARROW expr                        { count:=(!count)+1;`EFun(!count, $1,$3) }
  |ID fun_abbr                          { count:=(!count)+1;`EFun(!count, $1,$2) }
;


bool_expr:
  | bool_or_expr "||" bool_expr           { `EBinaryOp("||", $1, $3) }
  | bool_or_expr                          { $1 }
;

bool_or_expr:
  | bool_factor_expr "&&" bool_or_expr    { `EBinaryOp("&&", $1,$3) }
  | bool_factor_expr                      { $1 }
;

bool_factor_expr:
  | bool_factor_expr "=" arith_expr       { `EBinaryOp("=", $1, $3) }
  | bool_factor_expr "<" arith_expr       { `EBinaryOp("<", $1, $3) }
  | bool_factor_expr "<=" arith_expr      { `EBinaryOp("<=", $1, $3) }
  | bool_factor_expr ">" arith_expr       { `EBinaryOp(">", $1, $3) }
  | bool_factor_expr ">=" arith_expr      { `EBinaryOp(">=", $1, $3) }
  | cons_expr                             { $1 }
;

cons_expr: 
  | arith_expr "::" cons_expr             { `EBinaryOp("::", $1, $3) }
  | arith_expr                            { $1 }
;

arith_expr:
  | arith_expr "+" factor_expr  { `EBinaryOp("+", $1, $3) }
  | arith_expr "-" factor_expr  { `EBinaryOp("-", $1, $3) }
  | factor_expr                 { $1 }
;

factor_expr:
  | factor_expr "*" unary_expr   { `EBinaryOp("*", $1, $3) }
  | factor_expr "/" unary_expr   { `EBinaryOp("/", $1, $3) }
  | factor_expr "mod" unary_expr   { `EBinaryOp("mod", $1, $3) }
  | unary_expr                   { $1 }
;
unary_expr:
  | "-" unary_expr { `EUnaryOp ("~-", $2) }
  | "+" unary_expr { `EUnaryOp ("~+", $2) }
  | app_expr { $1 }

app_expr:
  | app_expr atomic_expr { `ECall ($1, $2) }
  | atomic_expr          { $1 }

;

atomic_expr:
  | INT             { `EConstInt($1) }
  | BOOL            { `EConstBool($1) }
  | ID              { `EVar($1) }
  | "(" ")"         { `EConstUnit }
  | "[" "]"         { `EList([]) }
  | "["; es=semi_separated_exprs; "]" { `EList(es) }
  | "(" expr ")"    { $2 }

;
semi_separated_exprs:
  | e=expr { [e] }
  | e=expr SEMI {[e]}
  | e=expr SEMI es=semi_separated_exprs { e :: es }
