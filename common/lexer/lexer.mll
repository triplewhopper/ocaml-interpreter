{
    exception Eof
}
let digit = ['0'-'9']
let space = ' ' | '\t' | '\r' | '\n'
let alpha = ['a'-'z' 'A'-'Z' '_' ]
let ident = alpha (alpha | digit | ''')*

rule main = parse
| space+       { main lexbuf }

| "+"          { Parser.PLUS }
| "*"          { Parser.TIMES }
| "-"          { Parser.MINUS }
| "/"          { Parser.DIV }
| "mod"        { Parser.MOD }

| "&&"         { Parser.AND }
| "||"         { Parser.OR }
| "::"         { Parser.CONS }

| "="          { Parser.EQ }

| "<"          { Parser.LT }
| "<="         { Parser.LE }
| ">"          { Parser.GT }
| ">="         { Parser.GE }

| "let"        { Parser.LET }
| "rec"        { Parser.REC }
| "in"         { Parser.IN }
| "and"        { Parser.LETAND }


| "if"         { Parser.IF }
| "then"       { Parser.THEN }
| "else"       { Parser.ELSE }
| "match"      { Parser.MATCH }
| "with"       { Parser.WITH }
| "|"          { Parser.MIDDLEBAR }
| "fun"        { Parser.FUN}
| "function"   { Parser.FUNCTION }
| "->"         { Parser.ARROW }

| "true"       { Parser.BOOL (true) }
| "false"      { Parser.BOOL (false) }

| ","          { Parser.COMMA }
| "("          { Parser.LPAR }
| ")"          { Parser.RPAR }
| "["          { Parser.LBRACK }
| "]"          { Parser.RBRACK }
| ";"          { Parser.SEMI }
| ";;"         { Parser.SEMISEMI }

| digit+ as n  { Parser.INT (int_of_string n) }
| ident  as id { Parser.ID id }
| eof          { raise Eof}
| _            { failwith ("Unknown Token: " ^ Lexing.lexeme lexbuf)}
