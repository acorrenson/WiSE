grammar ImpLanguage;

start : macrodef * imp ;

aexpr :
    ID  # var
  | NUM # cst
  | aexpr '+' aexpr # add
  | aexpr '-' aexpr # sub
  | '(' aexpr ')'   # apar
  ;

bexpr :
    ( TRUE | FALSE )  # bcst
  | aexpr '<=' aexpr  # ble
  | aexpr '<' aexpr   # blt
  | aexpr '>=' aexpr  # bge
  | aexpr '>' aexpr   # bgt
  | aexpr '==' aexpr  # beq
  | 'not' bexpr       # bnot
  | bexpr 'and' bexpr # band
  | bexpr 'or' bexpr  # bor
  | '(' bexpr ')'     # bpar
  ;

imp :
    'skip'                                # skip
  | 'fail'                                # err
  | ID '=' aexpr                          # aff
  | 'assert' bexpr                        # assert
  | 'if' bexpr 'then' imp 'else' imp 'fi' # ite
  | 'while' bexpr 'do' imp 'od'           # loop
  | name=ID
      ( '(' aexpr (',' aexpr) * ')' ) ?   # macrocall
  | imp ';' imp                           # seq
  ;

macrodef :
    'macro' name=ID
    ( '(' aexpr (',' aexpr) * ')' ) ?
    'begin' imp 'end'
  ;

TRUE: 'true' ;
FALSE: 'false' ;
NUM : '-' ? [0-9]+ ;
ID : [a-zA-Z0-9_]+ ;

WS : [ \r\n\t]+ -> skip ;
COMMENT
  :  '#' ~( '\r' | '\n' )* -> skip
  ;