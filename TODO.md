TODO
====

PROJECT:
    * pretty arg parsing utils

FILE: full_debug.ml
    * better arg parsing
    * Allow users to choose what to print (Pretoks/Sexp/SexpNode/Pexp/Lexp/etc..)
        * --all
        * --pretoks
        * --sexp
        * --node
        * --pexp
        * --lexp
        
        Other Option
            --repl 
            
            
case (a,b)
   | (Foo, Foo) => 3.14
   | (Bar, Bar) => 3.15
;;



# Issues

* The duplicate ';' create Sexp::Epsilon() which makes pexp_parse fail
* pexp_parse fail to parse inductive
