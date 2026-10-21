open Printf ;;

type
  thing =
    Closure of thing * thing * environment |
    Cons of thing * thing |
    Nil |
    Number of int |
    Primitive of (thing -> environment -> thing) |
    Symbol of string
and
  environment = (string * thing) list ;;


module type Evaluatish =
sig
  val evaluate: thing -> thing ;;
  exception EvaluatorError of string ;;
end ;;

module Evaluator: Evaluatish =
struct

  exception EvaluatorError of string ;;

  let oops message =
    raise (EvaluatorError message) ;;

  let envGet env name etc =
    let rec envGetting env =
      match env
      with [] ->
             etc () |
           (otherName, otherValue) :: otherEnv ->
             if name = otherName
             then otherValue
             else envGetting otherEnv
    in envGetting env ;;

  let envMake () =
    [] ;;

  let envPut name value env =
    (name, value) :: env ;;



  let tee = Symbol "t" ;;


  let global = ref (envMake ()) ;;

  global := envPut "nil" Nil (! global) ;;
  global := envPut "t"   tee (! global) ;;


  let lookup env name =
    envGet env name
      (fun () ->
        envGet (! global) name
          (fun () ->
            oops ("Unbound name " ^ name))) ;;


  let rec evaluating thing env =
    match thing
    with Cons(func, args) ->
           (match (evaluating func env)
            with Closure (pars, body, bodyEnv) ->
                   apply pars args env body bodyEnv |
                 Primitive howTo ->
                   howTo args env |
                 _ ->
                   oops "Closure or primitive expected") |
         Symbol name ->
           lookup env name |
         _ ->
           thing


  and apply pars args argsEnv body bodyEnv =
    let rec applying pars args bodyEnv =
      match (pars, args)
      with (Nil, Nil) ->
             evaluating body bodyEnv |
           (Nil, Cons (_, _)) ->
             oops "More arguments than parameters" |
           (Cons (_, _), Nil) ->
             oops "Fewer arguments than parameters" |
           (Cons (Symbol name, pars), Cons (arg, args)) ->
             applying pars args
               (envPut name (evaluating arg argsEnv) bodyEnv) |
           _ ->
             oops "Bad application"
    in applying pars args bodyEnv ;;



  let evaluate thing =
    evaluating thing (envMake ()) ;;


  let makeArithmetic op message =
    (fun args env ->
      match args
      with Cons (left, Cons (right, Nil)) ->
             (let left = evaluating left env
              in let right = evaluating right env
                 in match (left, right)
                    with (Number left, Number right) ->
                           Number (op left right) |
                         _ ->
                           oops message) |
           _ ->
             oops message) ;;


  let makeRelation op message =
    (fun args env ->
      match args
      with Cons (left, Cons (right, Nil)) ->
             (let left = evaluating left env
              in let right = evaluating right env
                 in match (left, right)
                    with (Number left, Number right) ->
                           if op left right
                           then tee
                           else Nil |
                         _ ->
                           oops message) |
           _ ->
             oops message) ;;



  let primitive name howTo =
    global := envPut name (Primitive howTo) (! global) ;;



  primitive "*" (makeArithmetic ( * ) "* expected two numbers") ;;


  primitive "+" (makeArithmetic (+) "+ expected two numbers") ;;


  primitive "-"
    (fun args env ->
      match args
      with Cons (right, Nil) ->
             (match (evaluating right env)
              with Number right ->
                     Number (- right) |
                   _ ->
                     oops "- expected a number") |
           Cons (left, Cons (right, Nil)) ->
             let left = evaluating left env
             in let right = evaluating right env
                in (match (left, right)
                    with (Number left, Number right) ->
                           Number (left - right) |
                         _ ->
                           oops "- expected two numbers") |
           _ ->
             oops "- expected one or two numbers") ;;


  primitive "/"
    (fun args env ->
      match args
      with Cons (left, Cons (right, Nil)) ->
             let left = evaluating left env
             in let right = evaluating right env
                in (match (left, right)
                    with (_, Number 0) ->
                           oops "/ tried to divide by 0" |
                         (Number left, Number right) ->
                           Number (left / right) |
                         _ ->
                           oops "/ expected two numbers") |
           _ ->
             oops "/ expected two numbers") ;;

  primitive "<"  (makeRelation (<)  "< expected two numbers") ;;
  primitive "<=" (makeRelation (<=) "<= expected two numbers") ;;
  primitive "<>" (makeRelation (<>) "<> expected two numbers") ;;
  primitive ">"  (makeRelation (>)  "> expected two numbers") ;;
  primitive ">=" (makeRelation (>=) "< expected two numbers") ;;


  primitive "="
    (fun args env ->
      match args
      with Cons (left, Cons (right, Nil)) ->
             (let left = evaluating left env
              in let right = evaluating right env
                 in match (left, right)
                    with (Nil, Nil) ->
                           tee |
                         (Number left, Number right) ->
                           if left = right
                           then tee
                           else Nil |
                         (Symbol left, Symbol right) ->
                           if left = right
                           then tee
                           else Nil |
                         _ ->
                           Nil) |
           _ ->
             oops "= expected two arguments") ;;


  primitive "and"
    (fun args env ->
      let rec anding args =
        match args
        with Nil ->
               tee |
             Cons (arg, Nil) ->
               evaluating arg env |
             Cons (arg, args) ->
               if (evaluating arg env) = Nil
               then Nil
               else anding args |
             _ ->
               oops "AND expected zero or more arguments"
      in anding args) ;;

(* CAR. Return the first element of a nonempty Lisp list. *)

  primitive "car"
   (fun args env ->
     match args
     with Cons (arg, Nil) ->
            (match (evaluating arg env)
             with Cons (first, _) ->
                   first |
                  _ ->
                    oops "CAR expected a CONS") |
          _ ->
            oops "CAR expected a CONS") ;;

(* CDR. Return a Lisp list without its first element. *)

  primitive "cdr"
   (fun args env ->
     match args
     with Cons (arg, Nil) ->
            (match (evaluating arg env)
             with Cons (_, rest) ->
                    rest |
                  _ ->
                    oops "CDR expected a CONS") |
          _ ->
            oops "CDR expected a CONS") ;;



  primitive "cons"
    (fun args env ->
      match args
      with Cons (first, Cons (rest, Nil)) ->
             let first = evaluating first env
             in let rest = evaluating rest env
                in (match rest
                    with Cons (_, _) | Nil ->
                           Cons (first, rest) |
                         _ ->
                           oops "CONS expected an object and a list") |
           _ ->
             oops "CONS expected an object and a list") ;;


  primitive "define"
    (fun args env ->
      match args
      with Cons (left, Cons (right, Nil)) ->
             (match left
              with Symbol name ->
                     global := envPut name (evaluating right env) (! global) ;
                     left |
                   _ ->
                     oops "DEFINE expected a symbol and an expression") |
           _ ->
             oops "DEFINE expected a symbol and an expression") ;;


  primitive "if"
    (fun args env ->
      match args
      with Cons (test, Cons (whenTrue, Cons (whenFalse, Nil))) ->
             if evaluating test env = Nil
             then evaluating whenFalse env
             else evaluating whenTrue env |
           _ ->
             oops "IF expected three arguments") ;;

(* IS-CONS. Test if the single argument is a CONS, i.e., a nonempty list. *)

  primitive "is-cons"
    (fun args env ->
      match args
      with Cons (arg, Nil) ->
             (match (evaluating arg env)
              with Cons (_, _) ->
                     tee |
                   _ ->
                     Nil) |
           _ ->
             oops "IS-CONS expected one argument") ;;

(* IS-FUNCTION. Test if the single argument is a CLOSURE or a PRIMITIVE. *)

  primitive "is-function"
    (fun args env ->
      match args
      with Cons (arg, Nil) ->
             (match (evaluating arg env)
              with Closure (_, _, _) | Primitive (_) ->
                     tee |
                   _ ->
                     Nil) |
           _ ->
             oops "IS-FUNCTION expected one argument") ;;

(* IS-NUMBER. Test if the single argument is a NUMBER. *)

  primitive "is-number"
    (fun args env ->
      match args
      with Cons (arg, Nil) ->
             (match (evaluating arg env)
              with Number _ ->
                     tee |
                   _ ->
                     Nil) |
           _ ->
             oops "IS-NUMBER expected one argument") ;;

(* IS-SYMBOL. Test if the single argument is NIL or a SYMBOL. *)

  primitive "is-symbol"
    (fun args env ->
      match args
      with Cons (arg, Nil) ->
             (match (evaluating arg env)
              with Nil | Symbol _ ->
                     tee |
                   _ ->
                     Nil) |
           _ ->
             oops "IS-SYMBOL expected one argument") ;;

(* IS MEMBER. Helper for ARE PARAMETERS. Test if THING is a member of the Lisp
   list THINGS. *)

  let isMember thing things =
    let rec isMembering things =
      match things
      with Cons (first, rest) ->
             thing = first || isMembering rest |
           _ ->
             false
    in isMembering things ;;

(* ARE PARAMETERS. Helper for LAMBDA. Test if THINGS is a Lisp list of SYMBOLS,
   in which no SYMBOL appears more than once. *)

  let rec areParameters things =
    match things
    with Nil ->
           true |
         Cons (first, rest) ->
           (match first
            with Symbol _ ->
                   not (isMember first rest) && (areParameters rest) |
                 _ ->
                   false) |
         _ ->
           false ;;


  primitive "lambda"
    (fun args env ->
      match args
      with Cons (pars, Cons (body, Nil)) ->
             if areParameters pars
             then Closure (pars, body, env)
             else oops "LAMBDA expected parameters and a body" |
           _ ->
             oops "LAMBDA expected parameters and a body") ;;


  primitive "list"
    (fun args env ->
      let rec listing args =
        match args
        with Nil ->
               Nil |
             Cons (arg, args) ->
               Cons (evaluating arg env, listing args) |
             _ ->
               oops "LIST expected zero or more arguments"
      in listing args) ;;

(* NOT. Test if the single argument is NIL. *)

  primitive "not"
    (fun args env ->
      match args
      with Cons (arg, Nil) ->
             if (evaluating arg env) = Nil
             then tee
             else Nil |
           _ ->
             oops "NOT expected one argument") ;;


  primitive "or"
   (fun args env ->
     let rec oring args =
       match args
       with Nil ->
              Nil |
            Cons (arg, Nil) ->
              evaluating arg env |
            Cons (arg, args) ->
              let value = evaluating arg env
              in if value = Nil
                 then oring args
                 else value |
            _ ->
              oops "OR expected zero or more arguments"
     in oring args) ;;


  primitive "quote"
    (fun args _ ->
      match args
      with Cons (arg, Nil) ->
             arg |
           _ ->
             oops "QUOTE expected one argument") ;;
end ;;



module Scanner =
struct

(* TOKEN. A token for an expression in a subset of Lisp. *)

  type token =
    CloseParenToken |
    EndToken |
    NumberToken of int |
    OpenParenToken |
    SymbolToken of string ;;


  let makeScanner path =
    let input = open_in path
    in let ch = ref ' '
       in


  let nextChar () =
    try ch := input_char input
    with End_of_file ->
           ch := '\000'
  in

(* NEXT CLOSE PAREN TOKEN. Read a CLOSE PAREN TOKEN. *)

  let nextCloseParenToken () =
    nextChar () ;
    CloseParenToken
  in


  let rec nextComment () =
    match ! ch
    with '\000' ->
           () |
         '\n' ->
           nextChar () |
         _ ->
           nextChar () ;
           nextComment ()
  in


  let nextEndToken () =
    EndToken
  in

(*  NEXT NUMBER TOKEN. Read a NUMBER TOKEN. If it doesn't denote an INT then we
    read it as a SYMBOL TOKEN instead. *)

  let nextNumberToken () =
    let rec nextNumbering chars =
      match ! ch
      with '\000' | '\n' | ' ' | '(' | ')' ->
             (try
                NumberToken (int_of_string chars)
              with
                Failure _ ->
                  SymbolToken chars) |
           _ ->
             let otherChars = Char.escaped ! ch
             in nextChar () ;
                nextNumbering (chars ^ otherChars)
    in nextNumbering ""
  in

(* NEXT OPEN PAREN TOKEN. Read an OPEN PAREN TOKEN. *)

  let nextOpenParenToken () =
    nextChar () ;
    OpenParenToken
  in

(*  NEXT SYMBOL TOKEN. Read a SYMBOL TOKEN. *)

  let nextSymbolToken () =
    let rec nextSymboling chars =
      match ! ch
      with '\000' | '\n' | ' ' | '(' | ')' ->
             SymbolToken chars |
           _ ->
             let otherChars = Char.escaped ! ch
             in nextChar () ;
                nextSymboling (chars ^ otherChars)
    in nextSymboling ""
  in

(* NEXT TOKEN. Look at CH to tell what TOKEN is coming next. Dispatch to the
   function that will read that TOKEN and return it. *)

  let rec nextToken () =
    match ! ch
    with '\000' ->
           nextEndToken () |
         ' ' | '\n' ->
           nextChar () ;
           nextToken () |
         '(' ->
           nextOpenParenToken () |
         ')' ->
           nextCloseParenToken () |
         ';' ->
           nextComment () ;
           nextToken () |
         '-' | '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' ->
           nextNumberToken () |
         _ ->
           nextSymbolToken ()

(* Lost? This is MAKE SCANNER's body. Initialize CH by reading the NEXT CHAR,
   and return (but do not call!) NEXT TOKEN. *)

  in nextChar () ;
     nextToken ;;

end ;;


module type Parserish = 
sig 
  val makeParser : string -> (unit -> thing);;
  exception CantParse of string;;
end;;

(* PARSER. Read Lisp expressions from a file. *)

module Parser : Parserish =
struct
  exception CantParse of string;;

  let makeParser path = 
    let scanner = Scanner.makeScanner path in
    let token = ref (scanner ()) in
  
  let rec nextThing () = 
    match !token
    with CloseParenToken -> raise (CantParse "Unable to parse, unexpected CloseParenToken") |
         EndToken -> raise (CantParse "Unable to parse, unexpected EOF") |
         NumberToken n -> token := scanner(); Number n |
         SymbolToken "nil" -> token := scanner();  Nil |
         SymbolToken s -> token := scanner(); Symbol s |
         OpenParenToken -> token := scanner(); nextThings ()
  
  and nextThings () = 
    match !token 
    with EndToken -> raise (CantParse "Unable to parse, unexpected EOF") |
         CloseParenToken -> token := scanner (); Nil |
         _ -> let first = nextThing() in
              let rest = nextThings() in
              Cons (first, rest)
    in
    
  fun () -> nextThing ();;

end;;

module type Printish =
sig

  exception BadThing;;
  val printThing : thing -> unit;;

end ;;

(* PRINTER. Print Lisp THINGs to standard output. *)

module Printer: Printish =
struct 

  exception BadThing;;

  let rec printingThings thing = 
    match thing 
    with Cons (first, Nil) -> 
            printingThing first;
            printf ")" |
        Cons (first, rest) -> 
            printingThing first;
            printf " ";
            printingThings rest; |
        Nil -> printf "nil" |
        _ -> printingThing thing

  and printingThing thing = 
    match thing 
    with Closure (_, _, _) -> printf "[Closure]" |
        Nil -> printf "nil" |
        Number n -> printf "%i" n |
        Primitive _ -> printf "[Primitive]" |
        Symbol s -> printf "%s" s |
        Cons _ -> printf "(";
                printingThings thing |
        _ -> raise BadThing;;

  let printThing thing =
    printingThing thing;
    printf "\n";;

end ;;


module type Lispish =
sig

  val repl : unit -> unit;;

end ;;

(* LISP. Read Lisp programs from files and execute them. *)

module Lisp: Lispish =
struct

  let commandArguments etc =
    Arg.parse
      [ ("", (Arg.String (fun _ -> ())), "Zero or more arguments expected") ]
      etc
      "Argument expected" ;;

  let rec repl () = 
    commandArguments (fun p -> 
      let nextThing = Parser.makeParser p in
        let rec repling () = 
          try
            let curr = nextThing () in
              (match curr
              with Symbol "end" -> () |
                   _ -> let evaluated = (Evaluator.evaluate curr) in 
                        Printer.printThing (evaluated);
              repling())
          with
            Evaluator.EvaluatorError s -> Printf.printf "%s: Evaluator error %s\n" p s;
            repl() |

            Parser.CantParse s -> Printf.printf "%s: Parser error %s\n" p s;
            repl() |

            Printer.BadThing -> Printf.printf "%s: Printer error\n" p;
            repl() |

            _ -> Printf.printf "%s: Internal error\n" p;
            repl()
            
      in repling()
    );;

end ;;

(* ------------------------------------------------------------------------- *)

(* The big finish. Run it! *)

Lisp.repl () ;;