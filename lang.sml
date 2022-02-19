(* Imports *)
load "Int";
load "Bool";
load "Listsort";

(* Types and datatypes definition *)
type loc = string
type var = string

datatype langType =  mInt  
                    | mUnit  
                    | mBool 
                    | mRef of langType
                    | mFun of langType * langType

type store = (loc * langType) list
datatype oper = plus | gt

(* Lang structure *)
datatype exp =
        Boolean of bool
    |   Integer of int
    |   Op of exp * oper * exp
    |   If of exp * exp * exp
    |   Assign of loc * exp
    |   Skip 
    |   Seq of exp * exp
    |   While of exp * exp
    |   Deref of loc
    |   Var of var
    |   Fn of var * langType * exp
    |   App of exp * exp


(* Returns whether or not the passed argument is a value *)
fun value (Integer n)     = true
  | value (Boolean b)     = true
  | value (Fn (v, t, e))  = true
  | value (Var x)         = true
  | value (Skip)          = true
  | value _               = false

(* Searches in the store the location passed as argument *)
fun lookup ( [], l ) = NONE
  | lookup ( (l',n')::pairs, l) = 
    if l=l' then SOME n' else lookup (pairs,l)

(* Updates the store *)
fun update'  front [] (l,n) = NONE
 |  update'  front ((l',n')::pairs) (l,n) = 
    if l=l' then 
        SOME(front @ ((l,n)::pairs) )
    else 
        update' ((l',n')::front) pairs (l,n)

fun update (s, (l,n)) = update' [] s (l,n)

(* Applies substitution of value in var *)
fun substitute var value (Boolean b)      = Boolean b
  | substitute var value (Integer n)      = Integer n
  | substitute var value Skip             = Skip
  | substitute var value (Var x)          = if var = x then value else (Var x)
  | substitute var value (Fn(x, t, e))    = Fn(x, t, substitute var value e)
  | substitute var value (App(f, e))      = App(substitute var value f, substitute var value e)
  | substitute var value (If(g, t, f))    = If(substitute var value g, substitute var value t, substitute var value f)
  | substitute var value (Assign(l, e))   = Assign(l, substitute var value e)
  | substitute var value (While(g, e))    = While(substitute var value g, substitute var value e)
  | substitute var value (Seq(e1, e2))    = Seq(substitute var value e1, substitute var value e2)
  | substitute var value (Deref(l))       = Deref(l)
  | substitute var value (Op(e1, oper, e2)) = Op(substitute var value e1, oper, substitute var value e2)

(* Small-step operational semantics *)
fun reduce (Integer n, s) = NONE
  | reduce (Boolean b, s) = NONE
  | reduce (Fn (v, t, e), s) = NONE
  | reduce (Var x, s) = NONE
  | reduce (Skip,s) = NONE
  | reduce (Op (e1, oper, e2), s) = 
    (case (e1, oper, e2) of
         (Integer n1, plus, Integer n2) => SOME(Integer (n1 + n2), s)   (*oper+*)
       | (Integer n1, gt, Integer n2) => SOME(Boolean (n1 >= n2), s)    (*oper>=*)
       | (e1, oper, e2) => (                                               
         if (value e1) then (                                        
             case reduce (e2, s) of 
                 SOME (e2', s') => SOME (Op(e1, oper, e2'), s')     (*op2*)
               | NONE => NONE )                           
         else (                                                 
             case reduce (e1, s) of 
                 SOME (e1',s') => SOME(Op(e1', oper, e2), s')      (*op1*)
               | NONE => NONE ) ) )
  | reduce (If (g, e1, e2), s) =
    (case g of
         Boolean(true) => SOME(e1, s)                           
       | Boolean(false) => SOME(e2, s)                          
       | _ => (case reduce (g, s) of
                   SOME(g',s') => SOME(If(g', e1, e2), s')      (*if*)
                 | NONE => NONE ))
  | reduce (Deref l, s) = 
    (case lookup(s, l) of                
          SOME n => SOME(Integer n, s)                          
        | NONE => NONE )                  
  | reduce (Assign (l, e), s) =                                  
    (case e of                                                 
         Integer n => (case update (s, (l, n)) of 
                           SOME s' => SOME(Skip, s')           
                         | NONE => NONE)                                   
       | _ => (case reduce (e, s) of                           
                   SOME (e', s') => SOME(Assign (l, e'), s')    
                 | NONE => NONE  ) )                          
  | reduce (While (g, e2), s) = SOME(If(g, Seq(e2, While(g, e2)), Skip), s) (* (while) *)
  | reduce (Seq (e1, e2), s) =                                   
    (case e1 of                                                 
        Skip => SOME(e2, s)                                     
      | _ => ( case reduce (e1, s) of                           
                 SOME (e1', s') => SOME(Seq (e1', e2), s')       
               | NONE => NONE ))
  | reduce (App (f, e), s) = (
    case (f, e) of
        (Fn(x, t, body), Integer n) => SOME(substitute x (Integer n) body, s)
        | (f, e) =>
              if (value f) then
                case reduce(e, s) of
                    SOME(e', s') => SOME(App(f, e'), s)
                  | NONE => NONE
              else
                case reduce(f, s) of
                    SOME(f', s) => SOME(App(f', e), s)
                  | NONE => NONE)

(* Big-step operational semantics *)
fun evaluate (e,s) = case reduce (e, s) of 
                         NONE => (e, s)
                       | SOME (e', s') => evaluate (e', s')

(* Typechecker *)
fun infertype gamma (Integer n) = SOME mInt
  | infertype gamma (Boolean b) = SOME mBool
  | infertype gamma (Var x) = (
    case lookup(gamma, x) of
        SOME t => SOME t
      | NONE => NONE
  )
  | infertype gamma (Fn (x, t, e)) = (
    case (infertype ((x, t)::gamma) e) of
        SOME t1 => SOME (mFun(t, t1))
      | NONE => NONE
  )
  | infertype gamma (App (e1, e2)) = (
    case (infertype gamma e1, infertype gamma e2) of
      (SOME(mFun(t, t1)), SOME t2) => if t = t2 then SOME t1 else NONE
    | _ => NONE
  )
  | infertype gamma (Op (e1, oper, e2)) 
    = (case (infertype gamma e1, oper, infertype gamma e2) of
          (SOME mInt, plus, SOME mInt) => SOME mInt
        | (SOME mInt, gt, SOME mInt) => SOME mBool
        | _ => NONE)
  | infertype gamma (If (g, e1, e2)) 
    = (case (infertype gamma g, infertype gamma e1, infertype gamma e2) of
           (SOME mBool, SOME t1, SOME t2) => 
           (if t1 = t2 then SOME t1 else NONE)
         | _ => NONE)
  | infertype gamma (Deref l) 
    = (case lookup(gamma, l) of
           SOME (mRef t) => SOME t
         | _ => NONE)
  | infertype gamma (Assign (l,e)) 
    = (case (lookup (gamma,l), infertype gamma e) of
           (SOME (mRef(mInt)), SOME mInt) => SOME mUnit
         | _ => NONE)
  | infertype gamma (Skip) = SOME mUnit
  | infertype gamma (Seq (e1,e2))  
    = (case (infertype gamma e1, infertype gamma e2) of
           (SOME mUnit, SOME t2) => SOME t2
         | _ => NONE )
  | infertype gamma (While (e1, e2)) 
    = (case (infertype gamma e1, infertype gamma e2) of
           (SOME mBool, SOME mUnit) => SOME mUnit 
         | _ => NONE );

(* Pretty printer *)
fun printOp plus = "+"
  | printOp gt = ">="

fun printType (mInt) = "int"
  | printType (mBool) = "bool"
  | printType (mUnit) = "unit"
  | printType (mRef(t)) = printType(t) ^ "ref"
  | printType (mFun(t, t1)) = "(" ^ (printType t) ^ ") -> " ^ (printType t1)
                         
fun printExp (Integer n) = Int.toString n
  | printExp (Boolean b) = Bool.toString b
  | printExp (Var x) = x
  | printExp (Op (e1,oper,e2)) 
    = "(" ^ (printExp e1) ^ (printOp oper) 
      ^ (printExp e2) ^ ")"
  | printExp (If (e1,e2,e3)) 
    = "if " ^ (printExp e1) ^ " then " ^ (printExp e2)
      ^ " else " ^ (printExp e3)
  | printExp (Deref l) = "!" ^ l
  | printExp (Assign (l,e)) =  l ^ ":=" ^ (printExp e )
  | printExp (Skip) = "skip"
  | printExp (Seq (e1,e2)) =  (printExp e1 ) ^ "; " 
                                     ^ (printExp e2)
  | printExp (While (e1,e2)) =  "while " ^ (printExp e1 ) 
                                       ^ " do " ^ (printExp e2)
  | printExp (Fn(x, t, e)) = "fn " ^ x ^ ": " ^ (printType t) ^ " => " ^ (printExp e)
  | printExp (App(f, e)) = "(" ^ (printExp f) ^ ")" ^ "(" ^ (printExp e) ^ ")"


fun printStore' [] = ""
  | printStore' ((l,n)::pairs) = l ^ "=" ^ (Int.toString n) 
                                   ^ " " ^ (printStore' pairs)

fun printStore pairs = 
    let val pairs' = Listsort.sort 
                         (fn ((l,n),(l',n')) => String.compare (l,l'))
                         pairs
    in
        "{ " ^ printStore' pairs' ^ "}" end


fun printConf (e, s) = "< " ^ (printExp e) 
                             ^ " , " ^ (printStore s) ^ " >"


fun printReduce' (e, s) = 
    case reduce (e, s) of 
        SOME (e',s') => 
        ( TextIO.print ("\n -->  " ^ printConf (e',s') ) ;
          printReduce' (e',s'))
      | NONE => (TextIO.print "\n -/->  " ; 
                 if value e then 
                     TextIO.print "(a value)\n" 
                 else 
                     TextIO.print "(stuck - not a value)" )

fun printReduce (e, s) = (TextIO.print ("\t"^(printConf (e,s))) ;
                          printReduce' (e, s))

fun generateGamma [] = []
  | generateGamma ((l, n)::pairs) = (l, mRef(mInt))::generateGamma(pairs)

fun printGamma' [] = ""
  | printGamma' ((l, t)::pairs) = l ^ ": " ^ (printType t) 
                                   ^ " " ^ (printGamma' pairs)

fun printGamma pairs = 
    let val pairs' = Listsort.sort 
                         (fn ((l,n),(l',n')) => String.compare (l,l'))
                         pairs
    in
        "{ " ^ printGamma' pairs' ^ "}" end

fun printTypecheck e NONE = (printTypecheck e (SOME []))
  | printTypecheck e (SOME s) = (
    TextIO.print ("> Expression: " ^ (printExp e) ^ "\n");
    let val gamma = generateGamma s in
      case infertype gamma e of
          SOME t => (
            TextIO.print ("> Gamma: " ^ (printGamma gamma) ^ "\n");
            TextIO.print ("> Type: " ^ (printType t) ^ "\n")
          )
        | NONE => TextIO.print "> Error: can't infer type for this expression\n"
    end)