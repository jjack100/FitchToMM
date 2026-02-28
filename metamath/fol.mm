$(
################################################################################
Natural Deduction for First-Order Logic
################################################################################
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*
Formal Grammar
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*

We represent all formulas and terms simply as S-Expressions.
An S-Expression is a string representation of a tree recursively defined as either:
1. An atom which cannot be decomposed further (e.g., an operator name), or
2. A list of S-Expressions that is space-delimited and enclosed in
  parentheses, where the first element of the list is typically the
  operator and the rest the operands.
For example, ( and psi phi ) represents the conjunction of psi and phi.

A judgement of natural deduction is represented as a list of assumptions the
judgement depends on (the "context"), followed by the turnstile symbol |- and
the formula that is proved.
For example, phi psi |- ( and phi psi ) represents the judgement that phi and
psi are true assuming phi and assuming psi.
$)

$( Constant symbols $)
$c ( ) ; |- :=  $.
$( Type symbols: well-formed formulae (WFFs), contexts, statements $)
$c wff ctx stmt $.

$( We use an ellipsis as a metavariable to range over a list of WFFs (that form
   an assumption context) $)
$v ... ..._1 ..._2 $.
ctx.ellipsis    $f ctx ... $.
ctx.ellipsis_1  $f ctx ..._1 $.
ctx.ellipsis_2  $f ctx ..._2 $.

$( Metavariables used to represent WFFs $)
$v phi psi chi phi_1 psi_1 chi_1 phi_2 psi_2 chi_2 $.
wff.phi   $f wff phi $.
wff.psi   $f wff psi $.
wff.chi   $f wff chi $.
wff.phi_1 $f wff phi_1 $.
wff.psi_1 $f wff psi_1 $.
wff.chi_1 $f wff chi_1 $.
wff.phi_2 $f wff phi_2 $.
wff.psi_2 $f wff psi_2 $.
wff.chi_2 $f wff chi_2 $.

$( Define syntax for contexts $)

$( A context list may be empty $)
ctx.empty $a ctx $. 
$( A context list may contain a single WFF $)
ctx.singleton $a ctx phi $.
$( Two context lists may be concatenated to form a new list $)
ctx.concat $a ctx ..._1 ..._2 $.

$( We can now construct lists by appending WFFs $)
ctx.append $p ctx ... phi $= ( ctx.singleton ctx.concat ) ABCD $.
$( And we can now construct lists by prepending WFFs $)
ctx.prepend $p ctx phi ... $= ( ctx.singleton ctx.concat ) BCAD $.

$( Syntax for judgements $)
stmt.jdg $a stmt ... |- phi $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*
Propositional Logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*
$)

$( Logical symbols $)
$c and or not implies iff true false $.

$( Propositional WFFs $)
wff.and     $a wff ( and phi psi ) $.
wff.or      $a wff ( or phi psi ) $.
wff.implies $a wff ( implies phi psi ) $.
wff.iff     $a wff ( iff phi psi ) $.
wff.not     $a wff ( not phi ) $.
wff.true    $a wff true $.
wff.false   $a wff false  $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
Introduction Rules
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
$)

${
  axm.and-intr.1 $e ; ... |- phi $.
  axm.and-intr.2 $e ; ... |- psi $.
  $( Conjunction Introduction $)
  axm.and-intr   $a ; ... |- ( and phi psi ) $.
$}

${
  axm.or-intr.1 $e ; ... |- phi $.
  $( Disjunction Introduction (left side) $)
  axm.or-intr-1 $a ; ... |- ( or phi psi ) $.
  $( Disjunction Introduction (right side) $)
  axm.or-intr-2 $a ; ... |- ( or psi phi ) $.
$}

${
  axm.implies-intr.1 $e ; ... phi |- psi $.
  $( Implication Introduction $)
  axm.implies-intr   $a ; ... |- ( implies phi psi ) $.
$}

${
  axm.iff-intr.1 $e ; ... phi |- psi $.
  axm.iff-intr.2 $e ; ... psi |- phi $.
  $( Biconditional Introduction $)
  axm.iff-intr   $a ; ... |- ( iff phi psi ) $.
$}

${
  axm.not-intr.1 $e ; ... phi |- false $.
  $( Negation Introduction $)
  axm.not-intr   $a ; ... |- ( not phi ) $.
$}

$( Verum Introduction $)
axm.true-intr $a ; ... |- true $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
Elimination Rules
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
$)

${
  axm.and-elim.1 $e ; ... |- ( and phi psi ) $.
  $( Conjunction Elimination (left side) $)
  axm.and-elim-1 $a ; ... |- phi $.
  $( Conjunction Elimination (right side) $)
  axm.and-elim-2 $a ; ... |- psi $.
$}

${
  axm.or-elim.1 $e ; ... |- ( or phi psi ) $.
  axm.or-elim.2 $e ; ... phi |- chi $.
  axm.or-elim.3 $e ; ... psi |- chi $.
  $( Disjunction Elimination $)
  axm.or-elim   $a ; ... |- chi $.
$}

${
  axm.implies-elim.1 $e ; ... |- ( implies phi psi ) $.
  axm.implies-elim.2 $e ; ... |- phi $.
  $( Implication Elimination $)
  axm.implies-elim   $a ; ... |- psi $.
$}

${
  axm.iff-elim-1.1 $e ; ... |- ( iff phi psi ) $.
  axm.iff-elim-1.2 $e ; ... |- phi $.
  $( Biconditional Elimination (rightwards direction) $)
  axm.iff-elim-1   $a ; ... |- psi $.
$}

${
  axm.iff-elim-2.1 $e ; ... |- ( iff phi psi ) $.
  axm.iff-elim-2.2 $e ; ... |- psi $.
  $( Biconditional Elimination (leftwards direction) $)
  axm.iff-elim-2   $a ; ... |- phi $.
$}

${
  axm.not-elim.1 $e ; ... |- phi $.
  axm.not-elim.2 $e ; ... |- ( not phi ) $.
  $( Negation Elimination $)
  axm.not-elim   $a ; ... |- false $.
$}

${
  axm.false-elim.1 $e ; ... |- false $.
  $( Falsum Elimination $)
  axm.false-elim   $a ; ... |- phi $.
$}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
Other Rules
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
$)

${
  axm.ip.1 $e ; ... ( not phi ) |- false $.
  $( Indirect Proof:
     A form of reductio ad absurdum, or proof by contradiction.
     Because this allows us to derive the law of excluded middle, this separates
     intuitionistic from classical logic. $)
  axm.ip   $a ; ... |- phi $.
$}

$( Assumption Rule:
   We can assume something for the sake of argument. $)
axm.assume $a ; ... phi |- phi $.


${
  axm.thin.1 $e ; ..._1 |- phi $.
  $( Thinning Rule:
     Also called "weakening". We can always add unused assumptions to our
     claims. This is needed because we are presenting natural deduction in
     sequent-style to work in Metamath, but in a Fitch-style proof this is used
     implicitly whenever a subproof uses a result from an outer proof. $)
  axm.thin   $a ; ..._1 ..._2 |- phi $.
$}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*
Predicate Logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*
$)

$( Introduce some new grammatical types:
   variables, quantifiers, predicates, functions, terms, lists of terms $)
$c var qnt prd func trm lst $.

$( Introduce variables:
   We will adhere to the style of using letters a-r for eigenvariables and
   letters s-z for regular variables, though this is not enforced by our
   formalization. $)
$v a b c d e f g h i j k l m n o p q r s t u v w x y z $.
var.a $f var a $.
var.b $f var b $.
var.c $f var c $.
var.d $f var d $.
var.e $f var e $.
var.f $f var f $.
var.g $f var g $.
var.h $f var h $.
var.i $f var i $.
var.j $f var j $.
var.k $f var k $.
var.l $f var l $.
var.m $f var m $.
var.n $f var n $.
var.o $f var o $.
var.p $f var p $.
var.q $f var q $.
var.r $f var r $.
var.s $f var s $.
var.t $f var t $.
var.u $f var u $.
var.v $f var v $.
var.w $f var w $.
var.x $f var x $.
var.y $f var y $.
var.z $f var z $.

$( Metavariables for grammatical types $)
$v qnt_1 $.
qnt.qnt_1 $f qnt qnt_1 $.

$v prd_1 $.
prd.prd_1 $f prd prd_1 $.

$v func_1 $.
func.func_1 $f func func_1 $.

$v trm_1 trm_2 trm_3 trm_4 trm_5 $.
trm.trm_1 $f trm trm_1 $.
trm.trm_2 $f trm trm_2 $.
trm.trm_3 $f trm trm_3 $.
trm.trm_4 $f trm trm_4 $.
trm.trm_5 $f trm trm_5 $.

$v ..t ..u ..v ..w $.
lst.t $f lst ..t $.
lst.u $f lst ..u $.
lst.v $f lst ..v $.
lst.w $f lst ..w $.

$( Recursively define the syntax for a list of terms

   These will be used for listing the arguments of functions and predicates.
   Unlike lists of WFFs used for assumption contexts, we do not need to
   consider the case where argument lists are empty.

   This is because the special case where a function has no arguments can be
   seen as just a constant (and we can introduce constants simply by giving
   a symbol the grammatical type of a term).

   Likewise the special case where a predicate has no arguments can be seen as
   a propositional constant, of which there are only two possibilities: always
   true or always false. These are already expressed by the logical primitives
   verum and falsum. $)

$( A list may contain a single term $)
lst.singleton $a lst trm_1 $.
$( Two lists may be concatenated to form a new list $)
lst.concat $a lst ..t ..u $.

lst.append $p lst ..t trm_1 $= ( lst.singleton lst.concat ) BACD $.
lst.prepend $p lst trm_1 ..t $= ( lst.singleton lst.concat ) ACBD $.

$( A predicate symbol followed by its arguments is a WFF.

   For the simplicity of our grammar we do not enforce arity here.
   However, when introducing new predicates, we will follow the convention of
   only allowing definitions to be meaningful (and useful) for a fixed number
   of arguments.
   (The same will go for functions) $)
wff.atm $a wff ( prd_1 ..t ) $.

$( A quantified formula is a WFF $)
wff.qnt $a wff ( qnt_1 x phi ) $.

$( Variables are terms $)
trm.var $a trm x $.

$( A function symbol followed by its arguments is a term $)
trm.func $a trm ( func_1 ..t ) $.

$( Introduce the quantifiers $)
$c forall exists $.
qnt.forall $a qnt forall $.
qnt.exists $a qnt exists $.

$( Introduce the equality predicate $)
$c eq $.
prd.eq $a prd eq $.

$( We will use variables prefixed with an underscore to indicate they are
   "internal", i.e., not occuring in the original Fitch proof but needed to
   complete the generated proof. $)
$v _a _x _trm_1 $.
var._a     $f var _a $.
var._x     $f var _x $.
var._trm_1 $f var _trm_1 $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
Non-Freeness & Proper Substitution
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-

The intelim rules of predicate logic depend on the notions of free/bound
variables as well as proper (capture-avoiding) substitution, so we must define
these first.

We will first define these as statements of a different type than sequents, so
that they may be treated as metalogical side-conditions. Later on we will use
these statements to define a substitution operator so that it may be used within
logical formulae, corresponding to the common notation [t/x] meaning "substitute
t for x".

Unlike set.mm, we will define these with a recursive syntactic breakdown on WFFs
and terms, rather than expressing them via equivalences. Because of this, we
will also introduce the syntax for the substitution operator here before it is
defined, so that it can be recursed through.
$)

$c NONFREE REPLACES WITH IN sub $.

stmt.nf-wffs $a stmt NONFREE x ... $.
stmt.nf-trms $a stmt NONFREE x ..t $.

stmt.sub-wff $a stmt phi REPLACES x IN psi WITH trm_1 $.
stmt.sub-lst $a stmt ..t REPLACES x IN ..u WITH trm_1 $.

$( Substitution operator $)
wff.sub $a wff ( sub trm_1 x phi ) $.
$( Overload the substitution operator for terms $)
trm.sub $a trm ( sub trm_1 x trm_2 ) $.

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.
Nonfreeness for terms
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.
$)

${
  $d x ..t $.
  $( A variable that does not occur in a list is not free $)
  nf.lst-none $a ; NONFREE x ..t $.
$}

${
  $d x trm_1 $.
  $( A variable that does not occur in a term is not free $)
  nf.trm-none $p ; NONFREE x trm_1 $=
    ( lst.singleton nf.lst-none ) ABCD $.
$}

${
  nf.trm-func.1 $e ; NONFREE x ..t $.
  $( A variable is nonfree in an instance of function application when it is
     nonfree in its arguments $)
  nf.trm-func   $a ; NONFREE x ( func_1 ..t ) $.
$}

${
  nf.trm-sub-1.1 $e ; NONFREE x trm_1 $.
  $( Nonfreeness for substitution (case where variables are the same)
     A variable that does not occur because it is substituted with a different
     term is not free (hence we do not need a hypothesis that it is also
     nonfree in trm_2). $)
  nf.trm-sub-1   $a ; NONFREE x ( sub trm_1 x trm_2 ) $.
$}

${
  $d x y $.
  nf.trm-sub-2.1 $e ; NONFREE x trm_1 $.
  nf.trm-sub-2.2 $e ; NONFREE x trm_2 $.
  $( Nonfreeness for substitution (case where variables are distinct) $)
  nf.trm-sub-2   $a ; NONFREE x ( sub trm_1 y trm_2 ) $.
$}

${
  nf.lst.1 $e ; NONFREE x ..t $.
  nf.lst.2 $e ; NONFREE x ..u $.
  $( Nonfreeness for lists of terms $)
  nf.lst   $a ; NONFREE x ..t ..u $.
$}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.
Nonfreeness for WFFs
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.
$)

${
  $d x ... $.
  $( A variable that does not occur in a context is not free $)
  nf.ctx-none $a ; NONFREE x ... $.
$}

${
  $d x phi $.
  $( A variable that does not occur in a WFF is not free $)
  nf.wff-none $p ; NONFREE x phi $=
    ( ctx.empty ctx.append nf.ctx-none ) CADBE $.
$}

${ 
  $( Nonfreeness for the binary connectives $)
  nf.wff-bin.1   $e ; NONFREE x phi $.
  nf.wff-bin.2   $e ; NONFREE x psi $.
  nf.wff-and     $a ; NONFREE x ( and phi psi ) $.
  nf.wff-or      $a ; NONFREE x ( or phi psi ) $.
  nf.wff-implies $a ; NONFREE x ( implies phi psi ) $.
  nf.wff-iff     $a ; NONFREE x ( iff phi psi ) $.
$}

${ 
  nf.wff-not.1 $e ; NONFREE x phi $.
  $( Nonfreeness for negation $)
  nf.wff-not   $a ; NONFREE x ( not phi ) $.
$}

${
  nf.wff-prd.1 $e ; NONFREE x ..t $.
  $( A variable is nonfree in a predicate when it is nonfree in its arguments $)
  nf.wff-prd   $a ; NONFREE x ( prd_1 ..t ) $.
$}

$( Nonfreeness for quantifiers (case where variables are the same)
   A variable that is bound by a quantifier is not free. $)
nf.wff-qnt-1 $a ; NONFREE x ( qnt_1 x phi ) $.

${
  $d x y $.
  nf.wff-qnt-2.1 $e ; NONFREE x phi $.
  $( Nonfreeness for quantifiers (case where variables are distinct) $)
  nf.wff-qnt-2   $a ; NONFREE x ( qnt_1 y phi ) $.
$}

${
  nf.wff-sub-1.1 $e ; NONFREE x trm_1 $.
  $( Nonfreeness for substitution (case where variables are the same)
     A variable that does not occur because it is substituted with a different
     term is not free (hence we do not need a hypothesis that it is also
     nonfree in phi). $)
  nf.wff-sub-1   $a ; NONFREE x ( sub trm_1 x phi ) $.
$}

${
  $d x y $.
  nf.wff-sub-2.1 $e ; NONFREE x trm_1 $.
  nf.wff-sub-2.2 $e ; NONFREE x phi $.
  $( Nonfreeness for substitution (case where variables are distinct) $)
  nf.wff-sub-2   $a ; NONFREE x ( sub trm_1 y phi ) $.
$}

${ 
  nf.ctx.1 $e ; NONFREE x ..._1 $.
  nf.ctx.2 $e ; NONFREE x ..._2 $.
  $( Nonfreeness for lists of WFFs $)
  nf.ctx   $a ; NONFREE x ..._1 ..._2 $.
$}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.
Proper Substitution for Terms
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.

We say that "t1 REPLACES x IN t2 WITH t3" when t1 is obtained by substituting
every free occurrence of x in t2 with t3.
$)

$( Replacing a single variable with a term just yields that term $)
sub.trm-rep $a ; trm_1 REPLACES x IN x WITH trm_1 $.

${
  sub.trm-none.1 $e ; NONFREE x trm_1 $.
  $( Nothing is replaced in a term when there are no free occurrences $)
  sub.trm-none   $a ; trm_1 REPLACES x IN trm_1 WITH trm_2 $.
$}

$( Replacing a variable with itself has no effect $)
sub.trm-id $a ; trm_1 REPLACES x IN trm_1 WITH x $.

${
  sub.lst.1 $e ; ..t REPLACES x IN ..u WITH trm_1 $.
  sub.lst.2 $e ; ..v REPLACES x IN ..w WITH trm_1 $.
  $( Recursively handle replacement for lists of terms $)
  sub.lst   $a ; ..t ..v REPLACES x IN ..u ..w WITH trm_1 $.
$}

${ 
  sub.trm-func.1 $e ; ..t REPLACES x IN ..u WITH trm_1 $.
  $( A function replaces if all its arguments do $)
  sub.trm-func   $a ; ( func_1 ..t ) REPLACES x IN ( func_1 ..u ) WITH trm_1 $.
$}

${
  sub.trm-sub-1.1 $e ; trm_1 REPLACES x IN trm_2 WITH trm_4 $.
  $( Replacement over the substitution operator (case where variables are the same)
     The only occurrences (if any) of x in the expression t3[t2/x] are its
     occurrences in the term t2 (its occurrences in t3 are substituted away).
     Thus we only need to recursively check replacement over t2, and t3 should
     remain unchanged. $)
  sub.trm-sub-1   $a ; ( sub trm_1 x trm_3 ) REPLACES x IN
                       ( sub trm_2 x trm_3 ) WITH trm_4 $.
$}

${
  $d x y $.
  sub.trm-sub-2.1 $e ; NONFREE y trm_5 $.
  sub.trm-sub-2.2 $e ; trm_1 REPLACES x IN trm_2 WITH trm_5 $.
  sub.trm-sub-2.3 $e ; trm_3 REPLACES x IN trm_4 WITH trm_5 $.
  $( Replacement over the substitution operator (case where variables are distinct)
     The nonfreeness hypothesis acts analogously to the capture-avoidance
     condition for quantifiers: we do not want the term being inserted to
     contain the variable that the outer substitution is replacing, lest the
     substitution tacitly tampers with it. $)
  sub.trm-sub-2   $a ; ( sub trm_1 y trm_3 ) REPLACES x IN
                       ( sub trm_2 y trm_4 ) WITH trm_5 $.
$}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.
Proper Substitution for WFFs
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.

We say that "phi REPLACES x IN psi WITH t" when phi is obtained by substituting
every free occurrence of x in psi with t.

Here we must also require the substitution to be capture-avoiding. That is, x
should not be within the scope of a quantifier that uses a variable y also in
t, lest y becomes illegitimately bound to it ("captured") on substitution.
$)

${ 
  sub.wff-none.1 $e ; NONFREE x phi $.
  $( Nothing is replaced in a WFF when there are no free occurrences $)
  sub.wff-none   $a ; phi REPLACES x IN phi WITH trm_1 $.
$}

$( Replacing a variable with itself has no effect $)
sub.wff-id $a ; phi REPLACES x IN phi WITH x $.

${
  $( Define for the binary connectives $)
  sub.wff-bin.1 $e ; phi_1 REPLACES x IN phi_2 WITH trm_1 $.
  sub.wff-bin.2 $e ; psi_1 REPLACES x IN psi_2 WITH trm_1 $.

  $( Recurse replacement through conjunction $)
  sub.wff-and     $a ; ( and phi_1 psi_1 )     REPLACES x IN
                       ( and phi_2 psi_2 )     WITH trm_1 $.
  $( Recurse replacement through disjunction $)
  sub.wff-or      $a ; ( or phi_1 psi_1 )      REPLACES x IN
                       ( or phi_2 psi_2 )      WITH trm_1 $.
  $( Recurse replacement through implication $)
  sub.wff-implies $a ; ( implies phi_1 psi_1 ) REPLACES x IN
                       ( implies phi_2 psi_2 ) WITH trm_1 $.
  $( Recurse replacement through the biconditional $)
  sub.wff-iff     $a ; ( iff phi_1 psi_1 )     REPLACES x IN
                       ( iff phi_2 psi_2 )     WITH trm_1 $.
$}

${
  sub.wff-not.1 $e ; phi_1 REPLACES x IN phi_2 WITH trm_1 $.
  $( Recurse replacement through negation $)
  sub.wff-not   $a ; ( not phi_1 ) REPLACES x IN ( not phi_2 ) WITH trm_1 $.
$}

${ 
  sub.wff-prd.1 $e ; ..t REPLACES x IN ..u WITH trm_1 $.
  $( A predicate replaces if all its arguments do $)
  sub.wff-prd   $a ; ( prd_1 ..t ) REPLACES x IN ( prd_1 ..u ) WITH trm_1 $.
$}

${
  $d x y $.
  sub.wff-qnt.1 $e ; NONFREE y trm_1 $.
  sub.wff-qnt.2 $e ; phi REPLACES x IN psi WITH trm_1 $.
  $( Define substitution for quantifiers. The nonfreeness hypothesis acts to
     avoid variable capture on y. Variables x and y must be distinct to prevent
     the invalid replacement of bound occurences (the case where x and y are the
     same is covered by sub.wff-none). $)
  sub.wff-qnt   $a ; ( qnt_1 y phi ) REPLACES x IN ( qnt_1 y psi ) WITH trm_1 $.
$}

${
  sub.wff-sub-1.1 $e ; trm_1 REPLACES x IN trm_2 WITH trm_3 $.
  $( Replacement over the substitution operator (case where variables are the same)
     The only occurrences (if any) of x in the expression phi[t/x] are its
     occurrences in the term t. Thus we only need to recursively check
     replacement over t, and phi should remain unchanged. $)
  sub.wff-sub-1   $a ; ( sub trm_1 x phi ) REPLACES x IN
                       ( sub trm_2 x phi ) WITH trm_3 $.
$}

${
  $d x y $.
  sub.wff-sub-2.1 $e ; NONFREE y trm_3 $.
  sub.wff-sub-2.2 $e ; trm_1 REPLACES x IN trm_2 WITH trm_3 $.
  sub.wff-sub-2.3 $e ; phi REPLACES x IN psi WITH trm_3 $.
  $( Replacement over the substitution operator (case where variables are distinct)
     The nonfreeness hypothesis acts analogously to the capture-avoidance
     condition on quantifiers: we do not want the term being inserted to contain
     the variable that the outer substitution is replacing, lest the substitution
     tacitly tampers with it. $)
  sub.wff-sub-2   $a ; ( sub trm_1 y phi ) REPLACES x IN
                       ( sub trm_2 y psi ) WITH trm_3 $.
$}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
Introduction Rules
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
$)

${ 
  axm.forall-intr.1 $e ; NONFREE a ... $.
  axm.forall-intr.2 $e ; NONFREE x phi $.
  axm.forall-intr.3 $e ; psi REPLACES a IN phi WITH x $.
  axm.forall-intr.4 $e ; ... |- phi $. 
  $( Universal Introduction $)
  axm.forall-intr   $a ; ... |- ( forall x psi ) $. 
$}

${ 
  axm.exists-intr.1 $e ; phi REPLACES x IN psi WITH trm_1 $.
  axm.exists-intr.2 $e ; ... |- phi $. 
  $( Existential Introduction $)
  axm.exists-intr   $a ; ... |- ( exists x psi ) $. 
$}

$( Equality Introduction $)
axm.eq-intr $a ; ... |- ( eq trm_1 trm_1 ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
Elimination Rules
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
$)

${ 
  axm.forall-elim.1 $e ; psi REPLACES x IN phi WITH trm_1 $.
  axm.forall-elim.2 $e ; ... |- ( forall x phi ) $. 
  $( Universal Elimination $)
  axm.forall-elim   $a ; ... |- psi $. 
$}

${ 
  axm.exists-elim.1 $e ; NONFREE a ... $.
  axm.exists-elim.2 $e ; NONFREE a phi $.
  axm.exists-elim.3 $e ; NONFREE a chi $.
  axm.exists-elim.4 $e ; psi REPLACES x IN phi WITH a $.
  axm.exists-elim.5 $e ; ... |- ( exists x phi ) $. 
  axm.exists-elim.6 $e ; ... psi |- chi $. 
  $( Existential Elimination $)
  axm.exists-elim   $a ; ... |- chi $. 
$}

${ 
  $d x trm_1 $. $d x trm_2 $.
  axm.eq-elim-1.1 $e ; phi REPLACES x IN chi WITH trm_1 $.
  axm.eq-elim-1.2 $e ; psi REPLACES x IN chi WITH trm_2 $.
  axm.eq-elim-1.3 $e ; ... |- ( eq trm_1 trm_2 ) $.
  axm.eq-elim-1.4 $e ; ... |- phi $.
  $( Equality Elimination $)
  axm.eq-elim-1   $a ; ... |- psi $.
$}

${ 
  $d x trm_1 $. $d x trm_2 $.
  thm.eq-elim-2.1 $e ; phi REPLACES x IN chi WITH trm_1 $.
  thm.eq-elim-2.2 $e ; psi REPLACES x IN chi WITH trm_2 $.
  thm.eq-elim-2.3 $e ; ... |- ( eq trm_1 trm_2 ) $.
  thm.eq-elim-2.4 $e ; ... |- psi $.
  $( The reverse direction of equality elimination is in fact derivable as a
     theorem in our system, but in Fitch-style proofs we will permit using
     "axm.eq-elim" to refer to either one. $)
  thm.eq-elim-2   $p ; ... |- phi $= 
    ( prd.eq lst.singleton lst.concat wff.atm sub.trm-rep sub.wff-prd
    sub.trm-none sub.lst axm.eq-elim-1 nf.lst-none axm.eq-intr trm.var ) ACBDEGF
    IHALFMZUDNZOLGMZUDNZOLEUCMZUDNZOEFGELFUEUIEFUDUHUDUDEFPEFFEUDUAZRSQELGUGUIEG
    UFUHUDUDEGPEFGUJRSQJAFUBTKT $.
$}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
Definitions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
$)

stmt.def $a stmt phi := psi $.

${ 
  axm.def-intr.1 $e ; phi := psi $.
  axm.def-intr.2 $e ; ... |- psi $.
  $( Definiendum Introduction $)
  axm.def-intr   $a ; ... |- phi $.
$}

${ 
  axm.def-elim.1 $e ; phi := psi $.
  axm.def-elim.2 $e ; ... |- phi $.
  $( Definiendum Elimination $)
  axm.def-elim   $a ; ... |- psi $.
$}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.
Substitution Operator
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.
$)

${
  def.sub-wff.1 $e ; psi REPLACES x IN phi WITH trm_1 $.
  $( Define the substitution operator for WFFs $)
  def.sub-wff   $a ; ( sub trm_1 x phi ) := psi $.
$}

${
  def.sub-trm.1 $e ; trm_2 REPLACES x IN trm_3 WITH trm_4 $.
  $( Define the substitution operator for terms $)
  def.sub-trm   $a ; ( eq trm_1 ( sub trm_4 x trm_3 ) ) := ( eq trm_1 trm_2 ) $.
$}

$( We will also require special rules for substitution to allow rules that have
   replacement hypotheses to recognize when the substitution operator may be
   introduced or eliminated. $)

$( Substitution introduction for terms $)
sub.trm-intr $a ; ( sub trm_1 x trm_2 ) REPLACES x IN trm_2 WITH trm_1 $.

$( Substitution introduction for WFFs $)
sub.wff-intr $a ; ( sub trm_1 x phi ) REPLACES x IN phi WITH trm_1 $.

${
  sub.trm-elim.1 $e ; NONFREE y trm_1 $.
  $( Substitution elimination for terms
     Replacing a variable back with the original variable returns us to the
     original term, so long as the intermediate variable was fresh (nonfree in
     the original term). $)
  sub.trm-elim   $a ; trm_1 REPLACES y IN ( sub y x trm_1 ) WITH x $.
$}

${
  sub.wff-elim.1 $e ; NONFREE y phi $.
  $( Substitution elimination for WFFs
     Replacing a variable back with the original variable returns us to the
     original formula, so long as the intermediate variable was fresh (nonfree
     in the original formula). $)
  sub.wff-elim   $a ; phi REPLACES y IN ( sub y x phi ) WITH x $.
$}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.
Uniqueness Quantification
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.
$)

$c unique $.
qnt.unique $a qnt unique $.
${
  $d y phi $.
  $( Define the uniqueness quantifier $)
  def.unique $a ; ( unique x phi ) :=
                  ( exists x ( and phi ( forall y ( implies
                                                    ( sub y x phi ) 
                                                    ( eq y x ) ) ) ) ) $.
$}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*
Substitution of Equivalents & Rules of Replacement
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*

Two formulae are considered logically equivalent if their material biconditional
is a tautology (i.e., provable in the empty context).

If two WFFs are logically equivalent, they can generally be swapped for one
another in any arbitrary formula without affecting its truth-value. This allows
us to express "rules of replacement" that allow us to infer a new statement by
replacing some segments of it with logically equivalent ones.

Compared to the other rules of inference, these have the advantage of being able
to operate on not just on the whole formula but also on subformulae. This is
useful because it can spare us from having to dis- and reassemble an entire formula
to change only part of it.

In this section we will prove some results demonstrating that for each of our
logical operators, their interchangeability (in any context) follows from the
logical equivalence of their subformulae.
$)

thm.eqv-id $p ; ... |- ( iff phi phi ) $=
  ( axm.assume axm.iff-intr ) ABBABCZED $.

${
  thm.eqv-and.1 $e ; |- ( iff phi_1 phi_2 ) $.
  thm.eqv-and.2 $e ; |- ( iff psi_1 psi_2 ) $.
  thm.eqv-and   $p ; ... |- ( iff ( and phi_1 psi_1 ) ( and phi_2 psi_2 ) ) $= 
    ( ctx.empty ctx.append ctx.singleton axm.thin axm.and-elim-1 axm.iff-elim-1
    wff.and axm.assume axm.and-elim-2 axm.and-intr axm.iff-elim-2 axm.iff-intr
    wff.iff ) HABCNZDENZTHUAUBHUAIZDEUCBDHUAJZBDTZFKUCBCHUAOZLMUCCEHUDCETZGKUCBC
    UFPMQHUBIZBCUHBDHUBJZUEFKUHDEHUBOZLRUHCEHUIUGGKUHDEUJPRQSK $.
$}

${
  thm.eqv-or.1 $e ; |- ( iff phi_1 phi_2 ) $.
  thm.eqv-or.2 $e ; |- ( iff psi_1 psi_2 ) $.
  thm.eqv-or   $p ; ... |- ( iff ( or phi_1 psi_1 ) ( or phi_2 psi_2 ) ) $= 
    ( ctx.empty wff.or wff.iff ctx.append ctx.singleton axm.thin axm.iff-elim-1
    axm.or-intr-1 axm.or-intr-2 axm.or-elim axm.iff-elim-2 axm.iff-intr
    axm.assume ) HABCIZDEIZJHUAUBHUAKZBCUBHUATUCBKZDEUDBDHUALZBKBDJZFMUCBTNOUCCK
    ZEDUGCEHUECKCEJZGMUCCTNPQHUBKZDEUAHUBTUIDKZBCUJBDHUBLZDKUFFMUIDTROUIEKZCBULC
    EHUKEKUHGMUIETRPQSM $. 
$}

${
  thm.eqv-implies.1 $e ; |- ( iff phi_1 phi_2 ) $.
  thm.eqv-implies.2 $e ; |- ( iff psi_1 psi_2 ) $.
  thm.eqv-implies   $p ; ... |- ( iff
                                  ( implies phi_1 psi_1 )
                                  ( implies phi_2 psi_2 ) ) $= 
    ( wff.implies ctx.append ctx.singleton axm.thin axm.assume axm.implies-elim
    ctx.empty axm.iff-elim-2 axm.iff-elim-1 axm.implies-intr axm.iff-intr
    wff.iff ) NABCHZDEHZSNTUANTIZDEUBDIZCENTJDIZCESZGKUCBCUBDJTNTLKUCBDNUDBDSZFK
    UBDLOMPQNUAIZBCUGBIZCENUAJBIZUEGKUHDEUGBJUANUALKUHBDNUIUFFKUGBLPMOQRK $.
$}

${
  thm.eqv-iff.1 $e ; |- ( iff phi_1 phi_2 ) $.
  thm.eqv-iff.2 $e ; |- ( iff psi_1 psi_2 ) $.
  thm.eqv-iff   $p ; ... |- ( iff ( iff phi_1 psi_1 ) ( iff phi_2 psi_2 ) ) $= 
    ( ctx.empty ctx.append ctx.singleton axm.thin axm.iff-elim-2 axm.iff-elim-1
    wff.iff axm.assume axm.iff-intr ) HABCNZDENZNHQRHQIZDESDIZCEHQJZDIZCENZGKTBC
    SDJQHQOZKTBDHUBBDNZFKSDOLMMSEIZBDHUAEIZUEFKUFBCSEJQUDKUFCEHUGUCGKSEOLLMPHRIZ
    BCUHBIZCEHRJZBIZUCGKUIDEUHBJRHROZKUIBDHUKUEFKUHBOMMLUHCIZBDHUJCIZUEFKUMDEUHC
    JRULKUMCEHUNUCGKUHCOMLLPPK $.
$}

${
  $d x y $. $d y phi $. $d y psi $.
  thm.eqv-sub.1 $e ; |- ( iff phi psi ) $.
  thm.eqv-sub   $p ; ... |- ( iff ( sub trm_1 x phi ) ( sub trm_1 x psi ) ) $= 
    ( ctx.empty wff.sub wff.iff sub.wff-iff def.sub-wff nf.ctx-none nf.trm-none
    var.y sub.wff-intr nf.wff-sub-1 nf.wff-none axm.forall-intr axm.forall-elim
    trm.var sub.wff-elim sub.wff-id axm.def-elim axm.thin ) GABDEHZCDEHZIZGBCIZD
    EHZUGUHUGDEUEUFBCDEBDEOCDEOJKGUHUIDEUHDEOGUHDNTZHZUHNDGNLUHDUJDUJMPUHDNUHNQZ
    UAGUKUKNUJUKNUBGUHUKDNGDLULUHDUJOFRSRSUCUD $.
$}

${
  $d a x $. $d a phi $. $d a psi $.
  thm.eqv-forall.1 $e ; |- ( iff phi psi ) $.
  thm.eqv-forall   $p ; ... |- ( iff ( forall x phi ) ( forall x psi ) ) $= 
    ( var.a ctx.empty qnt.forall wff.qnt wff.iff ctx.append wff.sub nf.ctx-none
    nf.wff-sub-1 nf.wff-none sub.wff-elim ctx.singleton sub.wff-intr axm.assume
    axm.thin trm.var nf.trm-none axm.forall-elim axm.iff-elim-1 axm.forall-intr
    thm.eqv-sub axm.iff-elim-2 axm.iff-intr ) GABDHIZCDHIZJGUIUJGUIKZCDFUAZLZCFD
    UKFMCDULDULUBZNCDFCFOPUKBDULLZUMGUIQUOUMJZGBCDULEUFZTUKBUODULBDULRGUISUCUDUE
    GUJKZUOBFDURFMBDULUNNBDFBFOPURUOUMGUJQUPUQTURCUMDULCDULRGUJSUCUGUEUHT $.
$}

${
  $d a x $. $d a phi $. $d a psi $.
  thm.eqv-exists.1 $e ; |- ( iff phi psi ) $.
  thm.eqv-exists   $p ; ... |- ( iff ( exists x phi ) ( exists x psi ) ) $= 
    ( var.a ctx.empty qnt.exists wff.qnt wff.iff ctx.append wff.sub nf.ctx-none
    nf.wff-none sub.wff-intr axm.assume ctx.singleton axm.thin axm.exists-intr
    axm.exists-elim thm.eqv-sub axm.iff-elim-1 axm.iff-elim-2 axm.iff-intr
    trm.var ) GABDHIZCDHIZJGUFUGGUFKZBBDFUEZLZUGFDUHFMBFNUGFNBDUIOZGUFPUHUJKZCDU
    ILZCDUICDUIOZULUJUMGUFQUJKUJUMJZGBCDUIEUAZRUHUJPUBSTGUGKZCUMUFFDUQFMCFNUFFNU
    NGUGPUQUMKZUJBDUIUKURUJUMGUGQUMKUOUPRUQUMPUCSTUDR $.
$}

${
  $d x y $. $d y phi $. $d y psi $.
  thm.eqv-unique.1 $e ; |- ( iff phi psi ) $.
  thm.eqv-unique   $p ; ... |- ( iff ( unique x phi ) ( unique x psi ) ) $= 
    ( var.y ctx.empty qnt.unique wff.qnt wff.iff ctx.append trm.var wff.implies
    wff.sub qnt.forall wff.and qnt.exists def.unique ctx.singleton axm.thin
    prd.eq lst.singleton lst.prepend thm.eqv-sub thm.eqv-implies thm.eqv-forall
    wff.atm thm.eqv-and thm.eqv-exists axm.def-elim axm.iff-elim-1 axm.def-intr
    thm.eqv-id axm.assume axm.iff-elim-2 axm.iff-intr ) GABDHIZCDHIZJGUQURGUQKZU
    RCCDFLZNZUAUTDLUBUCUGZMZFOIZPZDQIZCDFRZUSBBDUTNZVBMZFOIZPZDQIZVFGUQSVLVFJZGV
    KVEDGBVJCVDEGVIVCFGVHVBVAVBGBCDUTEUDGVBUMUEUFUHUIZTUSUQVLBDFRZGUQUNUJUKULGUR
    KZUQVLVOVPVLVFGURSVMVNTVPURVFVGGURUNUJUOULUPT $. 
$}