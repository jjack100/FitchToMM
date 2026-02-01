$(
--------------------------------------------------------------------------------
Formal Grammar
--------------------------------------------------------------------------------

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
$v ... $.
ctx.ellipsis  $f ctx ... $.

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

$( Recursively define a context $)
ctx.empty $a ctx $. $( Base case is the empty context $)
ctx.append $a ctx ... phi $. $( Recursive case: a context followed by a WFF $)

$( Syntax for judgements $)
stmt.jdg $a stmt ... |- phi $.

$(
--------------------------------------------------------------------------------
Propositional Logic
--------------------------------------------------------------------------------
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

$( -------- Introduction Rules -------- $)

${ $( Conjunction Introduction $)
  axm.and-intr.1 $e ; ... |- phi $.
  axm.and-intr.2 $e ; ... |- psi $.
  axm.and-intr   $a ; ... |- ( and phi psi ) $.
$}

${ $( Disjunction Introduction $)
  axm.or-intr.1 $e ; ... |- phi $.
  axm.or-intr-1 $a ; ... |- ( or phi psi ) $.
  axm.or-intr-2 $a ; ... |- ( or psi phi ) $.
$}

${ $( Implication Introduction $)
  axm.implies-intr.1 $e ; ... phi |- psi $.
  axm.implies-intr   $a ; ... |- ( implies phi psi ) $.
$}

${ $( Biconditional Introduction $)
  axm.iff-intr.1 $e ; ... phi |- psi $.
  axm.iff-intr.2 $e ; ... psi |- phi $.
  axm.iff-intr   $a ; ... |- ( iff phi psi ) $.
$}

${ $( Negation Introduction $)
  axm.not-intr.1 $e ; ... phi |- false $.
  axm.not-intr   $a ; ... |- ( not phi ) $.
$}

$( Verum Introduction $)
axm.true-intr $a ; ... |- true $.

$( -------- Elimination Rules -------- $)

${ $( Conjunction Elimination $)
  axm.and-elim.1 $e ; ... |- ( and phi psi ) $.
  axm.and-elim-1 $a ; ... |- phi $.
  axm.and-elim-2 $a ; ... |- psi $.
$}

${ $( Disjunction Elimination $)
  axm.or-elim.1 $e ; ... |- ( or phi psi ) $.
  axm.or-elim.2 $e ; ... phi |- chi $.
  axm.or-elim.3 $e ; ... psi |- chi $.
  axm.or-elim   $a ; ... |- chi $.
$}

${ $( Implication Elimination $)
  axm.implies-elim.1 $e ; ... |- ( implies phi psi ) $.
  axm.implies-elim.2 $e ; ... |- phi $.
  axm.implies-elim   $a ; ... |- psi $.
$}

${ $( Biconditional Elimination $)
  axm.iff-elim-1.1 $e ; ... |- ( iff phi psi ) $.
  axm.iff-elim-1.2 $e ; ... |- phi $.
  axm.iff-elim-1   $a ; ... |- psi $.
$} ${
  axm.iff-elim-2.1 $e ; ... |- ( iff phi psi ) $.
  axm.iff-elim-2.2 $e ; ... |- psi $.
  axm.iff-elim-2   $a ; ... |- phi $.
$}

${ $( Negation Elimination $)
  axm.not-elim.1 $e ; ... |- phi $.
  axm.not-elim.2 $e ; ... |- ( not phi ) $.
  axm.not-elim   $a ; ... |- false $.
$}

${ $( Falsum Elimination $)
  axm.false-elim.1 $e ; ... |- false $.
  axm.false-elim   $a ; ... |- phi $.
$}

$( -------- Other Rules -------- $)

$( Indirect Proof:
   A form of reductio ad absurdum, or proof by contradiction.
   Because this allows us to derive the law of excluded middle, this separates
   intuitionistic from classical logic. $)
${
  axm.ip.1 $e ; ... ( not phi ) |- false $.
  axm.ip   $a ; ... |- phi $.
$}

$( Assumption Rule:
   We can assume something for the sake of argument. $)
axm.assume $a ; ... phi |- phi $.

$( Thinning Rule:
   Also called "weakening". We can always add unused assumptions to our claims.
   This is needed because we are presenting natural deduction in sequent-style
   to work in Metamath, but in a Fitch-style proof this is used implicitly
   whenever a subproof uses a result from an outer proof. $)
${
  axm.thin.1 $e ; ... |- phi $.
  axm.thin   $a ; ... psi |- phi $.
$}

$(
--------------------------------------------------------------------------------
Predicate Logic
--------------------------------------------------------------------------------
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

$v trm_1 trm_2 trm_3 $.
trm.trm_1 $f trm trm_1 $.
trm.trm_2 $f trm trm_2 $.
trm.trm_3 $f trm trm_3 $.

$v ..t ..u $.
lst.t $f lst ..t $.
lst.u $f lst ..u $.

$( Recursively define a list of terms $)
lst.single $a lst trm_1 $.
lst.append $a lst ..t trm_1 $.

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

$( -------- Substitution --------

  Here we define a notion of proper substitution.
  We say that a WFF phi replaces a variable x in another WFF psi with a term t
  when phi is obtained by substituting every free occurrence of x in psi with t.

  We will also require the substitution to be capture-avoiding. That is, x
  should not be within the scope of a quantifier that uses a variable y also in
  t, lest y becomes illegitimately bound to it ("captured") on substitution.
$)

$c REPLACES WITH IN $.

stmt.sub-wff $a stmt phi REPLACES x IN psi WITH trm_1 $.
stmt.sub-trm $a stmt ..t REPLACES x IN ..u WITH trm_1 $.

$( Base cases: $)

$( x is replaced if it is the term in question $)
sub.rep $a ; trm_1 REPLACES x IN x WITH trm_1 $.

${ $( Nothing is replaced when there are no occurrences $)
  $d x phi $.
  sub.none-wff $a ; phi REPLACES x IN phi WITH trm_1 $.
$} ${
  $d x ..t $.
  sub.none-trm $a ; ..t REPLACES x IN ..t WITH trm_1 $.
$}

$( Recursive cases: $)

${ $( Define for the logical connectives $)
  sub.con.1  $e ; phi_1 REPLACES x IN phi_2 WITH trm_1 $.
  sub.con.2  $e ; psi_1 REPLACES x IN psi_2 WITH trm_1 $.

  sub.and     $a ; ( and phi_1 psi_1 )     REPLACES x IN ( and phi_2 psi_2 )     WITH trm_1 $.
  sub.or      $a ; ( or phi_1 psi_1 )      REPLACES x IN ( or phi_2 psi_2 )      WITH trm_1 $.
  sub.implies $a ; ( implies phi_1 psi_1 ) REPLACES x IN ( implies phi_2 psi_2 ) WITH trm_1 $.
  sub.iff     $a ; ( iff phi_1 psi_1 )     REPLACES x IN ( iff phi_2 psi_2 )     WITH trm_1 $.
$} ${
  sub.not.1 $e ; phi_1 REPLACES x IN phi_2 WITH trm_1 $.
  sub.not   $a ; ( not phi_1 ) REPLACES x IN ( not phi_2 ) WITH trm_1 $.
$}

${ $( And for quantifiers $)
  $d y trm_1 $. $( Avoid variable capture $)
  $d x y $.     $( Avoid replacing bound occurrences $)
  sub.qnt.1 $e ; phi REPLACES x IN psi WITH trm_1 $.
  sub.qnt   $a ; ( qnt_1 y phi ) REPLACES x IN ( qnt_1 y psi ) WITH trm_1 $.
$}
$( When x is bound, no substitution occurs $)
sub.qnt-bound $a ; ( qnt_1 x phi ) REPLACES x IN ( qnt_1 x phi ) WITH trm_1 $.

${ $( A predicate or function replaces if all its arguments do $)
  sub.arg.1 $e ; ..t            REPLACES x IN ..u            WITH trm_1 $.
  sub.prd   $a ; ( prd_1 ..t )  REPLACES x IN ( prd_1 ..u )  WITH trm_1 $.
  sub.func  $a ; ( func_1 ..t ) REPLACES x IN ( func_1 ..u ) WITH trm_1 $.
$} ${
  sub.trm.1 $e ; trm_1     REPLACES x IN     trm_2 WITH trm_3 $.
  sub.trm.2 $e ; ..t       REPLACES x IN ..u       WITH trm_3 $.
  sub.trm   $a ; ..t trm_1 REPLACES x IN ..u trm_2 WITH trm_3 $.
$}

$( -------- Introduction Rules -------- $)

${ $( Universal Introduction $)
  $d a ... $. $( 'a' must not occur in an undischarged assumption $)
  axm.forall-intr.1 $e ; psi REPLACES a IN phi WITH x $.
  axm.forall-intr.2 $e ; ... |- phi $. 
  axm.forall-intr   $a ; ... |- ( forall x psi ) $. 
$}

${ $( Existential Introduction $)
  axm.exists-intr.1 $e ; phi REPLACES x IN psi WITH trm_1 $.
  axm.exists-intr.2 $e ; ... |- phi $. 
  axm.exists-intr   $a ; ... |- ( exists x psi ) $. 
$}

$( Equality Introduction $)
axm.eq-intr $a ; ... |- ( eq trm_1 trm_1 ) $.

$( -------- Elimination Rules -------- $)

${ $( Universal Elimination $)
  axm.forall-elim.1 $e ; psi REPLACES x IN phi WITH trm_1 $.
  axm.forall-elim.2 $e ; ... |- ( forall x phi ) $. 
  axm.forall-elim   $a ; ... |- psi $. 
$}

${ $( Existential Elimination $)
  $d a ... $. $( 'a' must not occur in an undischarged assumption $)
  $d a phi $. $( 'a' must not occur in phi $)
  $d a chi $. $( 'a' must not occur in chi (the conclusion) $)
  axm.exists-elim.1 $e ; psi REPLACES x IN phi WITH a $.
  axm.exists-elim.2 $e ; ... |- ( exists x phi ) $. 
  axm.exists-elim.3 $e ; ... psi |- chi $. 
  axm.exists-elim   $a ; ... |- chi $. 
$}

${ $( Equality Elimination $)
  $d x trm_1 $. $d x trm_2 $.
  axm.eq-elim-1.1 $e ; phi REPLACES x IN chi WITH trm_1 $.
  axm.eq-elim-1.2 $e ; psi REPLACES x IN chi WITH trm_2 $.
  axm.eq-elim-1.3 $e ; ... |- ( eq trm_1 trm_2 ) $.
  axm.eq-elim-1.4 $e ; ... |- phi $.
  axm.eq-elim-1   $a ; ... |- psi $.
$}

$( The reverse direction of equality elimination is in fact derivable as a
   theorem in our system, but in Fitch-style proofs we will permit using
   "axm.eq-elim" to refer to either one. $)
${ 
  $d x trm_1 $. $d x trm_2 $.
  thm.eq-elim-2.1 $e ; phi REPLACES x IN chi WITH trm_1 $.
  thm.eq-elim-2.2 $e ; psi REPLACES x IN chi WITH trm_2 $.
  thm.eq-elim-2.3 $e ; ... |- ( eq trm_1 trm_2 ) $.
  thm.eq-elim-2.4 $e ; ... |- psi $.
  thm.eq-elim-2   $p ; ... |- phi $=
    ( lst.single wff.atm sub.none-trm sub.rep sub.trm axm.eq-elim-1 prd.eq
    lst.append sub.prd trm.var axm.eq-intr ) ACBDEGFIHARFFLZSZMRFGLZSZMRFEUALZSZ
    MEFGERFUDUHEFFFUCUGEFUCNEFOPTERGUFUHEFFGUEUGEGUCNEGOPTJAFUBQKQ $.
$}

$(
--------------------------------------------------------------------------------
First Order Logic - Conservative Extensions
--------------------------------------------------------------------------------
$)

$( -------- Definitions -------- $)

stmt.def $a stmt phi := psi $.

${ $( Definiendum Introduction $)
  axm.def-intr.1 $e ; phi := psi $.
  axm.def-intr.2 $e ; ... |- psi $.
  axm.def-intr   $a ; ... |- phi $.
$}

${ $( Definiendum Elimination $)
  axm.def-elim.1 $e ; phi := psi $.
  axm.def-elim.2 $e ; ... |- phi $.
  axm.def-elim   $a ; ... |- psi $.
$}

$( -------- Logical Equivalence & Rules of Replacement --------

  If two WFFs are logically equivalent, they can generally be swapped for one
  another in any arbitrary formula without affecting its truth-value. This
  allows us to express "rules of replacement" that allow us to infer a new
  statement by replacing some segments of it with logically equivalent ones.

  Compared to the other rules of inference, these have the advantage of being
  able to operate on not just on the whole formula but also on subformulae.
  This is considered a "conservative extension" because it does not enable
  proving any new statements that we could not already prove; it is
  demonstrable as a metatheorem that if we have a proof using rules of
  replacement, there also exists a (potentially longer) proof of the same fact
  without them. However, it can nevertheless be useful, because it can shorten
  proofs by sparing us from having to dis- and reassemble an entire formula to
  change only part of it.

  Rules of replacement will be subject to the same capture-avoidance condition
  as proper substitution, so we will first define a new metalogical predicate
  similar to our previous "replaces" predicate. To distinguish them (and to
  emphasize the bidirectionality of the rules involving it), we will use the
  term "swaps".
$)

$c SWAPS === $.
stmt.swp $a stmt phi_1 SWAPS psi_1 IN phi_2 WITH psi_2 $.
stmt.eqv $a stmt phi === psi $.

$( Our formalization of substitution reprised: $)

$( psi is swapped if it is the WFF in question $)
swp.rep $a ; phi SWAPS psi IN psi WITH phi $.

$( Rules of replacement permit swapping only some occurrences, so leaving phi
   unchanged is always allowed. $)
swp.none $a ; phi SWAPS psi IN phi WITH chi $.

${ $( Define for the logical connectives $)
  swp.con.1  $e ; phi_1 SWAPS chi_1 IN phi_2 WITH chi_2 $.
  swp.con.2  $e ; psi_1 SWAPS chi_1 IN psi_2 WITH chi_2 $.

  swp.and     $a ; ( and phi_1 psi_1 )     SWAPS chi_1 IN ( and phi_2 psi_2 )     WITH chi_2 $.
  swp.or      $a ; ( or phi_1 psi_1 )      SWAPS chi_1 IN ( or phi_2 psi_2 )      WITH chi_2 $.
  swp.implies $a ; ( implies phi_1 psi_1 ) SWAPS chi_1 IN ( implies phi_2 psi_2 ) WITH chi_2 $.
  swp.iff     $a ; ( iff phi_1 psi_1 )     SWAPS chi_1 IN ( iff phi_2 psi_2 )     WITH chi_2 $.
$} ${
  swp.not.1 $e ; phi_1 SWAPS psi_1 IN phi_2 WITH psi_2 $.
  swp.not   $a ; ( not phi_1 ) SWAPS psi_1 IN ( not phi_2 ) WITH psi_2 $.
$}

${ $( And for quantifiers $)
  $d x psi_2 $. $( Avoid variable capture $)
  $d x psi_1 $. $( Avoid replacing bound occurrences $)
  swp.qnt.1 $e ; phi_1 SWAPS psi_1 IN phi_2 WITH psi_2 $.
  swp.qnt   $a ; ( qnt_1 x phi_1 ) SWAPS psi_1 IN ( qnt_1 x phi_2 ) WITH psi_2 $.
  $( Note: the $d conditions here are a bit overly restrictive in that it also
     rejects bound occurrences of x in psi_2, but this is only a problem if x
     would end up shadowed, which we will avoid as a matter of style anyway. $)
$}

$( Equivalence Introduction
   Two WFFs are logically equivalent if their material biconditional is a
   tautology (i.e., provable in the empty context ). $)
${
  axm.eqv-intr.1 $e ; |- ( iff phi psi ) $.
  axm.eqv-intr   $a ; phi === psi $.
$}

${ $( Equivalence Elimination $)
  axm.eqv-elim-1.1 $e ; phi_1 SWAPS psi_1 IN phi_2 WITH psi_2  $.
  axm.eqv-elim-1.2 $e ; psi_1 === psi_2 $.
  axm.eqv-elim-1.3 $e ; ... |- phi_1 $.
  axm.eqv-elim-1   $a ; ... |- phi_2 $.
$} ${ 
  axm.eqv-elim-2.1 $e ; phi_1 SWAPS psi_1 IN phi_2 WITH psi_2  $.
  axm.eqv-elim-2.2 $e ; psi_1 === psi_2 $.
  axm.eqv-elim-2.3 $e ; ... |- phi_2 $.
  axm.eqv-elim-2   $a ; ... |- phi_1 $.
$}

$( We can now prove that if two WFFs are equivalent by definition, they can be
   eliminated in the same way $)
${
  thm.def-eqv-1.1 $e ; phi_1 SWAPS psi_1 IN phi_2 WITH psi_2  $.
  thm.def-eqv-1.2 $e ; psi_1 := psi_2 $.
  thm.def-eqv-1.3 $e ; ... |- phi_1 $.
  thm.def-eqv-1   $p ; ... |- phi_2 $=
    ( ctx.empty axm.def-elim axm.def-intr axm.iff-intr axm.eqv-elim-1 ctx.append
    axm.assume axm.eqv-intr ) ABCDEFCEICEICNCEGICOJIENCEGIEOKLPHM $.
$} ${ 
  thm.def-eqv-2.1 $e ; phi_1 SWAPS psi_1 IN phi_2 WITH psi_2  $.
  thm.def-eqv-2.2 $e ; psi_1 := psi_2 $.
  thm.def-eqv-2.3 $e ; ... |- phi_2 $.
  thm.def-eqv-2   $p ; ... |- phi_1 $=
    ( ctx.empty axm.def-elim axm.def-intr axm.iff-intr axm.eqv-elim-2 ctx.append
    axm.assume axm.eqv-intr ) ABCDEFCEICEICNCEGICOJIENCEGIEOKLPHM $.
$}