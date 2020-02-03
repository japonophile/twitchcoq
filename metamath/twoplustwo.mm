$[ lib/peano.mm $]

wff_pa_ax1 $p wff not = 0 S x $=
  tzero varx tvar tsucc binpred_equals wff_atom wff_not
$.

int1 $p |- implies chi not = 0 S x $=
  varx wff_pa_ax1 logbinopimplies varx wff_pa_ax1 wff-chi wff_logbinop varx pa_ax1 varx wff_pa_ax1 wff-chi ax-1 ax-mp
$.

${
  $d psi x $.
  $d x y $.

  int2 $p |- implies psi forall x not = 0 S x $=
    varx wff_psi varx wff_pa_ax1 varx wff_psi int1 alpha_2
  $.

  $(
    phi: vary wff_pa_ax1
       = wff not = 0 S y
    psi: varx quant_all varx wff_pa_ax1 wff_quant
       = wff forall x not = 0 S x
    min: vary pa_ax1
       = |- not = 0 S y
    maj: vary wff_pa_ax1 varx int2
       = 
  $)

  nocheat $p |- forall x not = 0 S x $=
    vary wff_pa_ax1
    varx quant_all varx wff_pa_ax1 wff_quant
    vary pa_ax1
    varx vary wff_pa_ax1 int2
    ax-mp
  $.
$}

cheat2 $p |- forall x implies = x 0 not = 0 S x $=
  varx quant_all varx wff_pa_ax1 wff_quant
  varx quant_all logbinopimplies varx wff_pa_ax1 varx tvar tzero binpred_equals wff_atom wff_logbinop wff_quant
  varx nocheat
  tzero varx varx wff_pa_ax1 all_elim
  ax-mp
$.


$(
onenotzero $p |- not = 0 S x $=
?
$.
$)

$(


chi:
   = not = 0 S x
phi:
   = implies chi not = 0 S x
min: varx pa_ax1
   = |- not = 0 S x
maj: varx wff_pa_ax1 wff-chi ax-1
   = |- implies not = 0 S x implies chi not = 0 S x

logbinopimplies wff_psi varx wff_pa_ax1 wff_logbinop
wff implies not = 0 S x psi

logbinopimplies varx wff_pa_ax1 wff-chi wff_logbinop
wff implies chi not = 0 S x

varx wff_pa_ax1 wff-chi ax-1
|- implies not = 0 S x implies chi not = 0 S x


varx wff-chi varx wff_pa_ax1 varx wff-chi int1 alpha_2



varx wff_pa_ax1
logbinopimplies varx wff_pa_ax1 wff-chi wff_logbinop
varx pa_ax1
varx wff_pa_ax1 wff-chi ax-1
ax-mp

varx wff_pa_ax1 logbinopimplies varx wff_pa_ax1 wff-chi wff_logbinop varx pa_ax1 varx wff_pa_ax1 wff-chi ax-1 ax-mp



tzero varx varx wff_pa_ax1 all_elim
|- implies forall x not = 0 S x forall x implies = x 0 not = 0 S x



varx wff_pa_ax1 wff_psi varx pa_ax1 varx wff_pa_ax1 wff_psi ax-1 ax-mp

pa_ax1
varx wff_pa_ax1 wff_psi ax-1



Prove cheat2

phi: varx quant_all varx wff_pa_ax1 wff_quant
   = wff forall x not = 0 S x
psi: varx quant_all logbinopimplies varx wff_pa_ax1 varx tvar tzero binpred_equals wff_atom wff_logbinop wff_quant
   = wff forall x implies = x 0 not = 0 S x
min: varx nocheat
   = |- forall x not = 0 S x
maj: tzero varx varx wff_pa_ax1 all_elim
   = |- implies forall x not = 0 S x forall x implies = x 0 not = 0 S x





tzero varx tzero varx tvar tsucc binpred_equals wff_atom wff_not all_elim
|- implies forall x not = 0 S x forall x implies = x 0 not = 0 S x

|- forall x not = 0 S x
   ->
   forall x
     = x 0
     ->
     not = 0 S x


tzero varx tvar tsucc binpred_equals wff_atom wff_not
tzero tzero tsucc binpred_equals wff_atom wff_not


varx pa_ax1



x    = varx
phi  = |- not = 0 S x
chi  = true?

${ $d phi x $.

   alpha_hyp2 $e |- implies phi chi $.
   alpha_2    $a |- implies phi forall x chi $.
$}


${ $d phi x $.

   alpha_hyp2 $e |- implies phi chi $.
   alpha_2    $a |- implies phi forall x chi $.
$}


${ $d x t $.
   all_elim $a |- implies
                   forall x phi
                   forall x implies
                              = x t
                              phi $.
$}




twoplustwo $p |- = + S S 0 S S 0 S S S S 0 $=
tzero tsucc tsucc tzero tsucc tsucc binop_plus tbinop
tzero tsucc tsucc tsucc tsucc
binpred_equals wff_atom
$.
$)

