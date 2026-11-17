#!/bin/bash
# Gate for the Paper K Lean formalisation (Lie form, cofactor point, degenerate planar cases, three dimensions). Passes only if all of these hold:
#  * the sources contain no `sorry`, `admit`, `native_decide`, `axiom`, `#eval`, `run_cmd`,
#    `initialize`, `IO`, `set_option`, or syntax-extension commands (which could redefine
#    `#print axioms`);
#  * the library builds without errors;
#  * the gate itself generates the `#print axioms` report for each REQUIRED theorem;
#  * each REQUIRED theorem uses only Lean's standard axioms (propext, Classical.choice, Quot.sound).
# SCAFFOLD=1 skips the forbidden-token check and also tolerates `sorryAx`, so a partially
# finished development can be checked while it still contains `sorry`.
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")" || exit 1
NS="PaperK"
LIB="PaperK"
REQUIRED="PaperK.B_self_eq_zero_iff PaperK.tangency_identity PaperK.B_eq_zero_iff_tangent PaperK.mulVec_cofactor PaperK.B_G_cofactor_row PaperK.prop31 PaperK.prop31_cofactor PaperK.explicit_power PaperK.explicit_power_indep PaperK.equal_power PaperK2.equal_power PaperK2.equilateral_PX PaperK2.square_apollonius PaperK2.square_null_space PaperK2.square_PX PaperK2.equal_power_point_unique PaperK2.PX_circumcentre PaperK3.B_self_zero_iff PaperK3.tangency_identity PaperK3.equal_power PaperK3.tetra_PX_origin PaperK3.tetra_tangent_B PaperK3.tetra_E1_apollonius PaperK3.tetra_affineIndependent"
REQUIRED="$REQUIRED PaperK.bridge_dist_sq PaperK.bridge_B_toLinearMap₂ PaperK.bridge_cofactor_det PaperK.bridge_pt PaperK.bridge_pt_normalised PaperK.bridge_B_dist PaperK.bridge_B_eq_zero_iff_dist PaperK.bridge_B_isExtTangent PaperK.bridge_B_isIntTangent PaperK.bridge_B_power PaperK.bridge_power_sphere PaperK.bridge_power_eq_const_sphere PaperK.bridge_power_eq_const_sphere_rho0 PaperK.bridge_collinear_iff_det PaperK2.bridge_B_eq PaperK2.bridge_circ_null PaperK2.bridge_circ_centre_radius PaperK2.bridge_B_circ_dist PaperK2.bridge_circ_mem_sphere PaperK2.bridge_circ_power PaperK2.bridge_circ_isExtTangent PaperK2.bridge_circ_isIntTangent PaperK2.bridge_pw_sphere PaperK2.bridge_pconst_neg_B PaperK2.bridge_power_eq_const_sphere PaperK2.bridge_power_eq_const_sphere_rho0 PaperK2.bridge_Equi_dist PaperK2.bridge_D3_collinear PaperK2.bridge_Tangent PaperK3.bridge_dist_sq3 PaperK3.bridge_B_sph_dist PaperK3.bridge_sph_mem_sphere PaperK3.bridge_sph_power PaperK3.bridge_sph_isExtTangent PaperK3.bridge_sph_isIntTangent PaperK3.bridge_equal_power_sphere"
REQUIRED="$REQUIRED PaperKn.B_self_eq_zero_iff PaperKn.B_add_right PaperKn.B_smul_right PaperKn.tangency_identity PaperKn.B_eq_zero_iff_tangent PaperKn.power_eq_const PaperKn.equal_power PaperKn.prop31 PaperKn.dist_sq_const PaperKn.eq_zero_of_orth_affineIndependent PaperKn.simplex_E1 PaperKn.simplex_circumradius PaperKn.brief_E_false"
SOURCES="$(ls PaperK/*.lean) PaperK.lean"
[ -e .lake/packages/mathlib ] || { echo "FAIL: Mathlib packages missing (run setup by hand)"; exit 1; }
if [ "${SCAFFOLD:-0}" != "1" ]; then
  if grep -nE "\bsorry\b|\badmit\b|native_decide|\baxiom\b|#eval|\brun_cmd\b|\binitialize\b|\bIO\b|\bdebug\.|\bmacro|\belab|\bsyntax\b|\bnotation\b|\binfix|\bprefix\b|\bpostfix\b|import Lean|open Lean|\bset_option\b" $SOURCES; then
    echo "FAIL: forbidden token"; exit 1; fi
fi
build=$(lake build $LIB 2>&1); bstatus=$?
printf '%s\n' "$build" | tail -3
[ "$bstatus" -eq 0 ] || { printf '%s\n' "$build"; echo "FAIL: build"; exit 1; }
root=$(lake env lean "$LIB.lean" 2>&1) || { printf '%s\n' "$root"; echo "FAIL: build (root file)"; exit 1; }
chk=".gatecheck_$$.lean"
trap 'rm -f "$chk"' EXIT
{ echo "import $LIB"; for t in $REQUIRED; do echo "#print axioms $t"; done; } > "$chk"
out=$(lake env lean "$chk" 2>&1); status=$?
printf '%s\n' "$out"
[ "$status" -eq 0 ] || { echo "FAIL: axiom report"; exit 1; }
echo "$out" | grep -qE "(^|:)[[:space:]]*error" && { echo "FAIL: Lean reported an error"; exit 1; }
flat=$(printf '%s\n' "$out" | awk '/^'"'"'/{if(buf!="")print buf; buf=$0; next} {buf=buf" "$0} END{if(buf!="")print buf}')
reports=$(printf '%s\n' "$flat" | grep -E "depends on axioms|does not depend on any axioms")
n=0
for t in $REQUIRED; do
  te=$(printf '%s' "$t" | sed 's/[.]/\\./g')
  c=$(printf '%s\n' "$reports" | grep -cE "^'$te' (depends on axioms|does not depend)")
  [ "$c" -eq 1 ] || { echo "FAIL: expected one axiom report for $t, found $c"; exit 1; }
  n=$((n+1))
done
[ "$(printf '%s\n' "$reports" | grep -c .)" -eq "$n" ] || { echo "FAIL: unexpected extra reports"; exit 1; }
printf '%s\n' "$reports" | grep "depends on axioms" | grep -qv '\]' && { echo "FAIL: unterminated axiom list"; exit 1; }
if [ "${SCAFFOLD:-0}" = "1" ]; then ALLOW='^(propext|Classical\.choice|Quot\.sound|sorryAx)$'; else ALLOW='^(propext|Classical\.choice|Quot\.sound)$'; fi
bad=$(printf '%s\n' "$reports" | grep "depends on axioms" | sed 's/.*depends on axioms: *\[//; s/\].*//' \
      | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u | grep -vE "$ALLOW")
[ -n "$bad" ] && { echo "FAIL: nonstandard axioms: $bad"; exit 1; }
echo "PASS ($n declarations, standard axioms only)"
