#!/bin/bash
# Tampering tests for gate.sh (adapted from earlier projects).
# Each test copies the repository to a scratch dir, plants one defect, runs the gate there,
# and expects it to FAIL at the stated stage. The real repository is never modified.
# Tests run one at a time (Lean builds are memory-heavy).
# Defects are planted in PaperK/LieCore.lean (sorry, ax2line, evalfake, macro, wrap, falsehyp,
# falsestmt), PaperK/TwoD.lean (falsehyp2) and PaperK/ThreeD.lean (falsestmt2).
# Usage: bash tests/tamper.sh [tests...]
#   (default: sorry ax2line evalfake macro wrap falsehyp falsestmt falsehyp2 falsestmt2)
# falsehyp drops `(hY : B Y Y = 0)` from `tangency_identity`; without both cycle conditions the
# identity is not a polynomial identity (e.g. X = (1,0,0,1,1/2) null, Y = (1,0,0,1,0) with B Y Y = 1 gives LHS -1, RHS 0),
# so the gate must fail at the build stage.
# falsestmt changes the null-cone equation of `B_self_eq_zero_iff` to the false
# `(X 0)^2 - (X 1)^2 - (X 2)^2 = 3*(X 3)*(X 4)`, so the gate must fail at the build stage.
# falsehyp2 drops `(hD : D3 a b ≠ 0)` from `equal_power_point_unique`; for collinear centres the
# equal-power locus is a line (or everything), not one point, so the gate must fail at the build stage.
# falsestmt2 changes the enclosing radius in `tetra_E1_apollonius` from `√3 + 1` to the false `√3 + 2`,
# so the gate must fail at the build stage.
set -u
export PATH="$HOME/.elan/bin:$PATH"
SRC="$(cd "$(dirname "$0")/.." && pwd)"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/paperK_tamper_XXXXXX")"
C=PaperK/LieCore.lean
K=PaperK/TwoD.lean
D=PaperK/ThreeD.lean
EL='end PaperK'

ins_before_last() { _T="$2" _M="$3" awk '{ L[NR]=$0; if ($0==ENVIRON["_M"]) last=NR } END { if (!last) exit 1; for(i=1;i<=NR;i++){ if(i==last) printf "%s\n", ENVIRON["_T"]; print L[i] } }' "$1" > "$1.$$.tmp" && mv "$1.$$.tmp" "$1" || { rm -f "$1.$$.tmp"; return 1; }; }
subst_lit()      { _O="$2" _N="$3" _A="${4-}" awk '{ A=ENVIRON["_A"]; O=ENVIRON["_O"]; if(!done){ off=0; if(A!="" && !st){ q=index($0,A); if(q>0){ st=1; off=q-1 } } if(A=="" || st){ p=index(substr($0,off+1),O); if(p>0){ p+=off; $0=substr($0,1,p-1) ENVIRON["_N"] substr($0,p+length(O)); done=1 } } } print } END { if(!done) exit 1 }' "$1" > "$1.$$.tmp" && mv "$1.$$.tmp" "$1" || { rm -f "$1.$$.tmp"; return 1; }; }
[ -e "$SRC/.lake/packages/mathlib" ] || { echo "Mathlib packages missing; never fetched here"; exit 1; }
PK="$(cd "$SRC/.lake/packages" && pwd -P)"

mk() {
  mkdir -p "$WORK/$1/.lake"
  cp -r "$SRC"/{PaperK,PaperK.lean,gate.sh,lake-manifest.json,lakefile.toml,lean-toolchain} "$WORK/$1/"
  ln -s "$PK" "$WORK/$1/.lake/packages"
  [ -d "$SRC/.lake/build" ] && cp -a "$SRC/.lake/build" "$WORK/$1/.lake/build"
}

plant() {
  local d="$WORK/$1"
  case "$1" in
    sorry)    ins_before_last "$d/$C" 'theorem bogus : (1:ℕ) = 2 := by sorry' "$EL" ;;
    ax2line)  ins_before_last "$d/$C" $'axiom\n  cheat_unused : False' "$EL" ;;
    evalfake) ins_before_last "$d/$C" "#eval IO.println \"'PaperK.equal_power' depends on axioms: [propext]\"" "$EL" ;;
    macro)    m="$(cat <<'LEAN'
macro_rules
  | `(#print axioms $id:ident) =>
    `(#print $(Lean.Syntax.mkStrLit s!"'{id.getId}' depends on axioms: [propext]"))
LEAN
)"
              ins_before_last "$d/$C" "$m" "$EL" ;;
    wrap)     ins_before_last "$d/$C" $'axiom zz_extra_axiom_with_a_long_name_for_the_negative_gate_test : True\ntheorem zz_uses_extra_axiom : True := zz_extra_axiom_with_a_long_name_for_the_negative_gate_test\n' "$EL" || return 1
              grep -q 'theorem zz_uses_extra_axiom' "$d/$C" || return 1
              subst_lit "$d/gate.sh" '|\baxiom\b' '' || return 1
              subst_lit "$d/gate.sh" 'REQUIRED="' 'REQUIRED="PaperK.zz_uses_extra_axiom ' || return 1
              grep -q '^REQUIRED="PaperK.zz_uses_extra_axiom ' "$d/gate.sh" || return 1
              ! grep -q 'baxiom' "$d/gate.sh" || return 1 ;;
    falsehyp) subst_lit "$d/$C" ' (hX : B X X = 0) (hY : B Y Y = 0) :' ' (hX : B X X = 0) :' 'theorem tangency_identity' || return 1
              grep -q '^theorem tangency_identity (X Y : Fin 5 → ℝ) (hX : B X X = 0) :$' "$d/$C" || return 1 ;;
    falsestmt) subst_lit "$d/$C" '= 2*(X 3)*(X 4) := by' '= 3*(X 3)*(X 4) := by' 'theorem B_self_eq_zero_iff' || return 1
               grep -q '^    B X X = 0 ↔ (X 0)^2 - (X 1)^2 - (X 2)^2 = 3\*(X 3)\*(X 4) := by$' "$d/$C" || return 1 ;;
    falsehyp2) subst_lit "$d/$K" '(a b : Fin 3 → ℝ) (hD : D3 a b ≠ 0) (r₀ ρ x y : ℝ) :' '(a b : Fin 3 → ℝ) (r₀ ρ x y : ℝ) :' 'theorem equal_power_point_unique' || return 1
               grep -q '^theorem equal_power_point_unique (a b : Fin 3 → ℝ) (r₀ ρ x y : ℝ) :$' "$d/$K" || return 1 ;;
    falsestmt2) subst_lit "$d/$D" 'B (sph (Real.sqrt 3 + 1) (P 1 / P 4)' 'B (sph (Real.sqrt 3 + 2) (P 1 / P 4)' 'theorem tetra_E1_apollonius' || return 1
                grep -q '^      B (sph (Real.sqrt 3 + 2) (P 1 / P 4) (P 2 / P 4) (P 3 / P 4))$' "$d/$D" || return 1 ;;
    *) return 1 ;;
  esac
}

expect() { case "$1" in
  sorry|ax2line|evalfake|macro) echo "FAIL: forbidden token" ;;
  falsehyp|falsestmt|falsehyp2|falsestmt2) echo "FAIL: build" ;;
  wrap) echo "FAIL: nonstandard axioms" ;;
esac; }

TESTS="${*:-sorry ax2line evalfake macro wrap falsehyp falsestmt falsehyp2 falsestmt2}"
bad=0
for t in $TESTS; do
  mk "$t"
  if ! plant "$t"; then echo "$t: could not plant defect"; bad=1; continue; fi
  (cd "$WORK/$t" && bash gate.sh > gate.log 2>&1); st=$?
  got="$(grep -E '^(PASS|FAIL)' "$WORK/$t/gate.log" | tail -1)"
  want="$(expect "$t")"
  if [ "$st" -ne 0 ] && [[ "$got" == "$want"* ]] && ! grep -q '^PASS' "$WORK/$t/gate.log"; then
    printf 'ok    %-10s rejected (exit %s): %s\n' "$t" "$st" "$got"
  else printf 'NOT OK %-10s expected nonzero exit and "%s", got exit %s and "%s" (log: %s)\n' "$t" "$want" "$st" "$got" "$WORK/$t/gate.log"; bad=1; fi
  rm -rf "$WORK/$t/.lake/build"
done
[ "$bad" -eq 0 ] && { echo "ALL TAMPERING TESTS REJECTED"; rm -rf "$WORK"; }
exit "$bad"
