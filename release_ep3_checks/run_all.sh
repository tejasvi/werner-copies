#!/bin/bash
# Reruns the additional checks of this package.
#   ./run_all.sh               the rows that take minutes on one core: R3, R6, R7, R9, R10, R13, R13b (about 16 min)
#   ./run_all.sh R7 R13        only the rows named; the heavy rows R1, R2, R4 (= R4, R5), R8, R10b, R11, R12 (15 min to
#                              hours each) run only when named
#   ./run_all.sh list          print the commands of the heavy rows without running them
#   DRY=1 ./run_all.sh [ROW]   print the commands of the selected rows without running them
# Environment: PYTHON (default python3), OUT (output directory, default <package>_out next to the package directory;
# it must lie outside the package).  Logs go to $OUT/logs; README.md names the reference log in expected/ for every row.
set -u -o pipefail
PKG=$(cd "$(dirname "$0")" && pwd)
OUT=${OUT:-${PKG}_out}
mkdir -p "$OUT/logs" && OUT=$(cd "$OUT" && pwd) || exit 2
case "$OUT/" in "$PKG"/*) echo "OUT=$OUT lies inside the package; choose another directory" >&2; exit 2 ;; esac
read -r -a PY <<< "${PYTHON:-python3}"
PY+=(-I -B)
W=("${PY[@]}" "$PKG/code/pkgrun.py")
export PKG_OUT=$OUT OMP_NUM_THREADS=${OMP_NUM_THREADS:-1} OPENBLAS_NUM_THREADS=${OPENBLAS_NUM_THREADS:-1} MKL_NUM_THREADS=${MKL_NUM_THREADS:-1}
D=$PKG/data
fails=0

run() {  # run LOG DIR CMD ...: run CMD in DIR with its output in $OUT/logs/LOG
    local name=$1 log=$OUT/logs/$1 dir=$2 t0=$SECONDS rc
    shift 2
    if [ -n "${DRY:-}" ]; then
        printf '(cd %q && %s) > %q 2>&1\n' "$dir" "$(printf '%q ' "$@")" "$log"
        return 0
    fi
    (cd "$dir" && "$@") > "$log" 2>&1
    rc=$?
    echo "      $(( SECONDS - t0 )) s, exit $rc: logs/$name"
    return $rc
}

check() {  # check LABEL LOG REGEX [COUNT]: at least COUNT (default 1) lines of the log match REGEX
    [ -n "${DRY:-}" ] && return 0
    local n
    n=$(awk -v re="$3" '$0 ~ re { n++ } END { print n + 0 }' "$OUT/logs/$2")
    if [ "$n" -ge "${4:-1}" ]; then
        echo "PASS  $1"
    else
        echo "FAIL  $1: $n of ${4:-1} lines matching /$3/ in logs/$2"
        fails=$((fails + 1))
    fi
}

absent() {  # absent LABEL LOG REGEX: no line of the log matches REGEX
    [ -n "${DRY:-}" ] && return 0
    if awk -v re="$3" '$0 ~ re { f = 1 } END { exit !f }' "$OUT/logs/$2"; then
        echo "FAIL  $1: logs/$2 has lines matching /$3/"
        fails=$((fails + 1))
    fi
}

same() {  # same LABEL FILE1 FILE2: the two files are byte-identical
    [ -n "${DRY:-}" ] && { printf 'cmp %q %q\n' "$2" "$3"; return 0; }
    if cmp -s "$2" "$3"; then echo "PASS  $1"; else echo "FAIL  $1: $2 differs from $3"; fails=$((fails + 1)); fi
}

CERT2=(runs/cert2_k3_d6.pkl runs/cert2_k3_d9.pkl runs/cert2_k3_d10.pkl runs/cert2_k3_d11.pkl runs/cert2_k3_d12.pkl
       runs/cert2_k3_d13.pkl runs/cert2_k3_d14.pkl runs/cert2_k3_d15.pkl runs/cert2_k3_d16.pkl)
NODES=(); for n in 17 18 19 20 21 22 23 24 25 26 27 28; do NODES+=("runs/certnode_n$n.pkl"); done
REL=(); for n in 31 38 48 64 93 150 288 790 7061; do REL+=("runs/relcert2_n$n.pkl"); done
UNODES=7061,790,288,150,93,64,48,38,31,26,23,21,20,19,18,17

row_R3() {  # R3 and R6 parts A-D: verifier semantics against dense implementations; R3: audit of the 22 certificate files
    run R3_R6_check_validity.log "$PKG" "${W[@]}" validity/check_validity.py
    check 'R3/R6 validity checks, parts A-E' R3_R6_check_validity.log '^ALL CHECKS PASS$'
    check 'R3 audit of the 22 certificate files' R3_R6_check_validity.log 'eq groups .* : ok$' 22
}

row_R6() {  # R6 negative test: Verifier II accepts the converted d = 3 certificate and rejects a perturbed copy
    run R6_convert.log "$OUT" "${PY[@]}" "$PKG/code/cert/convert_cert_v4.py" "$D/cert/runs/certfile_k3_d3.pkl" R6_certfile4_k3_d3.pkl
    run R6_convert_perturbed.log "$OUT" "${PY[@]}" "$PKG/code/cert/convert_cert_v4.py" "$D/cert/runs/certfile_k3_d3.pkl" \
        R6_certfile4_k3_d3_perturbed.pkl perturb
    run R6_verify4_d3.log "$OUT" "${PY[@]}" "$PKG/code/cert/verify_cert4.py" R6_certfile4_k3_d3.pkl
    run R6_verify4_d3_perturbed.log "$OUT" "${PY[@]}" "$PKG/code/cert/verify_cert4.py" R6_certfile4_k3_d3_perturbed.pkl
    check 'R6 control: the converted d = 3 certificate passes Verifier II' R6_verify4_d3.log 'EXACT_CERTIFICATE_PASS$'
    check 'R6 the perturbed d = 3 certificate fails Verifier II' R6_verify4_d3_perturbed.log '] FAIL$'
}

row_R7() {  # FT_poly(d) equals the verifier's literal local data
    run R7_ft_check_d.log "$PKG" "${W[@]}" dim/uni/ft_check_d.py 6 9 10 11 12 13 14 15 16
    run R7_ft_newn.log "$PKG" "${W[@]}" dimaudit/ft_newn.py 17 18 19 20 21 22 23 24 25 26 30 31 50
    check 'R7 d = 6, 9..16' R7_ft_check_d.log 'for all cuts: True$' 9
    check 'R7 d = 17..26, 30, 31, 50' R7_ft_newn.log 'all cuts: True; .*: True [(]' 13
    absent 'R7 no mismatch' R7_ft_check_d.log 'MISMATCH|False'
    absent 'R7 no mismatch' R7_ft_newn.log 'MISMATCH|False'
}

row_R9() {  # degrees of the columns and of the objective
    run R9_degree_checks.log "$PKG" "${W[@]}" dim/lk/degree_checks.py
    run R9_eqdeg.log "$PKG" "${W[@]}" dim/lk/eqdeg_check.py
    check 'R9 D(n) Wg(n) has degree 4' R9_degree_checks.log 'max degree 4, consistent at n=13,14: True$'
    check 'R9 no label block of degree > 2f' R9_degree_checks.log 'label blocks with degree > 2f: 0$'
    check 'R9 max F_t = 6, numerator degree bound 24' R9_degree_checks.log 'max F_t over kept types = 6 -> numerator degree bound 12 [+] 2F = 24$'
    check 'R9 equality columns and objective: higher differences vanish' R9_eqdeg.log 'differences vanish: True True$' 2
}

row_R10() {  # the 1934 vanishing combinations, the rank of the 107 trace vectors, the zero modes
    run R10_fconst.log "$PKG" "${W[@]}" dim/lk/fconst_check.py
    run R10_fconst_colmap.log "$PKG" "${W[@]}" dimaudit/fconst_colmap.py
    run R10_tau_rank.log "$PKG" "${W[@]}" dimaudit/tau_rank.py
    run R10_zm_exact_q.log "$PKG" "${W[@]}" dimaudit/zm_exact_q.py
    check 'R10 F_const has dimension 1934' R10_fconst.log '^F_const dimension = 1934$'
    check 'R10 F_const annihilates the columns, equalities and objective' R10_fconst.log 'annihilates? ker[(]Ga[)].*: True$' 3
    check 'R10 ... also after the gram/gram2 column maps' R10_fconst_colmap.log 'colmaps .*: True$'
    check 'R10 the 107 trace vectors have exact rank 107' R10_tau_rank.log 'exact rank over Q = 107 '
    check 'R10 q_3 = 0 at the 31 zero modes' R10_zm_exact_q.log '^distinct dense zero modes: 31, max .* = 0[.]000e[+]00 '
}

row_R13() {  # Lebesgue constants of the interpolation points used in R12
    run R13_lebesgue_check.log "$PKG" "${PY[@]}" code/dimaudit/lebesgue_check.py
    check 'R13 28 points: grid maximum 3.0839' R13_lebesgue_check.log '^28 eval points +grid max 3[.]08392'
    check 'R13 16 points: grid maximum 2.7278' R13_lebesgue_check.log '^16 M nodes +grid max 2[.]72777'
}

row_R13b() {  # certified bounds of the two Lebesgue constants used by R12 (interval arithmetic; new script)
    run R13b_lebesgue_rigorous.log "$PKG" "${PY[@]}" code/lebesgue_rigorous.py
    check 'R13b 28 points: certified bound below 3.4895' R13b_lebesgue_rigorous.log '^[[].*28 evaluation points .*: certified sup Lambda <= 3[.]08392.*; < 3[.]4895$'
    check 'R13b 16 points: certified bound below 3.0645' R13b_lebesgue_rigorous.log '^[[].*16 Chebyshev nodes .*: certified sup Lambda <= 2[.]72777.*; < 3[.]0645$'
    check 'R13b both constants certified' R13b_lebesgue_rigorous.log 'LEBESGUE BOUNDS CERTIFIED: both constants used by uniform_verify[.]py hold$'
}

row_R1() {  # Construction I, d = 5..16, Verifier I: 30-50 min per d
    local d
    for d in 5 6 7 8 9 10 11 12 13 14 15 16; do
        run R1_verify2_k3_d$d.log "$D/dim" "${PY[@]}" "$PKG/code/dim/verify_cert.py" runs/certfile2_k3_d$d.pkl
        check "R1 d = $d passes Verifier I" R1_verify2_k3_d$d.log 'EXACT_CERTIFICATE_PASS$'
    done
}

row_R2() {  # Construction II, Verifier II: 4-25 min per d
    local d
    for d in 5 6 7 8 9 10 12 16; do
        run R2_verify4_k3_d$d.log "$D/cert" "${PY[@]}" "$PKG/code/cert/verify_cert4.py" runs/vm_certs/certfile4_k3_d$d.pkl
        check "R2 d = $d passes Verifier II" R2_verify4_k3_d$d.log 'EXACT_CERTIFICATE_PASS$'
    done
}

row_R4() {  # R4 and R5: d = 3 and d = 4, Verifier I: 14 and 28 min
    local d
    for d in 3 4; do
        run R4_R5_verify_k3_d$d.log "$D/cert" "${PY[@]}" "$PKG/code/cert/verify_cert.py" runs/certfile_k3_d$d.pkl
        check "R4/R5 d = $d passes Verifier I" R4_R5_verify_k3_d$d.log 'EXACT_CERTIFICATE_PASS$'
    done
}

row_R8() {  # export of the node certificates n = 17, 23 from the polynomial data, then Verifier I: about 1 h and 2 h
    local n
    mkdir -p "$OUT/R8"
    for n in 17 23; do
        run R8_export_n$n.log "$OUT/R8" "${W[@]}" dim/export_cert.py "$D/dim/runs/certnode_n$n.pkl" certfile_node_n$n.pkl
        same "R8 n = $n export reproduces data/dimaudit/runs/certfile_node_n$n.pkl" "$OUT/R8/certfile_node_n$n.pkl" \
            "$D/dimaudit/runs/certfile_node_n$n.pkl"
        run R8_verify_node_n$n.log "$OUT/R8" "${PY[@]}" "$PKG/code/dim/verify_cert.py" certfile_node_n$n.pkl
        check "R8 n = $n passes Verifier I" R8_verify_node_n$n.log 'EXACT_CERTIFICATE_PASS$'
    done
}

row_R10b() {  # rebuild of the 107 trace vectors (more than 10 min), written to $OUT/tau_exact2.pkl
    run R10b_exact_tau2.log "$PKG" "${W[@]}" dim/lk/exact_tau2.py "$OUT/tau_exact2.pkl" 107
    check 'R10b rebuilt trace vectors have exact rank 107' R10b_exact_tau2.log 'exact rank over Q: 107$'
}

row_R11() {  # strict PD at 30 dimensions, face check, mod-p cross-check: about 70 min
    local n
    run R11_pd_check.log "$D/dim" "${PY[@]}" "$PKG/code/dim/uni/pd_check.py" "${CERT2[@]}" "${NODES[@]}"
    check 'R11 strict PD, d = 6, 9..28 (21 certificates)' R11_pd_check.log 'consistent=True, strictly PD failures: 0$' 21
    run R11_face_check.log "$D/dim" "${W[@]}" dimaudit/face_check.py "${CERT2[@]}" "${NODES[@]}"
    check 'R11 the 21 certificates use the face of d = 6' R11_face_check.log 'N==Nref: True ' 21
    run R11_pd_rel2.log "$D/dim" "${W[@]}" dimaudit/pd_rel2.py "${REL[@]}"
    check 'R11 rigorous strict PD, n = 31..7061 (9 certificates)' R11_pd_rel2.log 'rigorous strict PD failures 0 of 1342 ' 9
    for n in 26 31 38 48 64 93 150 288 790 7061; do
        run R11_check_relcert_modp_n$n.log "$D/dim" "${W[@]}" dim/ac/check_relcert_modp.py runs/relcert2_n$n.pkl
        check "R11 n = $n identity modulo two primes" R11_check_relcert_modp_n$n.log 'nonzero residual rows mod p: 0 -> OK$' 2
    done
}

row_R12() {  # regenerates the 16 column files (24 GB, $OUT/dim/ac), then the uniform verification and its audit re-run
    local n
    mkdir -p "$OUT/dim/ac"
    for n in ${UNODES//,/ }; do
        [ -s "$OUT/dim/ac/rcols_n$n.npz" ] && continue
        run R12_rcols_n$n.log "$PKG" "${W[@]}" dim/ac/dumpcols_rel.py "$n" "$D/dim/ac/rel2_31.pkl" "$D/dim/ac/rel31b.pkl" \
            "$OUT/dim/ac/rcols_n$n.part.npz" || continue
        if [ -n "${DRY:-}" ]; then
            printf 'mv %q %q\n' "$OUT/dim/ac/rcols_n$n.part.npz" "$OUT/dim/ac/rcols_n$n.npz"
        else
            mv "$OUT/dim/ac/rcols_n$n.part.npz" "$OUT/dim/ac/rcols_n$n.npz"
        fi
    done
    run R12_uniform_verify.log "$PKG" "${W[@]}" dim/ac/uniform_verify.py "$UNODES" 28
    check 'R12 uniform certificate on [0, 1/17]' R12_uniform_verify.log ': UNIFORM CERTIFICATE VERIFIED$'
    run R12_uv_audit_infl10.log "$PKG" "${W[@]}" dimaudit/uv_audit.py "$UNODES" 28
    check 'R12 audit re-run with rounding terms x10' R12_uv_audit_infl10.log 'AUDIT [(]INFL=10, Frobenius G[)] UNIFORM CERTIFICATE VERIFIED$'
}

rows=("$@")
[ ${#rows[@]} -eq 0 ] && rows=(R3 R6 R7 R9 R10 R13 R13b)
if [ "${rows[0]}" = list ]; then DRY=1; rows=(R1 R2 R4 R8 R10b R11 R12); fi
for r in "${rows[@]}"; do
    declare -F "row_$r" > /dev/null || { echo "unknown row $r (rows: R1 R2 R3 R4 R6 R7 R8 R9 R10 R10b R11 R12 R13 R13b)" >&2; exit 2; }
done
echo "package $PKG"
echo "output  $OUT"
echo "python  ${PY[*]}"
if [ -z "${DRY:-}" ]; then
    (cd "$PKG" && sha256sum -c --quiet SHA256SUMS) || { echo "SHA256SUMS check failed" >&2; exit 1; }
fi
for r in "${rows[@]}"; do
    echo "== $r"
    "row_$r"
done
[ -n "${DRY:-}" ] && exit 0
if [ "$fails" -eq 0 ]; then
    echo "ALL SELECTED CHECKS PASSED (${rows[*]})"
else
    echo "$fails CHECK(S) FAILED (${rows[*]})"
    exit 1
fi
