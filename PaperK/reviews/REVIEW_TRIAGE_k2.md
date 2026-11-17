# Paper K — round-2 review triage (v3 → v4)

Two independent reviews of the frozen 16-page v3 (`paperk.tex` `b235a490…`, `paperk.pdf` `32f53431…`) at the
pinned commit `464a59d`, run 2026-11-17 08:51–09:03 EST on Josh's instruction ("match with Argon and Astra
into V4"):

- `REVIEW_v3_argon.md` — `gemini-4-argon`, verdict **minor revision**, 0 MAJOR / 9 MINOR.
- `REVIEW_v3_astra.md` — `gpt-6-astra`, verdict **major revision**, 6 MAJOR / 10 MINOR.

25 finding rows, **21 distinct** (four are the same defect reported by both: Astra 2 = Argon 1, Astra 10 =
Argon 3, Astra 14 = Argon 7, Astra 15 = Argon 6). Every row is dispositioned below: all 21 distinct findings are accepted in substance, 18 applied as
proposed and 3 in a narrowed form, plus 1 defect found during triage outside both reviews and fixed.

v4 = `paperk.tex` `49920863…`, `paperk.pdf` `bf01d137…`, 16 pp, 0 errors, 0 undefined refs, 0 `\PH`, name
gate PASS 57 / 18.

## Round-1 verification first

Argon independently re-checked all 12 round-1 MAJOR findings against the code and reported them applied; Astra
re-checked the same and reopened three of them (its 2, 3, 4) plus one it had itself raised in round 1 (its 6,
which round 1 marked closed). Where the two reviews disagree, I verified the text and the Lean myself; the
dispositions below record what the evidence showed, not who said it.

## Astra's MAJOR findings — verified one by one

### 1. The cofactor candidate is not an existence theorem — ACCEPTED, applied
`prop31_cofactor` takes `hP3 : (G *ᵥ cofactor M) 3 ≠ 0` (`LieCore.lean:140–144`), so orthogonality is what
Laplace gives; the nonzero finite vector is still assumed, and at rank < 4 every maximal minor vanishes. The
v3 sentences "so that the existence of `P` is discharged by the Laplacian identity instead of assumed" and
"its null vector is a cofactor vector" were therefore wrong as printed. §4 now says the orthogonality is
discharged and the `v`-slot is still assumed, and the source-definition paragraph adds the full-row-rank
qualification with the square as the lower-rank case. Argon read the same sentences as accurate; the Lean
signature settles it for Astra.

### 2. "cycle $P$" in Theorem 4 and the tetrahedron paragraph — ACCEPTED, applied
`TwoD.lean:177` and `ThreeD.lean:91` quantify over arbitrary vectors; the prose restricted them to null
vectors. A safe restriction, but it is the defect round 1 asked to fix and it was fixed in only one of the two
places. Both now read "any vector ... (no null-cone hypothesis on $P$ is required)". Same edit as Argon 1.

### 3. Plane encoding sign error in §10(2a) — ACCEPTED, applied
Checked directly: with `B(X,Y)=rr'−c·c'−vw'−wv'`, the vector `(1,n,0,w)` pairs with an affine cycle as
`r−n·c−w`, so it is the plane `{x : n·x = −w}`. v3 wrote the plane as `{x : n·x = h}` *and* the vector as
`(1,n,0,h)`, then said that vector is the plane `{n·x = −h}` — internally inconsistent by one sign. Corrected
to: plane `{n·x = h}` ↔ `(1,n,0,−h)`, tangency `r−n·c+h=0`. Also added the normalisation `H_0=1`,
`‖H_c‖=1` to the definition of `T_i`, which Astra asked for so that `T_i` cannot contain the zero or a
degenerate `(0,0,0,w)` vector. Argon had checked the parenthetical clause but not the leading clause.

### 4. Appendix square row drops the affine qualifier — ACCEPTED, applied
§7 says "among affine cycles"; the appendix row said the source's hypothesis "holds" flat. L15 row 11 records
that the projective "exactly two" was not established. The row now says "holds among affine cycles" and names
the `v=0` exclusion as a hand argument.

### 5. "covered by the token scan and the build only" is false for 9 of the 19 — ACCEPTED, applied
`gate.sh` prints an axiom report per `REQUIRED` declaration, and each report covers the transitive dependency
cone. `brief_E_false` uses `cex_pt_ne`, `cex_sum`, `cex_affInd`, `cex_orth`; `PaperKn.prop31` uses
`pt_affine_comb`. Those are axiom-checked, not merely token-scanned. Both places (§9 gate paragraph and the
GeneralN paragraph) now distinguish "no separate gate-generated axiom report" from "not axiom-gated", and say
which are covered transitively.

### 6. The L13 comparer is not at the pinned commit — ACCEPTED, applied
Confirmed: `scratch/` is absent from `repo_snapshot_464a59d` and from the public tree; the L13 report itself
says `scratch` was ignored and HEAD unchanged. v3's "`scratch/BlindCompare_K.lean` at `\pkcommit`" sent a reader
after a file that is not there. Now: `PaperK/layer13/BlindCompare_K.lean` in `LEAN-verification`, outside the
code commit and its gate, run against `464a59d` from an untracked work copy.

## MINOR findings

| # | reviewer | finding | disposition |
|---|---|---|---|
| A1 / S2 | Argon, Astra | "cycle $P$" in Thm 4 and tetrahedron | applied (both places) |
| A2 | Argon | `tetraFamR` scales centres as well as radius | applied: centres `(±s,±s,±s)`, radii `s(√3+1)`, `s(1−√3)` |
| A3 / S10 | Argon, Astra | §1 says 13 restatements; attributes error-catching to restatements; "became a Lean theorem" | applied: 21 claim rows across three files; errors attributed to the numerical checks and the general-`n` run; "now a Lean theorem in its negated form" |
| A4 | Argon | `PaperKn.prop31` also gives the affine weights | applied |
| A5 | Argon | `simplex_circumradius` is a vertex-norm identity, not Mathlib's circumradius; `dist_sq_const` holds for any common radius | applied (both), with the hand identification noted |
| A6 / S15 | Argon, Astra | stale preamble comment (no public remote); stale "earlier commit (the battery's mutation layer)" caveat | applied: comment rewritten; caveat replaced by "every figure is from the run at that commit" |
| A7 / S14 | Argon, Astra | appendix rows 2, 4, 16 wording (quantifies over / v≠0 only / necessary) | applied: "no theorem is stated for hyperplane cycles"; identity-vs-iff split; "cannot be dropped ... as the counterexample shows" |
| A8 | Argon | `L11_K_ANCHORS.md` still records the v2 run (56 names) | applied: regenerated for v4 (57 / 18, hashes, page count) |
| A9 | Argon | the Carver (1920) sentence is in the Zenodo abstract/kit but the paper never mentions Carver | applied: sentence removed from `ABSTRACT_plain.txt`, `ZENODO_DEPOSIT_K.md` and `INDEX.md`; the paper makes no at-infinity claim, so no credit belongs in its metadata |
| S7 | Astra | §5's "what is missing in Lean" is understated given `s19_RB` | applied: the section now says the link is not a theorem of the pinned library but was certified in the supplementary `L13Compare.s19_RB`, from the types of `row_relation` and `cof0–cof4`; the abstract's "not formalised" narrowed accordingly |
| S8 | Astra | §5 calls `(r,a,b,s,1)` "the four cycles"; §3 value constant uses `(X∣X)` not `(P∣P)` | applied: auxiliary data matrix, with the rows explicitly not cycle vectors; `(P∣P)` |
| S9 | Astra | the fourth circle does not make the triple's Apollonius pair exist or move it; no existence claim is proved | applied: the paragraph now separates the triple's concentric pair from the other subsets' pairs, states the theorem is not an existence statement, and gives Astra's counterexample (a fourth unit circle at `(0,1)` forces `v=0`; re-derived here before use). §1 "for any fourth circle" rephrased; EXTENSION §2 described as a perturbation of one input circle |
| S11 | Astra | "remaining differences are artefacts" over-reads s25/s36/s40; "both had already been repaired" was not quite true | applied: "no implication certificate is supplied for s25, s36 or s40"; and the two prose gaps are now genuinely closed — `P` added to Theorem 1's list of objects, `Y` stated to be a null vector with `Y_3=1` |
| S12 | Astra | "testing the statements rather than the proofs" overstates the tamper suite | applied: rejection is of the modified statement/proof pair at build time; independently checked counterexamples, not the build, establish falsity |
| S13 | Astra | L14b/L14c results are absent from the prose although they exist | applied: both named as outside the gate and outside the 73 |
| S16 | Astra | signature claim; "every statement about the centre carries P_3≠0"; "both cases occur below"; "null space drops" | applied: signature identified by hand; the centre sentence narrowed to the geometric conclusions proved; only the concentric case is claimed below; rank falls 4→3 and the kernel grows 1→2 |

## Found in triage, not reported by either reviewer

**F0 — every `\decl{...}` name printed with a literal backslash.** The `\decl` macro is `\url`-based, and
inside `\url` the escaped form `\_` is typeset literally, so v1–v3 printed `PaperK.B\_G\_cofactor\_row`,
`PaperK2.equilateral\_PX`, and so on, in 92 declaration names throughout the PDF. Both reviewers read the
text (Astra via `pdftotext`, which preserves the backslash) and neither flagged it. v4 passes the bare
underscore inside `\decl{...}`; `\UrlBreaks` still allows the break and all names have the usual underscore
glyph. The name gate is unaffected (57 / 18, PASS) because it reads names from the tex.

## Not accepted as worded

1. **Astra 9's implied fix to the theorem's hypotheses** — adding "whenever such a finite orthogonal `P`
   exists" is inside the theorem's own quantifier ("let `P` be ... with `P_3≠0`"); the existence point is
   made in the paragraph, not as a hypothesis. The counterexample is kept as prose evidence.
2. **Astra 3's request to restate `T_i` as a set of hyperplanes only** — applied as the normalisation
   `H_0=1`, `‖H_c‖=1` rather than by changing the set's role; `T_i` is not used in any Lean statement.
3. **Astra 10's implied rewrite of `L14` section's credit** — the credit split in §9 is accurate as it stands
   (the equal-norm finding is the general-`n` run's, the sign is the numerics'); only the §1 sentence was
   wrong and it is fixed.

## Result

- v4 built: 16 pp, pdflatex twice rc=0, 0 errors, 0 undefined references, 0 live `\PH`, one cosmetic
  overfull inherited from v3.
- Name gate: PASS, 57 `\decl` / 18 `\src`, 0 ungated (`repo_flat_464a59d`).
- Nothing in the Lean repository changes: all code claims remain at the pin `464a59d`. The PDF's numbers
  (73 / 9 / 444-460 / 73-54 / 238-4 / 24-3-21 / 36 / 17 / 43) are unchanged and were re-verified by both
  reviewers, independently, against the pinned export.
- Deposit kit refreshed: new PDF and tex in `deposit/zenodo/` and in
  `deposit/LEAN-verification-PaperK/preprint/`, `ZENODO_DEPOSIT_K.md`, `SHA256SUMS`, `L11_K_ANCHORS.md`.
