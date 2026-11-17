# Layer 13 (blind re-formalization) — Paper I

## Stage 1 — blind text
`paperi_blind.txt` (40,811 bytes), produced by AFM/tools/blind.py on 2026-10-30 from `paperi.tex`:
Lean names, code listings, repo URLs and the code/verification/formalization sections removed;
math macros expanded; leak check (paper's Lean names, dotted identifiers, repo URLs) = 0 hits.

## Stage 2 — blind writer
- Writer model: **gpt-6.1-terra** (Genspark LLM proxy, streaming). Not the draft's author model
  (Claude Opus 5.5) and not one of the draft's three reviewers (Gemini 4 Argon, GPT-6 Astra,
  Claude Opus 5.5).
- Input: the blind text only, split into the four theorem sections, plus the writing rules. No file
  access, no tools, no web.
- Output `Blind.lean`: 78 statements, names `blind_1..blind_78` in paper order, every theorem label
  covered (24), 13 `-- AMBIGUOUS:` readings flagged, each statement `:= by sorry`.
- Type-check: john (arm64, Lean v4.33.1 + Mathlib, `~/lean/reformalH/PaperIBlind.lean`) — **0 errors,
  78 "declaration uses sorry"**.
- sha256 `fd91f4e1047a2e741b8e46e6e807c57bd0ccd854aab830555c2e4a28f0d89be8`.
- Writer report: `WRITER_REPORT.md` (statement list, ambiguities, files read).

## Stage 3 — pairing
`pairs_J.txt` (quadrilaterals + circle systems, jack) and `pairs_M.txt` (arbelos + inversion, john),
built from Table 1 of `paperi.tex` (paper label → real declaration).

## Stage 4 — comparison
Independent comparer per side (Claude Opus 5.5), on work copies of the pinned repositories
(`~/l13_quad`, `~/l13_circles` on jack; `~/lean/l13_arbelos`, `~/lean/l13_inversion` on john),
each pair restated as a `Prop`, both implications proved with unfolding / repackaging / Mathlib only,
no library theorem in a proof body. Gate: `lake env lean scratch/L13_compare.lean` exit 0 and no
`sorry`/`admit`/`native_decide`/`axiom`. Results: `L13_COMPARE_J.md`, `L13_COMPARE_M.md`.

## Stage 4 result — side M (arbelos + inversion, john)
`L13_COMPARE_M.md`; files `L13_compare_arbelos.lean` (sha256 10550482…, 877 lines) and
`L13_compare_inversion.lean` (sha256 7ff27ebd…, 372 lines). Independently recompiled on john:
arbelos rc=0, inversion rc=0; forbidden-token grep empty; no library theorem used in a proof body
(only definitions unfolded; two small library facts re-proved from Mathlib).

29 rows: 21 both directions; 2 restricted (ARTEFACT — the library's ZMod n=0 / strong forms cover
cases the blind hypotheses exclude); 3 one direction only (ARTEFACT: `steiner_porism_strong`,
`steiner_concentric_strong` strictly stronger; `apollonian_integral` R→B proved, B→R open and the
pairing likely off — blind statement matches `isDescartes_foldr`); 3 with no blind counterpart.

REAL findings: `bankoff` and `bankoff_exists` have no blind statement at all (the writer covered only
the incircle in that theorem) — a genuine omission in Blind.lean, to be re-run for that theorem.
`image_inversion_sphere` likewise has no blind counterpart (the blind statements that do exist,
blind_36/37, match `invSphere_isExtTangent`/`_isIntTangent`).

Caveats stated by the comparer: the `pappus_chain` pair is trivial (both sides are field identities);
the incircle pair needed ~10 lines of algebra to show radius > 0.

## Stage 4 result — side J (quadrilaterals + circle systems, jack)
`L13_COMPARE_J.md`; files `L13_compare_quad.lean` (sha256 4c62539e…6c66) and
`L13_compare_circles.lean` (sha256 f1cc99dd…0130) — two files because `Quadrilaterals` and
`CircleSystems` are separate Lake projects that cannot import each other. Work copies `~/l13_quad`
(HEAD 12a24a6) and `~/l13_circles` (HEAD 2f036ed).
Independently recompiled on jack 2026-11-09 20:45 EST: quad rc=0, circles rc=0, no errors, no
warnings; forbidden-token grep (`sorry|admit|native_decide|axiom`) empty in both; `#print axioms` on
every comparison theorem = `[propext, Classical.choice, Quot.sound]`; the in-file library-use audit
reports `library theorems used: []` in both (only compiler-generated definition pieces occur);
`git status --porcelain` empty in both repos (`scratch/` is git-excluded).

19 attempted pairings (20 table rows incl. one not attempted):
- **17 both directions:** Bretschneider, Brahmagupta, Pitot and its converse, Euler, Ptolemy's second,
  Van Aubel, Newton line, Fuss; radical centre, coaxal pencil, `johnson_circle`, `johnson_orthocenter`,
  both Simson pairs, both Steiner-line pairs. The work was in definition bridges (blind cross product =
  `cross`/`areaForm` of `e.toBasis.orientation`, blind foot = `orthogonalProjection`, same-side ↔
  `SSameSide`, convexity ↔ `ConvexQuad`, orthocentre = A+B+C−2·circumcentre from Mathlib's Monge point).
- **1 restricted, ARTEFACT:** blind_49 / `johnson_mem_circles` — the library is stated for any normed
  group (via `omit`), the blind statement and the prose are inner-product only; B→R proved for inner
  product spaces, and that extra generality is invisible in the prose.
- **1 one-direction, ARTEFACT:** blind_48 / `johnson_orthocenter_eq` — the real statement is a
  Mathlib-`Affine.Triangle` repackaging (plane + affine independence), i.e. weaker, so it cannot give
  blind_48 back; blind_48 ⇒ both conjuncts.
- **Not attempted:** `johnson_reflection` and `johnson_congruent` have no blind statement at all —
  **REAL omission on the blind side** (the writer covered circle, membership, second intersections and
  orthocentre only).
No pair shows a misreading of the prose. Blind labels with no partner in `pairs.txt` were not compared:
blind_11–13, 40–42, 44, 45, 47, 50, 54 (the library has plausible partners for some, e.g.
`radicalAxis_eq_inner`, `pencil_radicalAxis`, `isOrthogonal_iff`).

## Stage 4 result — Bankoff pair (john) — closes the REAL omission from side M
`L13_BANKOFF.md`, file `L13_bankoff_compare.lean` (sha256 dbd46998…3d31), namespace `L13CmpBankoff`;
blind source `PaperIBlind.lean` sha256 61a67c73… (blind_79, blind_80). Independently recompiled on john
2026-11-09 20:45 EST: rc=0 with no output; forbidden-token grep empty. `git status --porcelain` shows
only the pre-existing L15 bridge additions — `Arbelos/Bankoff.lean` +47, `Arbelos/Steiner.lean` +186,
0 deletions (`git diff --numstat`).

- Row 1, radius claim (`Arbelos.bankoff` vs `blind_79`): **EQUIVALENT** both directions.
- Row 2, existence (`Arbelos.bankoff_exists` vs `blind_80`): **DIFFERENCE — REAL** (library weaker).
  `bankoff_exists` concludes only `∃ s, C ∈ s ∧ T₁ ∈ s ∧ T₂ ∈ s ∧ s.radius = ab/(a+b)`; the centre is
  nowhere in the statement. `blind_80` names the circle: centre `2a + (ab/(a+b))i`. Checked directly in
  both sources. R→B would need the incircle identified and T₁, T₂ computed — the content of the library
  proof, not repackaging; what R does give is proved (`bankoffEx_R_to_Bweak`, `blind80_to_weak`).
  Not an ambiguity artefact: the prose names the centre. Fix available (add `s.center = 2a + (ab/(a+b))i`
  to the conclusion — the existing proof's witness is that centre, so `rfl` closes it) but not applied.
- The regenerated blind definitions match what the library needs (definitional `bigS`/`leftS`/`rightS`/
  `ptC`; `BlindInternallyTangent`/`BlindExtTangentAtPoint` differ only in strict vs weak positivity and
  `0 ≤ p.im`, both derivable). Nothing missing after the blind.py truncation fix.

## L15 item I5b — Soddy existence (john)
`SODDY_EXISTS.md`, file `soddy_exists.lean` (sha256 0ea3b3fe…947d), namespace `SoddyExists`.
Independently recompiled on john 2026-11-09 20:45 EST: rc=0 with no output; forbidden-token grep empty;
`git status --porcelain` empty.
`classical_I5b` is proved with the statement byte-identical to `PaperIClassical.lean` (sha256 1c595a90…,
which still has `sorry` there), and `ClassicalSignedTangent` / `ClassicalMutuallyTangent` are copied
verbatim (diff against `PaperIClassical.lean` empty). Also proved: `soddy_circle` (explicit construction
at `soddyCentre C ρ`, tangent to all three), `soddy_classify` + `soddy_exactly_two` (any tangent circle
has curvature κ₊ or κ₋ and centre `soddyCentre`; consequently exactly the inner and — when κ₋ ≠ 0 — outer
Soddy circles), `centre_unique`, `soddy_dist_sq`.
Scope: three mutually externally tangent circles with positive radii, as in the I5b hypotheses. The
line-and-two-circles variant (κ₋ = 0) and triples that already contain an enclosing circle are not
covered. Because this is a scratch file, the library still has no existence statement, so the L15 "O"
row for the *library* stands; I5b itself is now proved against the verbatim classical statement and can
be re-recorded as covered by this file.

## L15 item I2b — closed (john)
`ptolemy_order.lean` (sha256 0d2fb504…), namespace `PtolemyOrder`, imports `Inversion`.
`classical_I2b_mp` proves the missing direction (equality in Ptolemy ⇒ cospherical with crossing
diagonals, or collinear with cyclic order); `classical_I2b_mpr` is the known direction;
`classical_I2b` is the full equivalence with the same statement as `PaperIClassical.classical_I2b`.
Recompiled on john: rc=0, no errors, no sorry/admit/axiom/native_decide. I2b moves from N to E in the
L15 inversion table.

## Blind-text defect found (2026-11-09)
The comparer reported `bankoff` / `bankoff_exists` as having no blind counterpart. The cause is not the
writer: `paperi_blind.txt` itself is truncated at `thm:bankoff`. `AFM/tools/blind.py` removes any line
matching its LEAK regex (`Lean|Mathlib|formaliz…|…`), and the theorem's last sentence contained
"(Mathlib's \lean{IsExtTangentAt})", so the whole line — the radius claim, the existence claim and the
explicit centre — was deleted. The rule is meant to drop sentences *about* the formalisation, not
mathematical sentences that mention Mathlib in a citation. Consequence: every paper redacted with this
tool may be missing any theorem sentence that cites Mathlib. Not patched yet (evidence reproducibility);
Paper I's gap was repaired by regenerating the two statements from the full prose.

Addendum: `Blind.lean` now has 80 statements (blind_79 radius claim, blind_80 existence), still 0 errors
on john, 80 sorry warnings; sha256 61a67c73…. Both blind statements compare against
`Arbelos.bankoff` / `Arbelos.bankoff_exists` as recorded above (equivalent / REAL difference).
The truncation fix is confirmed complete for this theorem: no hypothesis the library uses is missing.

## Independent verification, 2026-11-09 20:45–20:50 EST (collector pass)
All four deliverable files were recompiled from scratch on their own machines by the collector, not by
the comparers, and all four exit 0: quad, circles (jack, serialised through `flock ~/pi.lock`), bankoff,
soddy (john). sha256 of each remote file equals the local copy in `AFM/PaperI/layer13/`. Forbidden-token
grep returns no match in any of the four. `git status --porcelain`: empty on jack (both repos) and on
`~/lean/l13_inversion`; on `~/lean/l13_arbelos` only the pre-existing, addition-only L15 bridge diffs.
No comparer process is still running on either machine.
