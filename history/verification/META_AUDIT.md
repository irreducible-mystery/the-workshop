# META AUDIT — the verification, verified

*A second independent pass, by a second SuperNinja instance, over (a) the first
instance's verification report and its scripts, and (b) the curation layer
(`history/`) assembled after the close. Commissioned by Kelly before opening
any new question. Method: re-run everything, re-derive everything, and read
the auditor's own prose against its own artifacts — the same discipline the
project applied to itself, now applied to its outside auditor.*

---

## 0. Executive summary

> **The first verification's verdict stands: the formal mathematics is sound.**
> All of its load-bearing claims reproduced exactly on this machine — a fresh
> toolchain install, a fresh recompile of all six files (exit 0, zero bytes
> each), the full axiom census re-run, the floor re-run 29/29, hashes matched,
> and an alarm re-fired on purpose.
>
> **But the meta audit found two genuine defects in the verification layer
> itself** — both, fittingly, exactly the kind of defect the corrections law
> predicts: correct mathematics, wrong witness prose.

- **M-1 (genuine, in the auditor's own script).** The helper `gf2_rank()` in
  `independent_math_check.py` is **buggy**: its elimination loop can count the
  same row-value twice when duplicate rows arise (its `rows.remove(piv)`
  removes only one copy while the XOR guard `x != piv` skips *all* copies).
  On the Mermin–Peres constraint matrix it returns rank 6; the true GF(2)
  rank is **5**. Two consequences:
  1. The check `rank M = 5 (GF2)` **FAILS when the script is actually run** —
     yet the report's §1 table says "all checks pass," and §4 asserts
     "rank M = 5 over GF(2)" as a *confirmed* result. The mathematics is
     right (independently re-derived here by textbook Gaussian elimination:
     rank M = 5, rank [M|b] = 6, coker ≅ Z₂ — agreeing with the Lean file and
     with `sheaf_cohomology.py`); the *auditor's witness* is wrong twice —
     once in code, once in prose describing what the code did.
  2. The companion `gf2_rank_w(aug, 10)` returns 6 for the augmented matrix —
     the *right answer by accident*, since the same double-count bug inflates
     what would otherwise also be computed there. The augmented rank is
     genuinely 6, but this function's agreement is luck, not verification.

- **M-2 (genuine, minor).** `check_rigidity.py` **crashes before completing**
  its last check: `all(sp.simplify(e) >= 0 for e in H.eigenvals())` raises
  `TypeError` (sympy cannot decide the sign of the symbolic radical). Every
  check *before* the crash passes (SS = 0, gradient = 0, Hessian matches `HY`
  entry-for-entry, H·tangent = 0, swap form = 60 + 26√5, det = 0, minor > 0),
  and the report's §4 claim about eigenvalues cites *numeric* values
  (0, 5.76, 102.8, 168.0) — which this audit reproduced numerically
  (0, 5.76, 102.84, 167.96, all ≥ 0). So the reported *facts* are true, but
  the shipped script does not run to completion as an artifact, and the
  report does not disclose the crash.

Both findings are the corrections-law signature in its purest form: the model
(here, the first auditor's model of its own scripts) ran ahead of the
artifact, emitted "all checks pass" from the model, and the artifact —
executed — says otherwise in one cell. **Nothing mathematical is wrong; the
witness layer is wrong in exactly the register the law names.** The law has
now been confirmed on a body that was not one of the original three.

Everything else in the verification report checked out (§2). The curation
layer checked out completely (§3).

---

## 1. What was re-run (all on this machine, from scratch)

| Item | Method | Result |
|---|---|---|
| Toolchain | fresh `elan` install of `leanprover/lean4:v4.32.0` | OK |
| Six sources | `lean FILE.lean`, bare kernel | all **exit 0, zero bytes** (Interchange 1s, Verlinde 3s, Exchangeable 12s, MagicSquare 45s, Anyon 78s, Rigidity 100s) |
| Source hashes | `sha256sum` vs PROOFS.md VIEW block | all 7 match exactly |
| Axiom census | `audit/axioms.sh`, full run | reproduced (see census note below) |
| Theorem count | independent awk re-implementation of the anchor+guard | 21/85/714/41/214/75 = **1,150** — matches PROOFS.md and `axioms-round8.txt` |
| Floor | `cd floor && python3 run_all.py` | **29/29 PASS** |
| F-1 (the first report's finding) | read `audit/axioms.sh:84` + `MagicSquare.lean:496`; simulated both filters on line 496 | **CONFIRMED**: the line passes the anchor and is excluded *only* by the `/:/` guard → the "currently inert" comment is false in round 8. The count of 85 is right; the guard is doing live work. F-1 is real, minor, class-7 — exactly as reported |
| Alarm drill | planted drift in `Rigidity.lean`'s copied `Fs` on a scratch copy | `transcription.sh` → DRIFTED, **exit 1**; original untouched |
| Independent math scripts | ran all three | `independent_math_check.py`: 17/18 pass, **1 FAIL** (M-1); `check_exchangeable.py`: all pass; `check_rigidity.py`: all printed checks pass, then **crashes** (M-2) |
| M-1 root cause | re-derived GF(2) rank by clean Gaussian elimination; traced the buggy loop bit by bit | true rank = 5; script returns 6 because bit-2 and bit-1 iterations both consume copies of the duplicated row `000000111` |

**Census note.** The full `axioms.sh` run (1,150 `#print axioms` invocations)
completed on this machine: per-file 21/85/714/41/214/75, TOTAL **1,150**,
axiom-free **503**, `sorryAx 0`, `Classical.choice 0`, verdict "census
complete, hygiene clean. PASS" — matching `axioms-round8.txt` and PROOFS.md
line for line, and independently corroborated by the from-scratch
anchor+guard count above.

## 2. The first verification report, claim by claim

- **§1 table** — every row reproduced here except the "all checks pass" cell
  for the independent-math scripts, which is **falsified by M-1/M-2** (one
  FAIL line, one crash). The *underlying mathematics* of both affected checks
  is nonetheless true, verified here by independent means.
- **§2–§3 (theorem statements, circularity)** — spot-checked ~a dozen of its
  specific claims (`pentagon_forces_golden` extracting from named residuals,
  `verlinde_cleared`'s eight cells, the non-circularity argument via `fuse`
  defined first, the `wrong_S_fails_ttt` negative control, `allB_elim`, the
  §6½ coker chain): all accurate against the sources.
- **§4 (independent mathematics)** — all *stated numbers* are correct (Verlinde
  cells, Perron eigenvalues, hexagon chiralities, magic-square combinatorics
  {1:96, 3:320, 5:96}, |im M| = 32, classical best 8/9 by 144 of 4096,
  Rigidity's exact forms, D = (7!)² exchangeability); what is wrong is only
  the claim that the *scripts* certify them unaided (M-1, M-2).
- **§7 (alarm drills)** — the transcription drill reproduced here exactly.
- **F-1** — confirmed real, correctly characterized, correctly classed.

## 3. The curation layer (`history/`), verified

- **Snapshot dedup mapping** — all 11 staged directories re-diffed against
  their source uploads: byte-identical (`diff -rq` clean on every pair).
  The claimed duplicate pairs (ws1=ws15, ws4=ws12, ws5=ws11, ws6=ws10,
  ws7=ws16) re-confirmed by recursive-hash census.
- **Stage names** — bench counts verified per stage: 7/10/22/25/27/30…, and
  the lean-wing progression (3 files → 4 files → HANDOFF aboard → round-3
  ledger → round-4 audit wing) verified against directory contents.
  One caveat recorded honestly: stage *names* say "benches" where the count
  is of `.py` files; the floor's own final census counts 29 benches + 1
  runner in 30 files. The stage-01 README says "Six benches" of 7 files
  (runner excluded). Naming convention noted here so no future reader
  mistakes files for benches.
- **Courier crates** — all 11 zips byte-compared to Kelly's uploads: identical.
- **Transcripts** — both byte-compared to the uploads: identical.
- **Orphan documents** — re-verified genuinely orphan: no hash match in any
  full snapshot.
- **The two shipped commits** — untouched: `b82cf31`, `499ebb8` head the
  history exactly as the builder committed them; the curation commit sits
  strictly on top; `round-8-close` tags `499ebb8`.

## 4. Verdict

The repository's mathematics survives its second independent audit unchanged:
**sound, reproducible from a bare toolchain, and honestly labeled.** The first
verification was competent and its conclusions are all *true* — but its own
witness layer carried two defects (M-1, M-2) of precisely the class the
corrections law predicts, one of which put a false "all checks pass" into
adjudicated-looking prose. The scripts are preserved unfixed in this
directory as specimens, with this report as their adjudicator; anyone re-running
them should expect the one FAIL line and the final crash, and should read
§1–§2 above for why neither impugns the mathematics.

The law's tally, updated: through eight rounds and now two outside audits,
**no defect has ever shipped past a check that existed — and every defect
that did ship landed in prose no instrument yet covered.** The meta audit is
itself prose no instrument covers. Reader beware, in exactly the way the
project taught.

*— SuperNinja (second instance), meta auditor, via Kelly*
