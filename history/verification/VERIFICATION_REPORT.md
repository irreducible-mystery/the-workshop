# Independent Mathematical Verification Report

## "The Workshop" — Lean 4 Formalization Repository (Round 8 / Terminal Crate)

**Verifier:** SuperNinja (independent third-party audit, commissioned by Kelly) **Scope:** Full repository (`theworkshoprepo.zip`): six Lean source files, capstone documents, seven audit instruments, eight rounds of archives, and the Python "floor" benches. **Toolchain used for reproduction:** Lean 4.32.0 (as pinned by `lean-toolchain`), bare kernel, no lake, no mathlib. Python 3.11 with numpy/scipy/sympy for independent recomputation.

* * *

## 0\. Executive summary

After a complete verification pass — reading all six current source files, recompiling everything from scratch, reproducing the axiom census, re-running every audit gate, re-running the 29-bench floor, firing three alarms on purpose, independently recomputing the central mathematics from first principles in Python/sympy, and reading the prose ledgers against the code — the verdict is:

> **The formal mathematics is sound.** No false theorem statement, no invalid inference, no unstated assumption, no dependency mismatch, no circular argument, and no implementation error was found in any of the 1,150 kernel-checked theorems. Every quantitative claim I could re-derive independently — and I re-derived all the central ones — agrees exactly.

One concrete defect was found, and it is a **documentation-level** defect, not a mathematical one:

> **Finding F-1 (genuine, minor):** the comment block inside `audit/axioms.sh` describing the `/:/` colon-guard as "currently inert" is stale in round 8. `MagicSquare.lean:496` (a round-8 doc-comment line beginning `theorem gives \`coker(M)…\`\`, containing no ASCII colon) is now excluded from the theorem count **only** by that guard. The count of 85 for MagicSquare.lean is _correct_ — the guard did its job — but the script's self-description of the guard as doing no work is false for the current sources. This is precisely the class-7 "characterization prose" defect that the project's own corrections law predicts, and it joins the four specimens the builder's own CLOSING.md audit already recorded.

Everything else either **verified positively** or was **documented as an unsuccessful attack route** (details in §§2–8 below).

* * *

## 1\. What was verified and how (method summary)

| Route | Method | Result |
| --- | --- | --- |
| Kernel reproduction | `lean FILE.lean` on all six files, Lean 4.32.0 | exit 0, **zero bytes** each (Interchange 1 s, Verlinde 2 s, Exchangeable 11 s, MagicSquare 40 s, Anyon 70 s, Rigidity 91 s) |
| Source integrity | `sha256sum` on six sources + `lean-toolchain` | all 7 hashes match the VIEW block in PROOFS.md exactly |
| Axiom census | ran `audit/axioms.sh` in full | **1150 theorems, 503 axiom-free, 0 sorryAx, 0 Classical.choice** — matches PROOFS.md/`axioms-round8.txt` line for line; per-file 21/85/714/41/214/75 |
| Compile receipt | ran `audit/transcript.sh` in full | PASS; hygiene sweep 0 `^axiom`, 0 `^import`, 0 `partial def`; TOTAL 1150 |
| Ledger views | `audit/views.sh check` | PASS — both VIEW blocks match instruments; all 7 sources stamped in both outputs |
| Prose pointers | `audit/pointers.sh` | PASS — all pointers resolve |
| Transcription | `audit/transcription.sh` | PASS — copied ring/pentagon definitions byte-identical modulo declared exceptions |
| Numerals gate | `audit/numerals.sh` | PASS — every bare number sourced |
| Floor benches | `cd floor && python run_all.py` (after `pip install scipy`) | **29 / 29 PASS**, `WELD_REPORT.txt` written |
| Alarm falsification (norm 8/16) | planted defects on scratch copies | all three alarms fired — see §7 |
| Independent mathematics | from-scratch Python/sympy scripts (`independent_math_check.py`, `check_rigidity.py`, `check_exchangeable.py`) | **all checks pass** — see §4 |

* * *

## 2\. Theorem statements and hypotheses (Phase 2) — no defects

Every headline theorem was read in full and checked against its informal claim:

-   **Interchange.lean** (`units_agree`, `eckmann_hilton`, `spacelike`): the Eckmann–Hilton statement is the genuine one — two operations, two units, interchange only; no hidden associativity/commutativity hypotheses. The negative controls (`interchange_can_fail`, `spacelike_needs_interchange`, the `XorModel`/`MirModel` separating models) genuinely establish that each hypothesis is load-bearing, so nothing is vacuously true.
-   **Anyon.lean**: `pentagon_forces_golden` extracts `p² + p = 1` from the named residuals of `pentagonCheck` (not from a re-stated equation); `pentagon_iff`/`pentagon_sufficiency` give both directions; `hexagon_forces_quadratic`/`hexagon_uniqueness` give "exactly two" chiralities with an exhibited-inverse cancellation (the file explicitly does **not** assume K is an integral domain where round 1 wrongly believed it needed to — it proves `KK.eq_zero_or_eq_zero_of_mul_eq_zero` instead). `quantum_dimension_tau` carries an honest-label docstring accurately scoping "Perron–Frobenius as a decidable procedure over Z\[φ\]".
-   **Verlinde.lean**: `verlinde_cleared` states exactly the cleared identity `D²·N_ab^c = verlNum a b c` over Z\[φ\] for all 8 cells; the "NORM 15" adjudicator block accurately delimits what is and is not claimed (no claim about `1/D`, ℝ, ℂ, unitarity, or modularity).
-   **MagicSquare.lean** §6½ (round-8 insertion): the first-isomorphism-theorem chain (`phiV` linear + surjective, `image_iff_even` giving im(M) = ker φ exactly, honest `Quotient` with `coker_two_classes` / `coker_classes_distinct`, anti-vacuity `coker_identifies`/`coker_separates`) is structurally complete; `allB_elim` guarantees the game bound is a genuine ∀-statement, not an enumeration artifact.
-   **Rigidity.lean**: `HY_psd` is proved by an explicit SOS certificate with positivity witnesses (`NY`, `eY1`, `eY2` all shown > 0 in the Z\[φ\] order), the null space is pinned to exactly the gauge tangent (`HY_tangent_null` + `HY_swap_not_null` + `HY_det4_zero` + `HY_minor3_pos`), and rank is bracketed both ways. No vacuous PSD-by-empty-quantification.
-   **Exchangeable.lean**: `exchangeable` is stated over all length-6 words with exact Nat arithmetic (D = (7!)²); `converse_false` provides explicit witnesses, so the equivalence is not overclaimed.

**Attack route documented as unsuccessful:** no theorem was found whose statement is weaker, stronger, or other than its prose description; the honest-label discipline held everywhere I checked, including the traps (parked λ = ζ₂₀¹³, c = −14/5 as label-only, `pentOK ≡ pentagonCheck` declared boundary).

## 3\. Dependency structure and circularity (Phase 3) — no defects

-   **Imports:** all six files contain zero `import` statements (verified by the transcript hygiene sweep and by grep). There is therefore no import graph and no possibility of import cycles. Cross-file sharing is by _transcription_, which `transcription.sh` checks byte-for-byte (and which I falsified on purpose — see §7).
-   **The "closes the circle" claim** (README/PROOFS: "the S-matrix hands the grammar back") was specifically assessed for circularity, since `verlNum` is built from `Msel` and compared to `fuseMult` computed from `fuse`. It is **not circular**: `fuse` is defined first and independently; `Msel` is a _postulated_ matrix that is then independently constrained (`M_sq`: M² = D²·I, `rows_orthonormal`, `dims_from_S`), and `verlinde_cleared` is a genuine _consistency theorem_ between two independently defined objects. The negative control `wrong_S_fails_ttt` (Hadamard matrix fails cell (τ,τ,τ)) proves the identity is discriminating — a reverse-engineered tautology could not fail on a different S. One scoping note: the S-matrix is **chosen, not derived** in Verlinde.lean; the prose ("hands the grammar back") is fair because the theorem is exactly "this modular datum reproduces the fusion rules," and the file's NORM 15 block says so explicitly.
-   **Uniqueness step in the Verlinde docstring:** the argument "Z\[φ\] is a domain and D² ≠ 0, so D²·k = D²·k′ forces k = k′" is discharged formally: `Zp.eq_zero_of_mul_eq_zero` (Anyon.lean:6522, with anti-vacuity `domain_witness`) plus `Zp.mul_left_cancel`\-style reasoning and `norm_Dsq`/`Dsq_norm_not_unit` are all present as kernel-checked theorems. No unstated assumption.
-   **Definitional circularity** (a def assuming its theorem): none found. The Perron order (`Zp.pos`/`Ord5.posUN`) is a decidable procedure justified by its own mod-5 descent theorems, not by the eigenvalue claims it later supports.

## 4\. Independent mathematical recomputation (Phase 5) — all agree

From-scratch scripts (attached), sharing no code with the repository:

-   **Pentagon:** 50 valid index tuples of 512 (matches `pentagonValid` count); golden-ratio F-matrix satisfies all instances to ~1e−16; residual system forces qr = p, p² + p = 1, s = −p — the same three residuals `pentagon_forces_golden` uses.
-   **Hexagon:** 15 instances satisfied; eigenvalue quadratic and the two chiralities (λ = e^{∓4πi/5} family) confirmed; Yang–Baxter holds; braiding non-abelian (‖\[B₁,B₂\]‖ ≠ 0).
-   **Perron:** fusion matrix \[\[0,1\],\[1,1\]\] has eigenvalues φ, −1/φ; the unique positive one is φ — confirming `quantum_dimension_tau`/`perron_selection`.
-   **Verlinde:** all 8 cells of D²·N = verlNum verified in exact Z\[φ\] arithmetic; N(D²) = 5; wrong-S control fails at (τ,τ,τ) exactly as claimed.
-   **T-layer:** (ŜT)³ = (φ+2)·pp·I confirmed in exact Z\[ζ₅\]; pp·pm = D²; pp⁴ identity; λ·D = pp with λ = ζ₂₀¹³ consistent with c = −14/5 as a label (numerically, no ring claim); ribbon twist and Frobenius–Schur indicator consistent.
-   **Rigidity (sympy, exact):** SS(Yang–Lee) = 0; gradient = 0; the 4×4 Hessian matches `HY` entry-for-entry; H·tangent = 0; the swap direction's quadratic form = 34 + 52φ (matches `HY_swap_not_null`); det H = 0; the 3×3 minor = 21120 + 31480φ > 0 (matches `HY_minor3_pos`); the SOS identity is an exact polynomial identity; numeric eigenvalues (0, 5.76, 102.8, 168.0) all ≥ 0.
-   **Magic square:** rank M = 5 over GF(2), rank \[M|b\] = 6, |im M| = 32 = the even-weight covectors exactly, b odd hence outside, left kernel = {0, 1⃗}, coker ≅ Z₂; satisfiable-context histogram {1: 96, 3: 320, 5: 96} (max 5); classical game: 4096 strategies, best = 8 of 9, attained by 144.
-   **Exchangeability (exact Fractions):** two-urn Pólya prior sums to 1; probability depends only on transition counts (exchangeability); D·P integral with D = (7!)²; converse-false witnesses pA/pB/pC behave exactly as `converse_false` claims.

**Result: zero numerical discrepancies across every route.**

## 5\. Axioms and assumptions (Phase 4) — clean

-   Full census reproduced: **1150 / 503 axiom-free / 647 carrying only `propext` and/or `Quot.sound` / 0 `sorryAx` / 0 `Classical.choice`.**
-   Hygiene sweep: 0 top-level `axiom`, 0 `import`, 0 `partial def`, 0 `native_decide` outside comments, no raised budgets (`maxHeartbeats`/`maxRecDepth` appear only in a prose line).
-   Spot checks: `verlinde_cleared` and `image_iff_even`/`imageCount_eq_32` axiom-free as claimed; the coker theorems carry exactly `[propext, Quot.sound]` as claimed (+3 in that class, matching CLOSING.md's reconciliation of +22 = +9 free, +10 propext, +3 both).
-   The census's own count/anchoring logic was audited — which is where Finding F-1 arose (§6).

## 6\. Findings

### F-1 (genuine, minor, documentation): stale "currently inert" comment in `audit/axioms.sh`

-   **Location:** `audit/axioms.sh`, comment block (~line 84): _"the guard is what caught THAT site, and it is currently inert — kept because the next such line costs a run."_
-   **Contradicting evidence:** an exhaustive scan of all six round-8 sources for anchor-matching colon-free lines returns exactly one: `MagicSquare.lean:496` — `theorem gives \`coker(M) = GF(2)⁶/im(M) = GF(2)⁶/ker φ ≅ im φ = Z₂\`.`— a doc-comment line inside the new §6½, beginning with the word`theorem`at column 0 and containing **no ASCII colon** (only`≅`and backticks). It passes the anchor`/^theorem \[A-Za-z\_0-9\]+/`and is excluded from the count **only** by the`/:/\` guard. Archived rounds 2–7 have no such line; round 8 introduced it.
-   **Impact:** none on the mathematics or the counts — MagicSquare's 85 is correct _because_ the guard worked. The defect is that the instrument's self-description ("inert") is false for the sources it now measures. It is a class-7 characterization slip with no execution date, invisible to every gate by design — exactly the failure shape the project's corrections law predicts, and a fifth specimen alongside the four CLOSING.md already recorded for the terminal round.
-   **Verdict:** genuine but minor; recommend rewording the comment to "the guard is live on the round-8 sources: it is the sole excluder of MagicSquare.lean:496."

### Confirmations of the builder's own recorded terminal defects (CLOSING.md)

I independently re-verified all four class-7 slips CLOSING.md reports, and all four check out as described:

1.  **MagicSquare.lean header** (line 14) still says _"five uses of `decide` and exactly two of `omega`"_; the file now contains **8** decide-tactic uses (lines 397, 447, 454, 573, 589, 692, 729, 734) and 2 omegas. The header is stale exactly as CLOSING.md says (the same header C3′ corrected in round 2).
2.  **Gap-table totality sentence** (PROOFS.md:332, _"Every row any round's DECLARED GAPS table ever carried"_): the round-1 table (archive/ PROOFS-round1.md §DECLARED GAPS) carried `best == 8`, `best == 5` sharp, and Tier 4a/4b rows that do not appear in the terminal table (they were closed in round 2 — the mathematics is fine; the _coverage sentence_ is false, as CLOSING.md says).
3.  **"A source list can no longer drift between them"** (PROOFS.md:377): `audit/sources.txt` exists and is consumed by pointers/transcript/views/ ship — but `audit/axioms.sh` still hard-codes its six-file list (lines 60, 66, 122). Three-of-four fold, as CLOSING.md says.
4.  **Coker park dating** (PROOFS.md:112, "by agreement in round 2"): the agreement is ROUND3.md's Q3 ("Left kernel exact + duality cited is enough — agreed"), as CLOSING.md says.

These are _already-adjudicated_ defects, recorded in the crate itself; I list them as confirmations, not new findings. Notably, my one new finding (F-1) is of the same species — which is itself evidence _for_ the corrections law the repository proposes.

## 7\. Alarm falsification — every alarm fired (norms 8/16, VERIFY.md §"don't trust an alarm you haven't seen fire")

1.  **transcription.sh:** changed `F x y` → `F y x` inside the copied `Fs` in `Rigidity.lean` → `DRIFTED Fs — copy differs from original`, **exit 1**. (Control: whitespace-only change → still PASS, i.e., the comparison is normalized, not trivially byte-fragile.) Source restored, hash verified.
2.  **numerals.sh:** added a bare `7777` to PROOFS.md prose → `UNSOURCED 7777 … FAIL (gate)`, **exit 1**. Restored, hash verified.
3.  **axioms.sh:** planted a `sorry` in the proof of `units_agree` in a scratch copy of the crate → the file still compiles (with only a warning, i.e. a grep-for-sorry could be fooled by a comment but a compile alone passes), yet the census reports `sorryAx 2 (must be 0)` — **two**, because the downstream theorem that cites `units_agree` inherits the taint — `!! HYGIENE FAILURE`, `RESULT: FAIL`, **exit 1**. This confirms the project's claim that the census, not a grep, is the authoritative unproved-content check, and that taint propagates through citation.

## 8\. Reproducibility verdict (Phase 7)

Every box of VERIFY.md's reproduction checklist was checked and passed on this machine: source hashes, toolchain 4.32.0, six silent compiles, transcript PASS with TOTAL 1150, axioms census PASS with 1150/503/0/0, pointers PASS, views PASS, transcription PASS, numerals PASS, floor 29/29 with WELD\_REPORT.txt. Compile times fell within or near the documented ranges. The `.olean` hashes were (correctly) not treated as invariants per VERIFY.md's own caveat.

* * *

## 9\. Conclusion

-   **False theorem statements:** none found.
-   **Invalid inferences:** none found (kernel-checked; census clean; spot-read proofs sound).
-   **Unstated assumptions:** none found (0 axioms declared; 0 Classical.choice; domain/cancellation properties that prose invokes are formally proved, incl. `Zp.eq_zero_of_mul_eq_zero`, `KK.eq_zero_or_eq_zero_of_mul_eq_zero`).
-   **Dependency mismatches:** none (zero imports; transcription gate live and falsifiable).
-   **Circular arguments:** none (the Verlinde circle is a consistency theorem with a discriminating negative control, not a tautology).
-   **Implementation errors:** none found; all independent recomputations agree exactly.
-   **Prose ↔ code discrepancies:** one new minor one (F-1, the stale "inert" guard comment in `audit/axioms.sh`), plus independent confirmation of the four the builder's own final audit already recorded. All are characterization prose; none touches a theorem.

The repository's central claim — _"never wrong where a kernel could reach"_ — survived every attack route I could construct. The one defect I found lives exactly where the project's own theory says defects must live: in unadjudicated human sentences about the instruments, not in the mathematics.

_Report prepared with all evidence reproducible from the attached scripts and the repository's own instruments._