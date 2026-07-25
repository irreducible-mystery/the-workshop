# SCEP AUDIT RESULTS — "The Workshop"
**Audited:** `irreducible-mystery/the-workshop` @ `main` (`e0b09a5`), tag `round-8-close`
**Instrument:** SCEP v1.0 / CEP v1.0 / AUDIT_CHECKLIST v1.0
**Auditor:** SuperNinja (independent), on a fresh VM, everything re-run from scratch
**Date:** 2026-07-24 (audit session)

---

## 0. AUDIT BASIS — what was actually verified (not taken on trust)

Per SCEP §4.3 (data verification), every score below rests on artifacts examined and commands executed on this machine:

| Reproduction step | Result |
|---|---|
| All 7 source hashes (`sha256sum`) vs VERIFY.md | **all match exactly** |
| Fresh elan + Lean 4.32.0 (pinned by `lean-toolchain`) | installed, version confirmed |
| All six `.lean` files compiled, bare kernel | **exit 0, zero bytes, all six** (norm 10 pass) |
| `audit/axioms.sh` full census (1,150 × `#print axioms`) | **TOTAL 1150 · 503 axiom-free · 0 sorryAx · 0 Classical.choice · PASS** |
| `audit/pointers.sh` | 194 pointers, 0 unresolved, PASS |
| `audit/views.sh check` | PASS (views match instruments, sources stamped) |
| `audit/transcription.sh` | PASS (copies byte-identical mod declared exceptions) |
| `audit/numerals.sh` | PASS (every bare numeral sourced or labeled) |
| `floor/run_all.py` (29 benches) | **29/29 PASS**, WELD_REPORT written |
| All capstone/process docs read in full | README, PROOFS, CLOSING, REGISTER, HANDOFF, VERIFY, GOING-FORWARD, ROUND2–8, META_AUDIT, VERIFICATION_REPORT, OPEN-QUESTIONS |

**Domain adaptation note (required for honest scoring).** The workshop is not an operational system: no runtime, no actuators, no operators at risk. Its criticality domain is **epistemic** — the hazard is *a false claim shipping as verified*. The audit therefore maps SCEP's physical-safety vocabulary onto the epistemic domain (safe state ≈ never ship an unverified claim; fault ≈ defect in math or witness prose; incident ≈ crash/defect/near-miss in the round record). Items with no meaningful epistemic analogue are N/A with justification.

---

## SECTION A — FOUNDATIONS & CLASSIFICATION (9/10)

| # | Item | ⛔ | Score | Evidence / Notes |
|---|---|---|---|---|
| A1 | Criticality explicitly classified | ⛔ | 1 | Implicit but real: the "execution date" taxonomy (kernel-adjudicated vs inventory prose) is a criticality classification of claims, and rigor tracks it. Not framed as formal risk classes with severity/likelihood. |
| A2 | Worst credible consequence considered | | 2 | The project's *worst failure shape* is explicitly named and analyzed: "fully kernel-checked, entirely sound, and about the wrong object" (REGISTER, class 10) — exactly a worst-credible analysis. |
| A3 | Rigor scales with classification | | 2 | Load-bearing claims → kernel; hygiene → census; prose → 4 instruments; characterization → audit loop. Explicit, documented scaling. |
| A4 | Safe states defined | ⛔ | 2 | Epistemic safe state enforced: placeholders held until an instrument renders the number (near-miss records, PROOFS); PARKED/BLOCKED/NOT-ATTEMPTED statuses instead of guessing. "Nothing false built." |
| A5 | Lifecycle gates | | 2 | Round structure with crate-time checklist (norm 15), ship gate (`ship.sh` refuses default round), environment-parity handshake on resume. |

## SECTION B — HAZARD ANALYSIS (13/16)

| # | Item | ⛔ | Score | Evidence / Notes |
|---|---|---|---|---|
| B1 | Hazard analysis exists, predates design | ⛔ | 1 | Real and deep, but *emergent*: the defect-class analysis and corrections law were discovered during rounds, not performed up front. |
| B2 | Living hazard log with schema | ⛔ | 1 | REGISTER.md is a living adjudication log (class, born, adjudicator, coverage boundary) + terminal gap table + numbered corrections. Missing: severity/likelihood/residual-risk fields per SCEP §4.2. |
| B3 | Appropriate techniques (FMEA/FTA/STPA) | | 1 | No named formal technique; however the register-age analysis is a bespoke control-structure analysis of the writing system (STPA-like in spirit: unsafe *control actions* of the author-model). |
| B4 | Interaction/emergent hazards analyzed | | 2 | Exceptional: courier-channel hazards, cross-file transcription drift, model-emitted prose, reason-transplant across artifact sets (H1) — all interaction failures, all analyzed. |
| B5 | Mitigation precedence (design-out first) | | 2 | Views are *rendered, never typed* — eliminating the hazard by design rather than warning about it. `ship.sh` designs out the "wrong round" hazard by refusing defaults. |
| B6 | Mitigations trace to verification | | 2 | Every instrument "verified to bite" on a planted defect before trusted (norms 8/16). |
| B7 | Residual risk formally accepted | | 2 | Class 7 declared frontier, gap table's honest kinds, "the one honest boundary" in VERIFY — residual risk accepted explicitly, in writing, by both bodies. |
| B8 | Updated on change | | 2 | Register diffs required each round (norm 15); gap table restored silently-dropped rows in round 8. |

## SECTION C — REQUIREMENTS (11/12; C7 N/A)

| # | Item | ⛔ | Score | Evidence / Notes |
|---|---|---|---|---|
| C1 | Written, atomic, identified requirements | | 1 | Charter + 16 norms + per-round charges serve as requirements; not atomic/ID'd in the formal sense. |
| C2 | Safety requirements flagged | | 2 | Load-bearing vs non-load-bearing explicitly distinguished throughout ("nothing load-bearing standing"). |
| C3 | Negative requirements | | 2 | "No unmarked sorry", "zero imports", "0 Classical.choice" — shall-nots, machine-enforced. |
| C4 | Off-nominal behavior specified | ⛔ | 2 | Instrument failure semantics specified (exit codes, STALE/DRIFTED states); crash guardrails specify what to do when a proof approach fails (split, never raise budgets). |
| C5 | Bidirectional traceability | | 2 | pointers.sh (prose→artifact), views.sh (artifact→prose), numerals.sh, transcription.sh — enforced by tooling, audited. Rare even in certified industry code. |
| C6 | Assumptions documented + monitored | | 2 | Exemption lists with reasons; declared boundaries; and the audit loop caught a *false reason* (H1) — the monitoring works. |
| C7 | Timing/resource quantified | | N/A | Wall-times explicitly declared "not load-bearing" — an honest anti-requirement. No real-time claims exist. |

## SECTION D — ARCHITECTURE & DESIGN (18/20)

| # | Item | ⛔ | Score | Evidence / Notes |
|---|---|---|---|---|
| D1 | Detect→isolate→contain→recover | ⛔ | 2 | Detection (instruments), isolation (quarantine, norm 16), containment (register class), recovery (corrections loudest first, numbered, closed). |
| D2 | Watchdogs / health monitoring | | 1 | The instruments *are* health monitors but run per-round, not continuously; the project itself names this: "the loop runs once per round rather than once per sentence." |
| D3 | Redundancy with independence | | 2 | Two computations built blind on opposite sides of the courier agreeing cell-for-cell (Verlinde race); floor + kernel co-sign everything; two outside auditors. Genuine common-cause diversity. |
| D4 | Isolation/partitioning | | 2 | Zero imports = maximal isolation; six mutually independent files; costs of isolation honestly priced (class 10). |
| D5 | Graceful degradation | | 2 | PARTIAL/PARKED/BLOCKED taxonomy degrades claims honestly instead of failing silently or overclaiming. |
| D6 | Interfaces documented | | 2 | Courier channel spec: zip + SHA-256 carried *outside* the crate, manifest read back by spec-following extractor (REGISTER class 8). |
| D7 | Inputs validated at trust boundaries | ⛔ | 2 | Crates hash-verified both directions; `ship.sh` builds with one tool, re-reads with another; VERIFY.md mandates checkout hash validation before trusting anything. |
| D8 | Data integrity protected | | 2 | SHA-256 stamped into every instrument output ("a view names what it viewed"); staleness detection (STALE check). |
| D9 | Hazardous commands positive confirmation | | 2 | `ship.sh` requires the round argument — "no safe default" — a literal arm/fire pattern, added after a near-overwrite. |
| D10 | Dependencies inventoried/pinned | | 1 | Lean toolchain pinned exactly (v4.32.0) and stamped. **Gap:** floor's numpy/scipy unpinned, no `requirements.txt`, no Python version recorded. |

## SECTION E — IMPLEMENTATION (18/20; E10 N/A)

| # | Item | ⛔ | Score | Evidence / Notes |
|---|---|---|---|---|
| E1 | Coding standard enforced by tooling | | 1 | Norms are enforced by instruments — but invocation is manual/per-round; no CI runs them on every change. |
| E2 | Bounded computation on critical paths | | 2 | "Never raise a budget" norm — the direct analogue of bounded loops, learned from the crash, held for six rounds. |
| E3 | Resource discipline | | 2 | Headless heavy checks; scratch-file development (norm 11: 7s vs 200s feedback loops); failure output kept small by design. |
| E4 | Small verifiable units | | 2 | Calc-step splitting doctrine: "if a step will not close, it is too big: split it." |
| E5 | Assertion density / invariants | | 2 | Anti-vacuity counts pin every guarded ∀ (norm 3); negative controls per check (norm 5); `allB_elim` guards against enumeration artifacts. |
| E6 | Every return checked | ⛔ | 2 | Exit-code discipline everywhere; pass condition is *silence* (exit 0 AND zero bytes) — stricter than SCEP requires. |
| E7 | Zero-warning policy | | 2 | Norm 10: a warning is a failure. Verified on this machine: six files, zero bytes each. |
| E8 | No dead/orphan code | | 2 | pointers.sh caught a scaffold cited as a shipped theorem (its founding catch); phantom names impossible now. |
| E9 | No magic numbers | | 2 | numerals.sh: every bare multi-digit number in prose must match an instrument output or labeled exemption. Beyond industry practice. |
| E10 | Concurrency design | | N/A | No concurrent execution anywhere. |
| E11 | Flight-recorder logging | | 2 | Total: every round letter, ledger, transcript, crash-autopsy, and courier manifest preserved; git history append-only; predecessor's last words before the crash are in the record. |

## SECTION F — VERIFICATION & VALIDATION (20/22)

| # | Item | ⛔ | Score | Evidence / Notes |
|---|---|---|---|---|
| F1 | 100% review with independence | | 2 | Builder audited every round from the outside; citations spot-verified 22 deep; two further independent auditors (VERIFICATION_REPORT, META_AUDIT) — including an audit *of the auditor*. |
| F2 | Every requirement has a test | | 2 | Every claim class has a named adjudicator or is a declared frontier (REGISTER) — the requirement↔verification map is the project's centerpiece. |
| F3 | Test levels | ⛔ | 2 | Kernel (unit) → census (hygiene) → instruments (integration) → floor co-signature (system) → outside audit (acceptance). |
| F4 | Coverage measured, gaps dispositioned | | 2 | Census covers all 1,150 theorems; the uncovered register (class 7) is named, bounded, and dispositioned in writing. |
| F5 | Fault injection | ⛔ | 2 | Exemplary: planted `sorry` (census must exit 1), planted 2-char drift (DRIFTED), stub Lean kernel planted in `$HOME/.elan/bin` to falsify the transcript checker, planted bare numerals. "An alarm you cannot make fire is not an alarm" = SCEP VV-7 verbatim. |
| F6 | Off-nominal test effort | | 2 | Negative controls mandatory per check (norms 5, 8); `wrong_S_fails_ttt` Hadamard control; `converse_false` witnesses. |
| F7 | Automated regression on every change | | 1 | Full regression exists and is cheap (~10 min) but is invoked by hand per-round; nothing runs on push. |
| F8 | Static analysis in CI | | 1 | The instruments are static analyzers of prose+code; there is no CI to host them. |
| F9 | Environment representativeness | | 2 | Toolchain pinned; cross-platform caveats documented precisely (.olean hashes declared non-invariant; invariants enumerated). |
| F10 | Evidence retained, reproducible | | 2 | axioms-round4..8.txt, transcripts, per-round source snapshots. **This audit is the proof: everything reproduced exactly on a fresh machine.** |
| F11 | Validation in realistic scenarios | | 2 | The methodology was validated on fresh instances (a crashed prover's successor resumed from the crate alone and succeeded) and on outside auditors — the strongest available analogue. |

## SECTION G — CONFIGURATION & CHANGE (11/12)

| # | Item | ⛔ | Score | Evidence / Notes |
|---|---|---|---|---|
| G1 | Everything versioned | ⛔ | 2 | Now git (append-only history, tag `round-8-close`); during rounds, zip+SHA courier with manifests. Archives keep every round's sources. |
| G2 | Reproducible builds | | 2 | Fully reproduced here from `lean-toolchain` up. |
| G3 | Change control + impact assessment | | 2 | Corrections numbered, adjudicated, closed with restating-sites enumerated (norm 13); crate-time checklist question (norm 15) is a per-change safety-impact assessment. |
| G4 | Emergency change path with post-hoc completion | | 2 | The round-3 crash: expedited handoff with complete autopsy + binding guardrails delivered inside the same handoff — post-hoc analysis done in full. |
| G5 | Tested rollback | | 1 | Every prior round's state preserved and hash-verified (rollback *exists*); restoring from a crate was live-tested once (the crash recovery). Not a routinely drilled procedure. |
| G6 | Config as code | | 2 | `lean-toolchain` versioned, stamped into every instrument output; exemption lists versioned and gated. |

## SECTION H — OPERATIONS & CULTURE (15/16)

| # | Item | ⛔ | Score | Evidence / Notes |
|---|---|---|---|---|
| H1 | Monitoring incl. safety-function health | | 2 | The protections themselves are health-checked (alarm drills); instrument self-descriptions are audited for staleness (axioms.sh comment rule). |
| H2 | Tiered, actionable alerting | | 2 | Quarantine → review-item → gate graduation (norm 16) is severity tiering; "cry-wolf is the worse failure" explicitly managed. |
| H3 | Near-misses recorded | | 2 | Near-misses absorbed permanently into the capstone (the two count-placeholder episodes); "where we got lucky" treated as data. |
| H4 | Named accountable owner with halt authority | | 1 | Adjudication is distributed (builder/third body/Kelly); the *ending* was decided by asking, which is halt authority exercised — but no single named owner exists. |
| H5 | Concern-raising channel | | 2 | QUESTIONS blocks each round; "corrections loudest first, including corrections to oneself"; dissent adjudicated on receipts. |
| H6 | Schedule never overrides safety | | 2 | The round-6 "buy mathematics, not instruments" tradeoff was made *explicitly, in writing, with the risk named* — exactly how SCEP says pressure must be handled. The project ended deliberately rather than decaying. |
| H7 | Safety case maintained | | 2 | PROOFS.md + VERIFY.md constitute a structured, evidence-backed, reproducible argument — with the boundary of the argument stated inside the argument. |
| H8 | Periodic re-assessment | | 2 | Every round re-ran the full gauntlet; the terminal round restored silently-dropped gap rows. |

## SECTION I — CRASH/ERROR PROTOCOL (25/26)

| # | Item | ⛔ | Score | Evidence / Notes |
|---|---|---|---|---|
| I1 | Crash behavior designed in advance | ⛔ | 1 | The round-3 crash was *not* pre-planned-for: the predecessor crashed twice on the same approach (raised budgets, retried). Everything after is exemplary — but CEP Part I asks for preparedness *before* the first crash. |
| I2 | Fail loud, no silent recovery | ⛔ | 2 | Silence-as-pass inverts the failure economics: anything unexpected is loud by construction. Auto-suppression impossible: exemptions must be labeled, flags reviewed. |
| I3 | Crash artifacts captured | | 2 | The predecessor's full state was in the crate; its "last recorded words" preserved; the autopsy names the exact goal, tactic, and budget decision that killed it. |
| I4 | Post-crash startup verifies integrity | | 2 | "First action, before any new mathematics: recompile all four round-2 files, confirm 0 errors, report timings — the environment-parity handshake." A designed post-crash startup mode. |
| I5 | Error taxonomy | | 2 | Eleven artifact classes + register-age dial + defect-kind taxonomy (both signs, oversell/undersell). |
| I6 | Response ownership defined | | 2 | Roles crisp: builder (charge/audit), third body (proof), Kelly (courier); handoffs briefed against the written record. |
| I7 | Runbooks exist and are drilled | | 2 | HANDOFF.md is a genuine runbook (traps in the order they will bite, guardrails, resume procedure) — and it worked: a fresh instance resumed from it alone. Alarm drills run each round. |
| I8 | Incident process followed | | 2 | Crash → autopsy → guardrails → verified resume maps to declare/preserve/stabilize/verify/close. Corrections process handles the everyday layer. |
| I9 | Evidence preserved before recovery | | 2 | Autopsy written from preserved state before the successor touched the mathematics. |
| I10 | Blameless postmortems | | 2 | Model-perfect: "human error" never a root cause; the builder indicts its *own* letter in CLOSING ("two of these trace to my own letter"); "both bodies corrected, neither diminished." |
| I11 | Action items tracked; regression test per bug | | 2 | Every correction numbered and closed; every defect class got an instrument that is verified to catch *that instance* (pointers.sh "caught this very instance on its first run"). |
| I12 | Findings feed hazard log | | 2 | Findings become REGISTER rows and norms; the loop demonstrably closes. |
| I13 | Trends reviewed; normalization of deviance countered | | 2 | Register age is a leading indicator; "a check that cannot fail is not a check" and the exemption-list audits are anti-normalization machinery; five falsifiable predictions scored. |

## SECTION J — AI-ERA EXTENSIONS (23/24)

| # | Item | ⛔ | Score | Evidence / Notes |
|---|---|---|---|---|
| J1 | Uncertainty exposed, not laundered | | 2 | Placeholder discipline (never write the count before the instrument renders it); quarantine for new instruments' findings. |
| J2 | Hallucination in hazard analysis + mitigations | ⛔ | 2 | **The corrections law IS this item**: "good prophet, bad witness" is a precise, falsifiable, five-times-confirmed hazard model of model-emitted prose, with verified mitigations (execution dates, views, resolvers). This is the strongest treatment of AI confabulation-as-failure-mode this auditor has seen in any artifact. |
| J3 | Fact/inference/generated distinguished; provenance | | 2 | VIEW blocks rendered-not-typed; quotations vs assertions distinguished by the numeral gate; SHA-256 provenance stamped into every view. "Truth tracked provenance token by token." |
| J4 | "I don't know" supported | | 2 | PARKED / BLOCKED / NOT ATTEMPTED / DECLARED BOUNDARY — ignorance is a first-class, labeled status; "nothing false built." |
| J5 | Authority matrix | ⛔ | 2 | REGISTER is exactly an authority matrix: what the machine adjudicates alone, what the audit loop (human-paced) adjudicates, what nothing adjudicates (declared). Hazardous action (shipping) human-gated via Kelly. |
| J6 | Human interrupt independent of the component | | 2 | Kelly controls the channel between bodies; the ending was *asked*, not decided ("this letter proposes an ending, and asks rather than decides"). |
| J7 | Deterministic guardrails wrap AI output | | 2 | The kernel + seven shell gates are deterministic, independently verified monitors constraining what model output can ship. The guardrail, not the model, carries the claim — the project's founding design decision. |
| J8 | Drift monitoring; models+data versioned | | 1 | Transcription drift instrumented; toolchain pinned. **Gap:** the AI participants' own model identities/versions are not recorded (which Claude builds served as builder/third body) — provenance of the *authors* is thinner than provenance of the artifacts. |
| J9 | Compositions hazard-analyzed as a system | | 2 | The builder+prover+courier composition is the object of the second result; cross-boundary failure (reason transplanted between artifact populations, H1) found and named. |
| J10 | Semantic drift across handoffs | | 2 | Named as a failure class ("every noun greps green, and the edge between them is supplied by the model"); grep-the-fact-not-the-name norm; transcription gate. |
| J11 | Counter-case maintained | | 2 | Every register row carries "what it does NOT cover"; VERIFY.md's "one honest boundary"; CLOSING's audit *overturns the project's own zero-defect claim* — the safety argument attacks itself and publishes the result. |
| J12 | Goodhart audited; assumption expiry | | 2 | Explicit: "the count never mattered; the coverage did" — the defect-count metric is rejected *because* it is gameable, replaced by register age. Stale self-descriptions in instruments treated as defects (F-1). |

---

## SCORING SUMMARY

| Section | Applicable pts | Scored | % |
|---|---|---|---|
| A Foundations | 10 | 9 | 90% |
| B Hazard Analysis | 16 | 13 | 81% |
| C Requirements | 12 | 11 | 92% |
| D Architecture | 20 | 18 | 90% |
| E Implementation | 20 | 18 | 90% |
| F V&V | 22 | 20 | 91% |
| G Config/Change | 12 | 11 | 92% |
| H Ops/Culture | 16 | 15 | 94% |
| I Crash/Error | 26 | 25 | 96% |
| J AI Extensions | 24 | 23 | 96% |
| **TOTAL** | **178** | **163** | **91.6%** |

**Gating failures (⛔ items scored 0):** **NONE.**

## VERDICT: **L4 — Safety-Critical Grade (within its epistemic domain)**

91.6% with zero gating failures. Scope caveat stated plainly: this is a closed, non-operational, mathematical artifact; the verdict means the workshop's *methodology* meets safety-critical engineering standards for its domain (preventing false claims from shipping as verified), not that it is certified for physical safety-critical deployment.

## TOP 5 HIGHEST-LEVERAGE GAPS (risk reduction per unit effort)

1. **Continuous adjudication (F7/F8/E1/D2).** Add CI (e.g. GitHub Actions) running all seven gates + the floor on every push. The project itself named its deepest limit — "the loop runs once per round rather than once per sentence." Git hosting makes closing it nearly free, and GOING-FORWARD's living-workshop layer will otherwise regress to unadjudicated commits.
2. **Pin the floor's environment (D10/F9).** `requirements.txt` with exact numpy/scipy versions + a recorded Python version. The Lean wing is pinned to the byte; the Python wing floats. One upstream numerical change could silently alter a bench.
3. **Repair the two known-defective verification scripts (CEP PM-7).** META_AUDIT's M-1 (`gf2_rank()` double-count bug — check FAILS when actually run) and M-2 (`check_rigidity.py` crashes before its last check) are documented but the defective artifacts still ship unfixed in `history/verification/`. Fix both, add the regression cases, or stamp the files themselves with a defect notice — a shipped checker that fails-when-run is exactly the artifact class the house norms exist to prevent.
4. **Pre-crash preparedness for future questions (CEP Part I / I1).** The round-3 crash protocol was written *after* two crashes of the same cause. Adopt the Crash/Error Protocol's Part I for any new question: budgets/limits declared before heavy work, max-retry rules (a second identical crash means the approach is wrong), and resume-handshake defined at charter time — turning the hard-won guardrails from archaeology into standing law.
5. **Author provenance + housekeeping (J8/governance).** Record the model identities/versions of AI participants in future charters; add a LICENSE (the repo currently has none, which leaves the record's reuse status undefined); consider adopting a severity/escalation matrix (CEP §2.1) so future incidents are classified by lookup rather than judgment.

---
*Companion narrative: FINDINGS_REPORT.md. Benchmark documents: SAFETY_CRITICAL_ENGINEERING_PROTOCOL.md, CRASH_ERROR_PROTOCOL.md, AUDIT_CHECKLIST.md.*
