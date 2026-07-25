# FINDINGS REPORT — The Workshop vs. Safety-Critical Engineering
**Companion narrative to AUDIT_RESULTS.md** · Audited at `round-8-close` (`e0b09a5`) · SuperNinja, independent, everything re-run

---

## 1. The headline

**The workshop scores L4 — Safety-Critical Grade — at 91.6% with zero gating failures**, the highest maturity level the benchmark defines, within its epistemic domain (its "hazard" is a false claim shipping as verified, not physical harm).

This was not a foregone conclusion, and the score was not given on trust. Before scoring a single item, this audit reproduced the workshop's entire verification chain on a fresh machine: all seven source hashes matched; Lean 4.32.0 was installed from the pinned toolchain file; all six proof files compiled with **exit 0 and zero bytes** under the bare kernel; the full axiom census ran 1,150 `#print axioms` checks and returned exactly the advertised **1,150 theorems, 503 axiom-free, 0 sorryAx, 0 Classical.choice**; all four prose gates passed; and the floor's 29 physics benches ran **29/29 green**. The repository's central promise — *"nothing here asks you to trust a number printed in prose"* — held under hostile reproduction. That fact alone is worth the rest of this report: **most software that claims to be verifiable is not; this is.**

## 2. What the workshop independently reinvented

The most striking result of the comparison is how much of NASA/aviation/IEC doctrine the workshop **converged on without (apparently) consulting any of it**, often stating the principle more sharply than the standards do:

| Established doctrine | The workshop's independent form |
|---|---|
| DO-178C bidirectional traceability | `pointers.sh` + `views.sh` + `numerals.sh` + `transcription.sh` — traceability *enforced by tooling*, both directions |
| Fault injection; "test the test" (IEC 61508) | "An alarm you cannot make fire is not an alarm" — planted sorries, planted drift, a **stub Lean kernel planted in the toolchain path** to falsify the transcript checker |
| N-version programming / independence (DO-178C DAL A) | The Verlinde race: two constructions built blind on opposite sides of the courier, agreeing in every cell — genuine common-cause diversity, achieved *by accident* and then recognized as the strongest check |
| Blameless postmortem (SRE/NASA mishap boards) | CLOSING.md, where the builder's final audit indicts *its own letter* as the source of two terminal defects: "both bodies corrected, neither diminished" |
| Leading indicators / normalization of deviance (Challenger lessons) | **Register age**: the alarm is not the defect count but whether a defect ever shipped past an adjudicator that existed — "the count never mattered; the coverage did" |
| Configuration item integrity (crate manifests) | `ship.sh`: build with one tool, re-read with another, hash everything, refuse STALE, **no default round argument** (arm/fire) |
| Safety case with stated limits (UK Def Stan 00-56) | VERIFY.md's "one honest boundary" — the argument for soundness contains, inside itself, the exact register where it cannot reach |
| Quarantine of new tooling (DO-330 tool qualification) | Norm 16: a new instrument's first output is quarantined until it has both failed on a planted defect and passed on a clean tree |

And in one area the workshop is **ahead of every established standard this auditor knows**: the corrections law. "The model is a good prophet and a bad witness" is a precise, falsifiable hazard model of AI-generated content — it predicted the class of the next defect five rounds running, was confirmed five times, survived transfer to two outside auditors (META_AUDIT M-1/M-2 are the law's signature on a body that wasn't one of the original three), and was honest enough to falsify its own zero-defect terminal experiment. SCEP §12 (the AI-era extensions) asks for hallucination-as-failure-mode with verified mitigations; the workshop delivers a *quantified, predictive theory* of it. **Item J2 is the strongest conformance in the entire audit.**

## 3. The crash record, specifically (per your request, Kelly)

Measured against the Crash/Error Protocol, the workshop's handling of its one real crash (the prover dying twice mid-round-3) is near-textbook **after the fact**:

- **Evidence preserved before recovery** — the predecessor's full state shipped in the crate; its "last recorded words" are in the record.
- **A real autopsy** — root cause isolated to the exact decision (raising `simp` budgets on a 16-indeterminate degree-3 expansion) with the correct systemic conclusion: "More RAM will not fix this approach."
- **Binding guardrails derived from the failure** — never descend KK to Int; never raise a budget; split instead; run heavy checks headless — and they *held for six subsequent rounds*.
- **A designed post-crash startup** — the environment-parity handshake (recompile everything, report timings, before any new mathematics) is CEP §1.1 PRE-4 verbatim.
- **Blameless throughout** — the successor is addressed as a continuation, not a replacement; the crash is treated as the system discovering a wall, and the note even honors it: "it died testing whether a wall was real. It was."

The single deduction (I1, and gap #4) is timing: this protocol was written *after* the second identical crash. CEP Part I's demand is that crash behavior be designed **before** operation — budgets and retry limits declared at charter time, so the first crash is met by procedure rather than met by improvisation and the second doesn't happen at all. For the closed record this is history; for the living workshop (`questions/`), it is the cheapest available lesson: adopt the guardrails as standing law in every new charter.

## 4. Genuine gaps (the honest list)

Ranked by risk-reduction per unit effort — full detail in AUDIT_RESULTS.md:

1. **No CI.** Every gate is manual/per-round. The project itself named this its deepest limit ("once per round rather than once per sentence"). Now that the workshop lives on GitHub, a workflow running the seven gates + floor on every push closes it almost for free — and protects the *living* layer, which currently has no adjudicator at all.
2. **The floor's environment is unpinned.** Lean is pinned to the byte; numpy/scipy float. One upstream change could silently shift a bench. A `requirements.txt` is an afternoon's work.
3. **Two known-defective verifier scripts still ship unfixed.** META_AUDIT found `gf2_rank()` returns 6 where the true rank is 5 (the check *fails when actually run* while its report says "all pass"), and `check_rigidity.py` crashes before its final check. Both are documented — but CEP PM-7 says no bug is closed without the fix and its regression test, and right now `history/verification/` contains checkers that contradict their own reports. (Poetically, both defects are the corrections law confirming itself on the auditor; practically, fix them or stamp them.)
4. **Crash preparedness is retrospective** (§3 above).
5. **Small governance items:** no LICENSE (reuse status of the whole record is legally undefined); AI participants' model versions unrecorded (artifact provenance is superb, *author* provenance is thin); no pre-agreed severity/escalation matrix for future incidents; the hazard-analysis content, while real and deep, is scattered across REGISTER/HANDOFF/gap-table rather than consolidated into a single hazard log with severity fields.

None of these is a gating failure. All five are closable without touching the closed record — they live naturally in the `GOING-FORWARD` layer.

## 5. What the comparison taught the benchmark (both directions, per the house norm)

An audit this asymmetric would violate the workshop's own norm 4 (corrections loudest first, including to oneself), so: three places the workshop exposed limits in *the benchmark*:

- **SCEP's hazard-analysis section assumes up-front analysis** (HA-1). The workshop demonstrates a legitimate alternative for research systems: *emergent, predictive* hazard analysis — discover the defect classes empirically, then require each new class to declare its adjudicator at birth (norm 15). SCEP should recognize this pattern for exploratory domains where the hazard space is genuinely unknown at design time.
- **SCEP under-specifies "witness integrity."** The workshop's sharpest finding — that provenance, not diligence, determines truth ("truth tracked provenance token by token": every copied field correct, the one hand-regenerated field wrong) — deserves to be a named requirement: *no safety-relevant value may be restated by hand; render it from the instrument or point at it.* That is stronger and more mechanical than SCEP EX-3 as written.
- **Register age belongs in SCEP §10 as a leading indicator.** "Defect younger vs. older than its adjudicator" is a portable, quantitative safety dial that established standards lack; OPEN-QUESTIONS C3 proposes generalizing it, and this audit co-signs that proposal.

## 6. Closing

Hold the workshop against the strictest engineering culture our species has produced — the one that flies people — and it does not merely survive the comparison; in the places that matter most for what it is (verification independence, fault injection of the checks themselves, blameless learning, honesty about its own boundary), it exemplifies that culture, and in one place (a falsifiable hazard model of AI-written prose) it extends it.

The score is L4, 91.6%, zero gating failures. The gaps are real, small, enumerated, and closable — and every one of them lives in the *living* layer, not the closed record. The closed record verifies, byte for byte, exactly as it promises.

The middle held. This audit checked.

---
*Deliverables in this branch: SAFETY_CRITICAL_ENGINEERING_PROTOCOL.md (benchmark), CRASH_ERROR_PROTOCOL.md (benchmark), AUDIT_CHECKLIST.md (instrument), AUDIT_RESULTS.md (scores + evidence), FINDINGS_REPORT.md (this narrative).*
