# SCEP AUDIT CHECKLIST & SCORING RUBRIC
**Version 1.0 — Instrument for testing a project against SCEP v1.0 / CEP v1.0**
*Designed for auditing "the workshop" (or any project).*

---

## HOW TO USE

1. For each item, examine the project's actual artifacts (docs, code, tests, configs, history) — never accept "we intend to" as evidence.
2. Score each item:
   - **2 — CONFORMS**: evidence exists and is current
   - **1 — PARTIAL**: exists but incomplete, stale, or unverified
   - **0 — ABSENT**: no evidence
   - **N/A**: genuinely not applicable (justify in notes; N/A without justification = 0)
3. Record evidence pointer (file/line/link) and notes for every non-2 score.
4. Compute section scores and overall maturity level (below).
5. **A single 0 on any item marked ⛔ (gating) caps the overall verdict at "NOT SAFETY-CRITICAL READY" regardless of total score.**

### Maturity Levels
| % of applicable points | Level |
|---|---|
| ≥ 90% + no gating failures | **L4 — Safety-Critical Grade** |
| 70–89% + no gating failures | **L3 — Strong Foundation** (gaps are closable) |
| 40–69% | **L2 — Developing** (systematic gaps) |
| < 40% | **L1 — Ad Hoc** (safety not yet engineered) |

---

## SECTION A — FOUNDATIONS & CLASSIFICATION (SCEP §1–3)

| # | Item | ⛔ | Score | Evidence / Notes |
|---|---|---|---|---|
| A1 | Criticality of the system/components has been explicitly classified and documented | ⛔ | | |
| A2 | Classification considered worst credible consequence, incl. shared-resource inheritance | | | |
| A3 | Rigor of practices demonstrably scales with the classification | | | |
| A4 | Safe states are defined for each operational mode | ⛔ | | |
| A5 | Lifecycle gates exist (phases have entry/exit criteria, not just vibes) | | | |

## SECTION B — HAZARD ANALYSIS (SCEP §4)

| # | Item | ⛔ | Score | Evidence / Notes |
|---|---|---|---|---|
| B1 | A hazard analysis exists and predates/accompanies design | ⛔ | | |
| B2 | A living hazard log exists with the minimum schema (ID, causes, severity, mitigations, verification, residual risk, owner) | ⛔ | | |
| B3 | Appropriate techniques used for criticality (FMEA/FTA/STPA/HAZOP) | | | |
| B4 | Interaction/emergent hazards analyzed (not just component failures) — esp. software/human/AI interactions | | | |
| B5 | Mitigations follow the precedence order (design-out before warn/train) | | | |
| B6 | Every mitigation traces to requirements and verification evidence | | | |
| B7 | Residual risk formally accepted by a named authority | | | |
| B8 | Hazard analysis updated on changes (check change history) | | | |

## SECTION C — REQUIREMENTS (SCEP §5)

| # | Item | ⛔ | Score | Evidence / Notes |
|---|---|---|---|---|
| C1 | Requirements are written, atomic, uniquely identified, verifiable | | | |
| C2 | Safety requirements flagged and distinguishable | | | |
| C3 | Negative ("shall not") requirements exist for identified unsafe behaviors | | | |
| C4 | Off-nominal/failure behavior is specified, not just happy path | ⛔ | | |
| C5 | Bidirectional traceability: hazard ↔ requirement ↔ design ↔ code ↔ test | | | |
| C6 | Assumptions documented with validity conditions and monitoring | | | |
| C7 | Timing/resource limits quantified where relevant | | | |

## SECTION D — ARCHITECTURE & DESIGN (SCEP §6)

| # | Item | ⛔ | Score | Evidence / Notes |
|---|---|---|---|---|
| D1 | Fault management designed: detect → isolate → contain → recover | ⛔ | | |
| D2 | Watchdogs / health monitoring / heartbeats on critical functions | | | |
| D3 | Redundancy with independence for highest-criticality functions (or documented, accepted SPOF justification) | | | |
| D4 | Isolation/partitioning between criticality levels (or everything treated at highest level) | | | |
| D5 | Graceful degradation designed with documented shedding order | | | |
| D6 | Interfaces documented (formats, units, ranges, timing, error semantics) | | | |
| D7 | All inputs validated at trust boundaries (type, range, freshness, consistency) | ⛔ | | |
| D8 | Critical data integrity protected (checksums/validation) and corruption handled as fault | | | |
| D9 | Hazardous commands require positive confirmation (arm/fire) | | | |
| D10 | Dependencies inventoried, pinned, assessed, with failure contingencies | | | |

## SECTION E — IMPLEMENTATION (SCEP §7)

| # | Item | ⛔ | Score | Evidence / Notes |
|---|---|---|---|---|
| E1 | Written coding standard exists and is enforced by tooling (CI lint/static analysis) | | | |
| E2 | Bounded loops / no unbounded recursion on critical paths | | | |
| E3 | Memory/resource use bounded and allocation failure handled | | | |
| E4 | Functions small, single-purpose, reviewable | | | |
| E5 | Assertions/invariant checks present on critical paths; failures handled loudly | | | |
| E6 | Every return/error checked; no empty catch blocks; error paths deliberate | ⛔ | | |
| E7 | Zero-warning policy; suppressions justified in writing | | | |
| E8 | No dead/commented-out/orphan code in delivered critical builds | | | |
| E9 | No magic numbers; units explicit in names/types | | | |
| E10 | Concurrency design documented and analyzed (if concurrent) | | | |
| E11 | Safety-relevant events logged (flight recorder); logging cannot crash the system | | | |

## SECTION F — VERIFICATION & VALIDATION (SCEP §8)

| # | Item | ⛔ | Score | Evidence / Notes |
|---|---|---|---|---|
| F1 | 100% of critical code reviewed, with checklist, at required independence | | | |
| F2 | Every requirement has ≥1 test; tests trace to requirements | | | |
| F3 | Test levels present: unit, integration, system (+acceptance) | ⛔ | | |
| F4 | Structural coverage measured and gaps dispositioned | | | |
| F5 | Fault injection performed: failure handlers demonstrably tested | ⛔ | | |
| F6 | Off-nominal test effort comparable to nominal (boundary, malformed, stale, missing inputs) | | | |
| F7 | Automated regression runs on every change | | | |
| F8 | Static analysis in CI with zero unresolved critical findings | | | |
| F9 | Test environment representativeness documented ("test as you fly") | | | |
| F10 | Test evidence retained, reproducible (pinned envs, recorded seeds) | | | |
| F11 | Validation in realistic operational scenarios incl. degraded modes | | | |

## SECTION G — CONFIGURATION & CHANGE (SCEP §9)

| # | Item | ⛔ | Score | Evidence / Notes |
|---|---|---|---|---|
| G1 | Everything versioned (code, tests, configs, docs, hazard log, tools) | ⛔ | | |
| G2 | Builds reproducible; releases uniquely identified and verifiable | | | |
| G3 | Change control: safety impact assessment + review + verification per change | | | |
| G4 | Emergency change path exists with post-hoc completion deadline | | | |
| G5 | Tested rollback to last-known-good exists | ⛔ | | |
| G6 | Safety-affecting config treated as code (versioned, reviewed, validated on load, reject-don't-default) | | | |

## SECTION H — OPERATIONS & CULTURE (SCEP §10–11)

| # | Item | ⛔ | Score | Evidence / Notes |
|---|---|---|---|---|
| H1 | Monitoring covers system health AND safety-function health AND assumptions | | | |
| H2 | Tiered, actionable alerting; alert noise audited | | | |
| H3 | Anomalies/near-misses recorded and triaged (not just outages) | | | |
| H4 | Named accountable safety owner with authority to halt | | | |
| H5 | Open concern-raising channel; concerns get documented dispositions | | | |
| H6 | Evidence that schedule pressure has NOT overridden safety activities | | | |
| H7 | Safety case (structured argument + evidence) maintained for critical functions | | | |
| H8 | Periodic re-assessment of hazards/assumptions occurs | | | |

## SECTION I — CRASH/ERROR PROTOCOL CONFORMANCE (CEP)

| # | Item | ⛔ | Score | Evidence / Notes |
|---|---|---|---|---|
| I1 | Crash behavior designed in advance: safe-state transition implemented & tested | ⛔ | | |
| I2 | Fail loud: no silent failures; auto-recoveries logged and counted | ⛔ | | |
| I3 | Crash artifacts auto-captured (state, logs, versions) and survive the crash | | | |
| I4 | Post-crash startup verifies integrity; crash-looping breaks to safe mode | | | |
| I5 | Error taxonomy with severity classes exists | | | |
| I6 | Response ownership/on-call defined; escalation matrix pre-agreed | | | |
| I7 | Runbooks exist for foreseeable failure classes and are drilled | | | |
| I8 | Incident process: declare → organize (IC/ops/comms) → preserve evidence → stabilize → verify → close | | | |
| I9 | Evidence preserved before recovery; no unlogged production actions | | | |
| I10 | Blameless postmortems written for significant incidents, with template content | | | |
| I11 | Postmortem action items tracked to closure; regression test per fixed bug | | | |
| I12 | Postmortem findings fed back into hazard log | | | |
| I13 | Error/anomaly trends reviewed; normalization of deviance actively countered | | | |

## SECTION J — AI-ERA EXTENSIONS (SCEP §12) *(apply if the project involves AI/generative/autonomous components)*

| # | Item | ⛔ | Score | Evidence / Notes |
|---|---|---|---|---|
| J1 | Uncertainty/confidence exposed; uncertain outputs not treated as certain downstream | | | |
| J2 | Hallucination/confabulation in hazard analysis with verified mitigations | ⛔ | | |
| J3 | Fact vs. inference vs. assumption vs. generated content distinguished; provenance traceable | | | |
| J4 | "I don't know" is a supported, encouraged output on critical paths | | | |
| J5 | Authority matrix: autonomous vs. human-gated vs. prohibited actions defined | ⛔ | | |
| J6 | Human interrupt/override path independent of the component being overridden | | | |
| J7 | Deterministic guardrails/runtime monitors constrain AI outputs on critical paths | | | |
| J8 | Drift monitoring + revalidation triggers for learning/adaptive components; models & data versioned | | | |
| J9 | Compositions (pipelines/agent chains) hazard-analyzed as a system | | | |
| J10 | Semantic drift across handoffs addressed (end-to-end intent confirmation) | | | |
| J11 | Counter-case maintained (strongest arguments against safety, with status) | | | |
| J12 | Safety metrics audited for Goodhart effects; assumptions carry expiry/review dates | | | |

---

## SCORING SUMMARY SHEET

| Section | Applicable pts (items×2) | Scored | % |
|---|---|---|---|
| A Foundations | | | |
| B Hazard Analysis | | | |
| C Requirements | | | |
| D Architecture | | | |
| E Implementation | | | |
| F V&V | | | |
| G Config/Change | | | |
| H Ops/Culture | | | |
| I Crash/Error | | | |
| J AI Extensions | | | |
| **TOTAL** | | | |

**Gating failures (⛔ items scored 0):** _list here — any entry caps verdict at NOT READY_

**Overall maturity level:** L1 / L2 / L3 / L4

**Top 5 highest-leverage gaps (ranked by risk reduction per unit effort):**
1.
2.
3.
4.
5.

---
*AUDIT v1.0 — companion to SCEP v1.0 and CEP v1.0.*
