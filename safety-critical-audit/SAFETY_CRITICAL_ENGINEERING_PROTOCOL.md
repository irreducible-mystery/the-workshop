# SAFETY-CRITICAL ENGINEERING PROTOCOL (SCEP)
**Version 1.0 — Benchmark Edition**
*A comprehensive protocol synthesized from NASA, aviation, industrial, automotive, medical, and rail safety standards, extended with modern practices for AI-era and human-AI collaborative systems.*

---

## PURPOSE OF THIS DOCUMENT

This protocol serves as a **benchmark and comparison instrument**. It defines what a system, codebase, or engineering practice must demonstrate to be considered safety-critical grade. It is designed to be used as a test: hold any project against this document, section by section, and identify where the project conforms, partially conforms, or does not conform.

**Sources synthesized:**
- NASA NPR 7150.2 (Software Engineering Requirements) & NASA-STD-8739.8 (Software Assurance)
- NASA/JPL "Power of 10" Rules & JPL Institutional Coding Standard
- RTCA DO-178C / EUROCAE ED-12C (Airborne Software), ARP4754A, ARP4761
- IEC 61508 (Functional Safety of E/E/PE Systems)
- ISO 26262 (Automotive Functional Safety)
- IEC 62304 (Medical Device Software)
- EN 50128 (Railway Software)
- MISRA C Guidelines
- MIL-STD-882E (System Safety)
- Google SRE practices (incident management, postmortems)
- Extensions original to this protocol (Section 12) covering AI systems, human-AI collaboration, and epistemic safety

---

# PART I — FOUNDATIONS

## 1. CORE PRINCIPLES OF SAFETY-CRITICAL ENGINEERING

These ten principles underlie every requirement in this protocol. A system that violates a principle cannot compensate with process paperwork.

### P1. Safety Is a System Property, Not a Component Property
Safety emerges from the interaction of components, humans, procedures, and environment. You cannot make a system safe by making each part "safe" in isolation (per Leveson/STAMP). Analysis must include interfaces, interactions, emergent behavior, and human factors.

### P2. Assume Failure — Design for It
Every component *will* fail. Every input *will* eventually be malformed. Every assumption *will* eventually be violated. Safety-critical design treats failure as a certainty to be managed, not a possibility to be hoped against.

### P3. Fail Safe, Fail Loud, Fail Known
When failure occurs, the system must transition to a **known safe state**, must **announce** the failure (never mask it), and its post-failure state must be **predictable and documented in advance**. Silent failure is the cardinal sin of safety-critical engineering.

### P4. Defense in Depth
No single barrier is trusted. Multiple independent layers (prevention → detection → containment → recovery → mitigation) must each be capable of stopping or limiting a hazard even if all preceding layers fail.

### P5. Simplicity Is a Safety Feature
Complexity is the enemy of verifiability. Every feature, abstraction, dependency, and line of code must justify its existence. If you cannot fully analyze it, you cannot certify it. Prefer the boring, obvious solution.

### P6. Traceability End-to-End
Every requirement traces to a hazard or need; every design element traces to a requirement; every line of code traces to a design element; every test traces to code and requirement. Orphan code (code tracing to nothing) is prohibited — it is unverifiable by definition.

### P7. Verification Is Not Optional and Not Once
Everything is verified, by someone/something other than its author where criticality demands, at multiple stages, with independence proportional to risk. "It works on my machine" has zero evidentiary value.

### P8. Humans Are Part of the System
Operator error is a symptom of system design, not a root cause. Interfaces, procedures, alerts, and documentation must be engineered for real humans under stress, fatigue, and time pressure.

### P9. Safety Culture Over Safety Paperwork
Documents don't make systems safe; behaviors do. Anyone can raise a safety concern; raising one is rewarded, never punished; schedule pressure never overrides a safety objection ("No launch fever"). Dissent is a resource.

### P10. The System Is Never "Done" Being Safe
Safety is maintained, not achieved. Operational monitoring, incident learning, periodic re-analysis, and change control continue for the entire lifecycle, including decommissioning.

---

## 2. CRITICALITY CLASSIFICATION (RISK-BASED TAILORING)

All established standards scale rigor to risk. Before applying this protocol, classify each system/component. Effort, independence, and evidence requirements scale with class.

### 2.1 Unified Criticality Levels (mapped to established standards)

| SCEP Level | Consequence of Failure | DO-178C | IEC 61508 | ISO 26262 | IEC 62304 | NASA (8739.8) |
|---|---|---|---|---|---|---|
| **CAT-1 Catastrophic** | Death, loss of vehicle/mission, irreversible large-scale harm | DAL A | SIL 4 | ASIL D | Class C | Class A (human-rated) |
| **CAT-2 Hazardous/Severe** | Serious injury, major mission degradation | DAL B | SIL 3 | ASIL C | Class C | Class A/B |
| **CAT-3 Major** | Minor injury, significant functional loss, major rework | DAL C | SIL 2 | ASIL B | Class B | Class B/C |
| **CAT-4 Minor** | Inconvenience, recoverable degradation | DAL D | SIL 1 | ASIL A | Class A | Class C/D |
| **CAT-5 Negligible** | No safety effect | DAL E | — | QM | Class A | Class D/E |

### 2.2 Classification Rules
1. Classify by **worst credible consequence**, not most likely.
2. A component inherits the criticality of the most critical function it can affect (including through shared resources — memory, CPU, network, data files).
3. **Partitioning/isolation** may reduce inherited criticality ONLY if isolation is itself verified to the higher level.
4. Classification must be documented, justified, reviewed independently, and revisited on every architectural change.
5. When in doubt between two levels, choose the more critical.

### 2.3 Rigor Scaling Table

| Activity | CAT-1 | CAT-2 | CAT-3 | CAT-4 |
|---|---|---|---|---|
| Independent verification | Required (fully independent team) | Required (independent persons) | Peer review | Self + peer check |
| Structural coverage | MC/DC + statement + branch | Branch + statement | Statement | Recommended |
| Formal methods | Recommended for core logic | Optional | Optional | — |
| Hazard analysis | FTA + FMEA + STPA | FTA or FMEA + STPA | FMEA | Checklist |
| Requirements traceability | Bidirectional, tool-managed, audited | Bidirectional | Forward | Informal |
| Code review coverage | 100%, two reviewers | 100%, one reviewer | 100% risk-based | Risk-based |

---

## 3. SAFETY LIFECYCLE OVERVIEW

Safety activities span the full lifecycle (per IEC 61508's 16-phase safety lifecycle, simplified):

```
CONCEPT → HAZARD ANALYSIS → SAFETY REQUIREMENTS → ARCHITECTURE →
DESIGN → IMPLEMENTATION → VERIFICATION → VALIDATION →
DEPLOYMENT → OPERATION & MONITORING → CHANGE MANAGEMENT → RETIREMENT
                     ↑__________ CONTINUOUS FEEDBACK __________|
```

**Gate rule:** No phase may begin at full pace until the prior phase's exit criteria are met and reviewed. Gates may be tailored by criticality but never skipped for CAT-1/CAT-2.

---

# PART II — ANALYSIS & REQUIREMENTS

## 4. HAZARD ANALYSIS & RISK ASSESSMENT

### 4.1 Requirements
- **HA-1**: A documented hazard analysis SHALL exist before design begins and SHALL be a living document updated with every significant change.
- **HA-2**: Hazard analysis SHALL use at least the techniques required by the criticality level (§2.3), drawn from:
  - **PHA** (Preliminary Hazard Analysis) — early, broad identification
  - **FMEA/FMECA** (Failure Modes & Effects Analysis) — bottom-up: "what happens if this part fails?"
  - **FTA** (Fault Tree Analysis) — top-down: "what combinations of events cause this hazard?"
  - **STPA** (System-Theoretic Process Analysis) — control-structure based: unsafe control actions, including software and human ones; REQUIRED for systems with significant software/human/AI interaction because FMEA/FTA under-capture interaction failures
  - **HAZOP** — guided-word deviation analysis for processes and dataflows
- **HA-3**: Each identified hazard SHALL be recorded in a **Hazard Log** with: unique ID, description, causes, worst credible effect, severity, likelihood, risk level, mitigations, verification of mitigations, residual risk, owner, status.
- **HA-4**: Every mitigation SHALL trace to one or more safety requirements (§5) and to verification evidence.
- **HA-5**: Risk acceptance SHALL follow the precedence order (MIL-STD-882E):
  1. **Eliminate** the hazard by design
  2. **Reduce** risk by design (inherent safety)
  3. **Incorporate safety devices** (interlocks, limiters)
  4. **Provide warning devices**
  5. **Procedures and training** (weakest — never the sole mitigation for CAT-1/CAT-2)
- **HA-6**: Residual risk for CAT-1 hazards SHALL be formally accepted in writing by an accountable authority — never implicitly.
- **HA-7**: Hazard analysis SHALL explicitly consider: hardware faults, software faults, data faults, timing faults, human error, environmental conditions, security-induced hazards (a security breach that can cause a safety hazard makes security safety-critical), degraded modes, maintenance activities, and interactions between "independently safe" components.

### 4.2 The Hazard Log Minimum Schema
```
HAZ-ID | Title | Description | Causal factors | Worst credible effect |
Severity (1-5) | Likelihood (A-E) | Risk (matrix) | Mitigations (→ REQ IDs) |
Verification (→ TEST IDs) | Residual risk | Accepted by | Date | Status
```

## 5. SAFETY REQUIREMENTS ENGINEERING

- **RQ-1**: Requirements SHALL be **unambiguous, verifiable, atomic, uniquely identified, and consistent**. Each must be testable — if you cannot state how you would verify it, it is not a requirement.
- **RQ-2**: Safety requirements SHALL be explicitly flagged and distinguishable from functional requirements.
- **RQ-3**: **Negative requirements** SHALL be written: what the system must NOT do (e.g., "The system SHALL NOT command actuator movement while the interlock is open"). Unsafe behaviors identified in STPA become "shall not" requirements.
- **RQ-4**: Requirements SHALL specify behavior under **all conditions**: nominal, off-nominal, boundary, degraded, and failure conditions — including required behavior when inputs are absent, late, out of range, or contradictory.
- **RQ-5**: Every requirement SHALL trace **backward** to a source (hazard, need, standard) and **forward** to design, code, and test (bidirectional traceability). Traceability SHALL be audited; broken links block release.
- **RQ-6**: **Derived requirements** (arising from design decisions, not parent requirements) SHALL be fed back into hazard analysis for safety impact assessment (per DO-178C).
- **RQ-7**: Timing, capacity, and resource requirements SHALL be quantified (worst-case execution time, maximum memory, latency budgets, throughput floors).
- **RQ-8**: Assumptions SHALL be documented as first-class artifacts, each with: statement, rationale, validity conditions, monitoring method, and consequence if violated. An unmonitored assumption on a CAT-1/2 path is a nonconformance.

---

# PART III — DESIGN & IMPLEMENTATION

## 6. ARCHITECTURE & DESIGN FOR SAFETY

### 6.1 Fault Tolerance & Safe States
- **AR-1**: For every operational mode, a **safe state** SHALL be defined, documented, and reachable from any other state. If no safe passive state exists (e.g., aircraft in flight), define minimum-risk degraded operation.
- **AR-2**: The system SHALL implement fault management: **detection → isolation → containment → recovery/safe-state transition**, each stage designed and verified explicitly.
- **AR-3**: **Redundancy** SHALL be applied per criticality: CAT-1 functions require redundancy with *independence* (no common-cause failure: diverse hardware, diverse implementations, or at minimum isolated instances). Voting/arbitration logic itself is CAT-1.
- **AR-4**: **Watchdogs and health monitoring** SHALL exist: liveness monitoring (heartbeats/watchdog timers), sanity monitoring (outputs within physical plausibility), and resource monitoring (memory, CPU, queue depths). Watchdog expiry drives transition to safe state.
- **AR-5**: **Partitioning/isolation**: mixed-criticality components sharing a platform SHALL be separated by verified isolation (memory protection, time partitioning, sandboxing). Without verified isolation, everything on the platform inherits the highest criticality present.
- **AR-6**: **Graceful degradation** SHALL be designed: prioritized shedding of non-critical functionality under resource exhaustion or partial failure, with critical functions preserved longest. Degradation order is documented and tested.

### 6.2 Interfaces & Data
- **AR-7**: Every external interface SHALL have a written Interface Control Document (ICD): format, units, ranges, timing, error semantics, and behavior on violation. Unit errors have destroyed spacecraft (Mars Climate Orbiter) — **units SHALL be explicit in every interface definition**.
- **AR-8**: **All inputs are guilty until proven innocent**: validate type, range, freshness (staleness detection), rate, and consistency at every trust boundary. Never assume upstream validation.
- **AR-9**: Critical data SHALL be protected in storage and transit (checksums/CRCs/ECC as appropriate); corruption SHALL be detected and handled as a fault, not ignored.
- **AR-10**: Commands with hazardous effect SHALL require positive multi-step confirmation (arm/fire pattern) and SHALL be rejected by default when preconditions are unverified.

### 6.3 Design Discipline
- **AR-11**: Design SHALL be documented at a level allowing an independent competent engineer to verify it against requirements without consulting the authors.
- **AR-12**: **Deterministic behavior** on critical paths: bounded loops, bounded memory, bounded execution time, no unbounded recursion, no reliance on best-effort scheduling for CAT-1/2 deadlines.
- **AR-13**: Single points of failure for CAT-1 functions SHALL be eliminated or, where physically unavoidable, formally documented, justified, and accepted at the same authority level as the residual hazard.
- **AR-14**: Dependency discipline: every third-party dependency on a critical path SHALL be inventoried, version-pinned, license-checked, assessed for assurance (treat unassessed dependencies at the criticality they can affect), and have a documented failure/compromise contingency.

## 7. IMPLEMENTATION / CODING STANDARDS

### 7.1 The Core Rules (derived from NASA/JPL Power of 10 & MISRA, generalized beyond C)

- **CS-1 Simple control flow**: No goto-equivalents, no unbounded jumps; recursion prohibited on critical paths (or provably bounded with static verification).
- **CS-2 Bounded loops**: Every loop SHALL have a statically provable upper bound. Loops intended to be infinite (schedulers) SHALL be explicitly annotated and monitored.
- **CS-3 Predictable memory**: No dynamic allocation after initialization on CAT-1/2 real-time paths; where the platform requires dynamic allocation (managed languages), allocation failure SHALL be handled and memory use bounded and monitored.
- **CS-4 Small units**: Functions SHALL be short enough to understand and verify as a unit (guideline: ~60 lines; one function, one purpose).
- **CS-5 Assertion density**: Minimum ~2 assertions per function on critical paths, checking preconditions, postconditions, and invariants. Assertions must be side-effect free. Assertion failure in operation triggers defined fault handling — never silent continuation.
- **CS-6 Minimal scope**: Declare data at the smallest possible scope. Minimize shared mutable state; where shared, protect with explicit, deadlock-analyzed synchronization.
- **CS-7 Check every return**: Every return value/error code SHALL be checked or the ignoring SHALL be explicitly annotated and justified. Every exception path SHALL be handled deliberately. Empty catch blocks are prohibited.
- **CS-8 Limit clever constructs**: Restrict metaprogramming, reflection, operator overloading, and macro magic on critical paths; code must mean what it appears to mean to a reviewer.
- **CS-9 Restrict indirection**: Limit pointer/reference indirection depth; no function pointers/dynamic dispatch on critical paths where static analysis cannot resolve targets (or provide the analysis).
- **CS-10 Zero-warning policy**: All code SHALL compile/lint clean at the most pedantic setting from day one. All warnings resolved by fixing the code, not suppressing the tool; suppressions require written justification.

### 7.2 Additional Implementation Requirements
- **CS-11**: A written, language-specific coding standard SHALL exist and be enforced by automated tooling in CI (not only human review).
- **CS-12**: **Defensive programming** at every trust boundary; **offensive programming** (assertions that crash loudly in test) inside verified boundaries — never let a fault propagate silently in either mode.
- **CS-13**: Error handling paths ARE critical paths: they SHALL be reviewed and tested with the same rigor as nominal paths (error paths are where systems die).
- **CS-14**: No dead code, no commented-out code, no orphan code on delivered critical builds. Deactivated code (present but disabled) requires documented justification and verified deactivation (DO-178C).
- **CS-15**: Magic numbers prohibited; all constants named, all units documented in names or types (`timeout_ms`, `altitude_m`).
- **CS-16**: Concurrency on critical paths requires a documented concurrency design (what locks what, in what order), race/deadlock analysis, and stress verification.
- **CS-17**: All safety-relevant events SHALL be logged with timestamps sufficient to reconstruct incident timelines (flight-recorder principle) — while logging itself must be non-blocking and unable to take down the critical function (log failure ≠ system failure).

---

# PART IV — VERIFICATION & VALIDATION

## 8. VERIFICATION & VALIDATION (V&V)

**Verification** = did we build it right (vs. requirements)? **Validation** = did we build the right thing (vs. real-world need)? Both are required; neither substitutes for the other.

### 8.1 Reviews
- **VV-1**: 100% of critical-path code SHALL be reviewed by qualified reviewer(s) per §2.3, using a written checklist covering: requirement conformance, coding standard, error handling, boundary conditions, concurrency, resource use, and safety impact.
- **VV-2**: Requirements, architecture, design, test plans, and hazard analyses SHALL each undergo documented review with recorded findings and closure.
- **VV-3**: Review independence scales with criticality; for CAT-1, the verifier SHALL NOT be the author and SHALL NOT report to the author's delivery-pressure chain.

### 8.2 Testing
- **VV-4**: Requirements-based testing: every requirement SHALL have at least one test; every test SHALL trace to requirement(s). Untraceable tests and untested requirements both block release.
- **VV-5**: Test levels required: unit → integration → system → acceptance. Plus, as applicable: fault injection, stress/load, endurance/soak, boundary/robustness (invalid, out-of-range, malformed, missing, stale inputs), timing/worst-case, and regression (full automated regression on every change).
- **VV-6**: **Structural coverage** per §2.3 (statement/branch/MC/DC). Coverage gaps SHALL be analyzed: either add tests, or justify (defensive code) in writing, or remove dead code.
- **VV-7**: **Fault injection is mandatory for CAT-1/2**: deliberately induce component failures, corrupt data, drop/delay/duplicate messages, exhaust resources, kill processes mid-transaction — and verify detection, containment, safe-state transition, and recovery behave as designed. An untested failure handler is assumed broken.
- **VV-8**: **Off-nominal emphasis**: for CAT-1/2, at least as much test effort SHALL target off-nominal/failure behavior as nominal behavior.
- **VV-9**: Test environments SHALL be representative; differences from operational environment SHALL be documented with risk assessment. "Test as you fly, fly as you test" (NASA) — deviations between tested and deployed configurations require explicit waiver.
- **VV-10**: Test results are evidence: retained, versioned, and reproducible (pinned environments, seeds recorded for randomized testing).

### 8.3 Analysis & Formal Methods
- **VV-11**: Static analysis SHALL run in CI on all code, at maximum practical strictness, with zero unresolved findings on critical paths (per CS-10).
- **VV-12**: For CAT-1: worst-case execution time analysis, worst-case memory/stack analysis, and numerical accuracy analysis (floating-point behavior) SHALL be performed where applicable.
- **VV-13**: Formal methods (model checking, proof of invariants) SHOULD be applied to CAT-1 core logic (mode logic, interlocks, voting, safe-state transitions) where feasible — these small, high-consequence kernels are exactly where proofs pay off.
- **VV-14**: Tools whose output is trusted without independent checking (code generators, verification tools) SHALL be qualified/validated for that use (DO-330 principle).

### 8.4 Validation
- **VV-15**: Validation SHALL exercise the system in realistic operational scenarios with realistic operators/users, including degraded modes and emergency procedures — before operational reliance.

---

# PART V — OPERATIONS & GOVERNANCE

## 9. CONFIGURATION MANAGEMENT & CHANGE CONTROL

- **CM-1**: Every artifact that affects the system (code, requirements, designs, tests, tools, build scripts, configs, data, docs, hazard log) SHALL be under version control. **The build SHALL be reproducible**: any released version can be exactly rebuilt from recorded sources, tools, and configuration.
- **CM-2**: Released baselines SHALL be immutable and uniquely identified; what is deployed SHALL be verifiable against the baseline (integrity check).
- **CM-3**: **No uncontrolled change**: every change to a baselined artifact goes through change control: documented reason → safety impact assessment (does this touch/affect any critical function? update hazard analysis?) → review → verification (targeted + regression) → approval by authority appropriate to criticality.
- **CM-4**: **Emergency changes are not exempt** — they use an expedited path with post-hoc completion of full analysis within a defined deadline (e.g., 72 hours), tracked to closure.
- **CM-5**: Deployment SHALL be reversible: a verified rollback to last-known-good SHALL exist and be *tested*, not assumed. Deploys of critical systems use staged rollout with health verification at each stage where the domain permits.
- **CM-6**: Environment/configuration values that affect safety behavior (limits, thresholds, feature flags, model versions) are safety-critical artifacts: version-controlled, reviewed, validated on load (reject-and-safe-state on invalid config, never "run with defaults" silently).

## 10. OPERATION, MONITORING & INCIDENT LEARNING

- **OP-1**: Operational monitoring SHALL cover: system health (liveness, resources), safety-function health (are the protections themselves working?), assumption monitors (§ RQ-8), and leading indicators (near-misses, error-rate trends, drift) — not just outages.
- **OP-2**: Alerting SHALL be tiered by severity with defined response times; alert fatigue is a safety hazard — alerts SHALL be actionable and periodically audited for noise.
- **OP-3**: Every anomaly, near-miss, and incident SHALL be recorded and triaged; incidents follow the **Crash/Error Protocol** (companion document).
- **OP-4**: **Blameless learning**: postmortems focus on systemic causes, never individual blame; findings feed back into hazard analysis, requirements, tests, and training (close the loop — an unimplemented postmortem action item is a known open risk).
- **OP-5**: Operator/user-facing procedures, alarms, and displays SHALL be designed and validated for human performance under stress (clear, prioritized, non-contradictory; critical alarms distinguishable; no "wall of red").
- **OP-6**: Periodic safety re-assessment SHALL occur (at minimum annually and after major changes): is the hazard analysis still valid? Have usage, environment, or dependencies drifted from assumptions?

## 11. SAFETY CULTURE & ORGANIZATION

- **SC-1**: A named individual SHALL be accountable for safety of each critical system, with authority to halt release/operation — and this authority SHALL be exercisable without career consequence.
- **SC-2**: Anyone SHALL be able to raise a safety concern through a defined channel; every concern receives a documented disposition. Retaliation for raising concerns is a critical organizational failure.
- **SC-3**: Schedule/cost pressure SHALL NEVER be accepted as rationale for skipping a safety activity on CAT-1/2 (the Challenger lesson: "prove it's unsafe" must never replace "prove it's safe").
- **SC-4**: Dissenting technical opinions on safety matters SHALL be documented and adjudicated on technical merit, not seniority (NASA's formal dissent process).
- **SC-5**: Competence: personnel performing safety-critical work SHALL have documented relevant competence; safety training is periodic, not one-time.
- **SC-6**: A **Safety Case** SHALL be maintained for CAT-1/2 systems: a structured, evidence-backed argument for why the system is acceptably safe for its intended use — kept current, and honest about limitations and residual risks.

---

# PART VI — EXTENSIONS BEYOND ESTABLISHED STANDARDS

## 12. SCEP ORIGINAL EXTENSIONS (for modern, AI-era, and human-AI collaborative systems)

Established standards predate large-scale AI and modern autonomous/generative systems. The following are required additions.

### 12.1 Epistemic Safety (Knowing What You Know)
- **EX-1**: Any component that produces judgments, predictions, or generated content SHALL represent and expose its **uncertainty/confidence**, and downstream consumers SHALL NOT treat uncertain outputs as certain.
- **EX-2**: **Confabulation/hallucination is a failure mode** and SHALL appear in hazard analysis for any generative/inferential component. Mitigations (grounding, verification against authoritative sources, human confirmation gates) SHALL be specified and verified.
- **EX-3**: The system SHALL distinguish, in data and in interfaces, between: measured fact, derived inference, assumption, and generated content. Provenance SHALL be traceable for safety-relevant data.
- **EX-4**: **"I don't know" is a valid and required output.** Systems SHALL be designed and rewarded (in training, metrics, and culture) to express ignorance rather than guess on critical paths.

### 12.2 Autonomy & Authority Boundaries
- **EX-5**: For any autonomous or AI-driven capability, an explicit **authority matrix** SHALL define what the automation may do alone, what requires human confirmation, and what is prohibited regardless of confidence. Hazardous actions default to human-gated until evidence justifies otherwise.
- **EX-6**: Autonomy SHALL be **interruptible**: a human SHALL be able to halt, override, or safe the system at any time, through a path that does not depend on the health of the component being overridden.
- **EX-7**: **Automation complacency** is a hazard: design SHALL keep humans meaningfully engaged for functions where human takeover is a mitigation (an operator who hasn't practiced takeover cannot perform it).
- **EX-8**: Behavioral envelope: AI/adaptive components on critical paths SHALL be wrapped in deterministic, independently verified **guardrails/runtime monitors** that constrain outputs to a verified safe envelope regardless of the model's internal behavior. The guardrail, not the model, carries the safety claim.

### 12.3 Drift, Learning & Data Safety
- **EX-9**: Any component whose behavior changes with data (learning systems, adaptive thresholds) SHALL have drift monitoring, defined retraining/revalidation triggers, and version control of models + training data as safety-critical artifacts (§CM-6).
- **EX-10**: Training/reference data SHALL be assessed for bias, coverage of off-nominal conditions, and poisoning/compromise risk where the component is on a critical path.

### 12.4 Compositional & Emergent Risk
- **EX-11**: When components are composed (pipelines, agent chains, tool-calling systems), the composition SHALL be hazard-analyzed as a system (per P1/STPA): individually-safe components can compose into unsafe behavior. Error propagation, feedback loops, and escalation-of-authority paths across the composition SHALL be explicitly analyzed.
- **EX-12**: **Semantic drift across handoffs** (meaning changing subtly as data/intent passes between components, agents, or humans) SHALL be treated as a failure mode: critical intent SHALL be confirmed end-to-end, not assumed preserved.

### 12.5 Honesty of the Safety Argument Itself
- **EX-13**: The safety case SHALL include a **counter-case**: an actively maintained list of the strongest known arguments *against* the system's safety, with status. A safety case with no counter-case is presumed incomplete.
- **EX-14**: Metrics SHALL be audited for Goodhart effects: when a safety metric becomes a target, verify it still measures safety (e.g., "zero incident reports" may mean suppressed reporting, not safety).
- **EX-15**: **Assumption expiry**: safety-relevant assumptions SHALL carry review dates; expired-unreviewed assumptions are treated as open risks, not silently trusted forever.

---

# APPENDIX A — QUICK CONFORMANCE SUMMARY (the protocol on one page)

1. Classify criticality; scale rigor to it. (§2)
2. Analyze hazards before and during design; keep a living hazard log. (§4)
3. Write verifiable requirements, including "shall nots" and failure behavior; trace everything both ways. (§5)
4. Define safe states; detect→isolate→contain→recover; redundancy & isolation per criticality; validate all inputs; document interfaces with units. (§6)
5. Code simply: bounded loops, checked returns, dense assertions, zero warnings, no dead code, tested error paths. (§7)
6. Verify with independence: reviews, requirements-based tests, coverage, fault injection, static analysis; validate in realistic conditions. (§8)
7. Control every change; reproducible builds; tested rollback; config is code. (§9)
8. Monitor safety functions and assumptions; learn blamelessly from every incident; close the loop. (§10)
9. Culture: anyone can stop the line; dissent is documented; schedule never beats safety. (§11)
10. For AI-era systems: expose uncertainty, gate authority, guardrail behavior, monitor drift, analyze compositions, and keep the safety argument honest. (§12)

---
*SCEP v1.0 — prepared as a benchmark instrument. Companion documents: CRASH_ERROR_PROTOCOL.md, AUDIT_CHECKLIST.md.*
