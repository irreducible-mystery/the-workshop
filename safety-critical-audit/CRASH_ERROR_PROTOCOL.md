# CRASH / ERROR PROTOCOL (CEP)
**Version 1.0 — Companion to the Safety-Critical Engineering Protocol (SCEP)**
*What to do when a crash, error, anomaly, or incident occurs — before, during, and after.*

---

## 0. SCOPE & PHILOSOPHY

This protocol governs response to **any unplanned deviation**: crashes, hangs, data corruption, wrong outputs, degraded performance, safety-function failures, near-misses, and "that's weird" anomalies.

**Core stances:**
1. **The system's crash behavior is designed in advance, not improvised.** (Part I)
2. **During an incident: safety first, evidence second, service third, cause fourth.** You stabilize before you diagnose; you preserve evidence before you "fix"; you never debug live on a system that can hurt someone.
3. **Every incident is tuition already paid — extract the learning.** Blameless, systemic, closed-loop. (Part III)
4. **A near-miss is a free incident.** Treat it with almost the same seriousness as the real thing.

---

# PART I — BEFORE: DESIGNED CRASH BEHAVIOR (Preparedness)

You cannot respond well to a crash you never planned for. The following must exist *before* operation.

### 1.1 Pre-Defined Failure Behavior
- **PRE-1**: For every operational mode, the **safe state** and the transition into it are defined, implemented, and tested (SCEP §6.1). The answer to "what does it do when it dies?" is written down, not discovered.
- **PRE-2**: **Fail loud**: every fault is announced (log + alert as severity demands). Silent failure and silent recovery are both prohibited — even auto-recovered faults are recorded and counted (a system auto-recovering 500 times/day is a failing system).
- **PRE-3**: Crash artifacts are captured automatically: state snapshots/dumps, logs with timestamps, recent inputs, version identifiers, and resource metrics — the "flight recorder" survives the crash it records.
- **PRE-4**: **Startup after crash is a designed mode**: on restart, the system verifies integrity (config, data, state) before resuming operation; if state is suspect, it enters safe/limited mode and says so. Crash-looping is detected and breaks to safe state (max restart attempts).
- **PRE-5**: Error taxonomy exists: every error the system can raise has a defined severity class (see §2.1), and the mapping is not left to individual developers' moods at 2 a.m.

### 1.2 Human Preparedness
- **PRE-6**: An **on-call/response ownership** model exists: for every critical system it is always knowable *who responds now* (person or rotation), with escalation contacts.
- **PRE-7**: **Runbooks** exist for foreseeable failure classes: symptoms → immediate safing actions → diagnostics → recovery steps → escalation criteria. Runbooks are versioned, tested in drills, and updated after every incident that reveals a gap.
- **PRE-8**: **Drills**: incident response (including rollback and safe-state entry) is practiced periodically on CAT-1/2 systems. An untested recovery procedure is assumed broken (same rule as untested code).
- **PRE-9**: A severity classification and escalation matrix is agreed *in advance* (§2.1), so classification during the event is a lookup, not a debate.

---

# PART II — DURING: INCIDENT RESPONSE

## 2. IMMEDIATE RESPONSE SEQUENCE

When a crash/error/anomaly is detected, execute in this order. **Do not reorder. Do not skip to diagnosis.**

### STEP 0 — SAFE (seconds to minutes)
> *Is anyone or anything at risk right now?*
- If the failure has safety consequence or unknown consequence on a critical function: **drive to safe state immediately** (per PRE-1). When in doubt, safe it. You never lose points for safing unnecessarily; you lose everything for not safing when needed.
- Do not attempt "quick fixes" on a live system in an unknown state. An unknown state is treated as an unsafe state until proven otherwise.

### STEP 1 — CLASSIFY & DECLARE (minutes)
Classify severity using the pre-agreed matrix:

| Sev | Definition | Response | Escalation |
|---|---|---|---|
| **SEV-1** | Safety impact (actual/imminent harm), or critical function down, or data integrity of critical data compromised | All-hands response, immediate | Accountable safety owner + leadership, immediately |
| **SEV-2** | Critical function degraded; safety margins reduced; major function down; near-miss on a CAT-1 hazard | Dedicated responder(s) now | Safety owner within 1 hour |
| **SEV-3** | Non-critical function down/degraded; recurring anomaly; error rates trending toward thresholds | Response within business hours | Team lead |
| **SEV-4** | Minor defect, cosmetic, single recoverable anomaly | Backlog, tracked | — |

- **Rule: classify by worst credible interpretation of current evidence; downgrade later with evidence, never upgrade too late.**
- **Declare** the incident in the tracking system: timestamp, declarer, initial severity, one-line description. Declaring "too easily" is explicitly encouraged; undeclared incidents are the dangerous ones.
- **Near-misses are declared too** (as the severity they *could* have been, flagged as near-miss).

### STEP 2 — ORGANIZE (minutes) — for SEV-1/SEV-2
Assign three distinct roles (one person may hold multiple only if resources truly don't allow otherwise — never for SEV-1):
- **Incident Commander (IC)**: owns decisions, priorities, and the big picture. Does NOT touch keyboards to debug.
- **Operations/Responders**: execute diagnostics and actions, only as coordinated by IC (no freelance changes — uncoordinated "help" during incidents causes secondary incidents).
- **Communications**: keeps stakeholders informed on a fixed cadence (e.g., SEV-1: every 30 min even if the update is "no change"), so responders aren't interrupted.

Maintain a **live incident timeline log**: every observation, action, and decision, with timestamps, as they happen. (This is both your postmortem source and your protection against memory distortion.)

### STEP 3 — PRESERVE EVIDENCE (before recovery actions where possible)
- Capture: logs, dumps, state snapshots, config as-deployed, version IDs, recent changes list, monitoring graphs.
- **Copy before you touch.** Restarting/rolling back often destroys the only evidence of cause. For SEV-1/2, evidence preservation precedes recovery unless active harm requires immediate action (Step 0 always wins).

### STEP 4 — STABILIZE / MITIGATE
Priority order: **stop the bleeding, not find the cause.**
1. **Rollback** to last-known-good (code/config/data) — the tested rollback (SCEP CM-5) is usually the fastest safe mitigation. Prefer rollback over roll-forward fixes during the incident.
2. **Isolate** the failing component; shed load; degrade gracefully per designed degradation order.
3. **Failover** to redundant capacity if available and healthy (verify the redundancy isn't failing for the same cause — common-cause check).
4. Only if none of these apply: minimal, reviewed, reversible manual intervention — logged in the timeline, second person's eyes on it before execution for SEV-1 (two-person rule for hazardous commands).

**Prohibited during incidents:**
- Unlogged actions on production systems.
- Experimental changes ("let's just try…") on SEV-1/2 systems without IC approval and reversibility.
- Debugging-in-place on a system still exposed to causing harm.
- Declaring resolution because symptoms paused without understanding *why they paused*.

### STEP 5 — VERIFY RECOVERY
- Recovery is claimed only when: critical functions verified healthy against defined checks (not just "no errors in the last 5 minutes"), data integrity verified, safety functions verified operational, and monitoring confirmed watching.
- If root cause is unknown, the system remains under **heightened watch** (elevated monitoring, restricted operation if warranted) — an unexplained recovery is an unresolved incident with the pause button pressed.

### STEP 6 — CLOSE THE RESPONSE PHASE
- IC formally ends the incident: final timeline entry, severity confirmed/adjusted, postmortem scheduled (mandatory for SEV-1/2 and any near-miss of a CAT-1 hazard; within 5 working days while memories are fresh).
- Communications sends closure notice: what happened, impact, current status, what happens next.

## 3. ESCALATION RULES
- **ESC-1**: Escalate on *time* as well as severity: if a SEV-2 isn't improving within a defined window (e.g., 2 hours), escalate as if SEV-1.
- **ESC-2**: Anyone may escalate; nobody may block escalation. Wrong escalations are cheap; missed ones are not.
- **ESC-3**: If the incident may have safety/regulatory/legal/user-harm dimensions, the accountable safety owner is informed regardless of technical severity.
- **ESC-4**: Handoffs (shift change, responder swap) require explicit briefing against the timeline log — incidents die in handoff gaps.

---

# PART III — AFTER: LEARNING & CLOSING THE LOOP

## 4. BLAMELESS POSTMORTEM

### 4.1 Rules of Conduct
- **PM-1**: **Blameless**: the analysis assumes people acted reasonably given what they knew, saw, and were incentivized to do. The question is never "who screwed up?" but "**what allowed this — and what would have caught it?**" (If your process only works when humans are perfect, your process is broken.)
- **PM-2**: "Human error" is never a root cause — it is the *starting point* of analysis: why was the erroneous action possible, plausible, or invited by the system?
- **PM-3**: Counterfactuals ("they should have…") are banned in causal analysis; only "what happened and why it made sense at the time" is admissible.
- **PM-4**: Postmortems are written, shared openly within the organization, and stored searchably. Hiding postmortems repeats incidents.

### 4.2 Required Content (Postmortem Template)
```
1. Summary: what happened, impact (duration, users/functions affected, safety relevance)
2. Severity + whether classification/escalation worked correctly
3. Timeline: detection → response → mitigation → recovery (from the live log)
4. Detection analysis: how was it detected? Should it have been detected earlier? By what?
5. Causal analysis: contributing causes (technical, process, organizational) —
   use "5 Whys" per branch, and check against SCEP hazard log:
   - Was this hazard identified in the hazard analysis? If no → hazard analysis gap.
   - If yes, why didn't the mitigations work? → mitigation/verification gap.
6. What went well / what went poorly / where we got lucky (luck = hidden risk)
7. Action items: each with owner, deadline, and verification method
8. Hazard log update: new hazards, revised likelihoods, revised mitigations
```

### 4.3 Action Item Discipline
- **PM-5**: Every SEV-1/2 postmortem SHALL produce at least one action item in each applicable layer: *detection* (find it faster), *prevention* (stop recurrence), and *response* (handle it better) — or explicitly justify why a layer needs nothing.
- **PM-6**: Action items are tracked to closure like defects; an open overdue postmortem action is a **known accepted risk** and is reviewed as such. "We wrote a postmortem" without implemented actions is theater.
- **PM-7**: A regression test SHALL be added for every code-level cause ("no bug fixed without a test that would have caught it").
- **PM-8**: Recurring incidents (same causal pattern ≥2 times) automatically escalate one severity level in postmortem treatment — recurrence means the learning loop is broken, which is itself a SEV-2 process failure.

## 5. ERROR & ANOMALY MANAGEMENT (the everyday, non-incident layer)

- **EM-1**: All errors are triaged; none are auto-ignored forever. Known-benign errors are explicitly classified as such (with rationale), not just tolerated in logs — a log full of "normal errors" is where the abnormal one hides.
- **EM-2**: Error budgets/thresholds: define acceptable rates per error class; threshold crossings are anomalies (SEV-3) even with no user impact — trends are the earliest alarm.
- **EM-3**: Every "that's weird" observation may be recorded cheaply (anomaly log, one line). Weirdness that recurs gets investigated. Most disasters announce themselves quietly first (Challenger's O-ring erosion was observed and normalized for years — **normalization of deviance is the failure mode this rule exists to stop**).
- **EM-4**: Quarterly (or per release), review the anomaly/error corpus for patterns; feed findings into hazard analysis (SCEP §4) and monitoring improvements.

---

# APPENDIX A — INCIDENT QUICK CARD (print this)

```
┌──────────────────────────────────────────────────────────┐
│ 0. SAFE      Anyone/anything at risk? → safe state NOW.  │
│              Unknown state = unsafe state.               │
│ 1. DECLARE   Classify severity (worst credible). Log it. │
│ 2. ORGANIZE  IC / Responders / Comms. Start timeline.    │
│ 3. PRESERVE  Copy evidence BEFORE touching anything.     │
│ 4. STABILIZE Rollback > isolate > failover > manual.     │
│              No freelancing. No unlogged actions.        │
│ 5. VERIFY    Health checks pass + safety functions live. │
│              Unexplained recovery ≠ resolved.            │
│ 6. CLOSE     End formally. Postmortem ≤ 5 days.          │
│                                                          │
│ ALWAYS: escalate early · log everything · blameless      │
│ NEVER:  debug live on a hazardous system · fix quietly   │
└──────────────────────────────────────────────────────────┘
```

# APPENDIX B — SEVERITY CHEAT SHEET

- Could this harm someone, or is a critical function dead, or is critical data corrupt? → **SEV-1**
- Are safety margins reduced, a critical function limping, or did we *almost* have a SEV-1? → **SEV-2**
- Is something non-critical broken or an error trend crossing thresholds? → **SEV-3**
- Is it minor and recoverable? → **SEV-4**
- Not sure between two? → **the higher one.**

---
*CEP v1.0 — companion to SCEP v1.0. See also AUDIT_CHECKLIST.md.*
