# Verification Plan — Lean Repository QA

## Phase 1: Reconnaissance

-   [x]  Read README, PROOFS.md, VERIFY.md, REGISTER.md, CLOSING.md, HANDOFF.md
-   [x]  Read all current Lean source files (Anyon, Exchangeable, Interchange, MagicSquare, Rigidity, Verlinde)
-   [x]  Understand claimed theorems and their informal meaning

## Phase 2: Theorem statements & hypotheses

-   [x]  Check each theorem statement matches its prose claim
-   [x]  Check for vacuous hypotheses / trivial truths / anti-vacuity
-   [x]  Check definitions encode intended mathematical objects

## Phase 3: Dependency & circularity

-   [x]  Map imports and dependency structure between files (zero imports verified)
-   [x]  Check for circular arguments (Verlinde "closes the circle" assessed — not circular)

## Phase 4: Axioms & assumptions

-   [x]  Search for sorry, admit, axiom, unsafe, native\_decide, partial
-   [x]  Check axiom audit transcripts vs actual code
-   [x]  Verify claimed axiom footprint (propext, Quot.sound only; 0 sorryAx, 0 Classical.choice)

## Phase 5: Computational checks

-   [x]  Compile all six files under Lean 4.32.0 (exit 0, zero bytes)
-   [x]  Run floor scripts (29/29 PASS) and all audit scripts (all PASS)
-   [x]  Independently recompute key numerical claims (all reconfirmed)

## Phase 6: Prose ↔ formal correspondence

-   [x]  Compare PROOFS.md claims to Lean statements one by one
-   [x]  Check ROUND\*.md / CLOSING.md claims vs code (CLOSING's four class-7 slips verified real)
-   [x]  Check archive rounds for known past defects and whether fixed

## Phase 7: Reproducibility

-   [x]  Reproduce benchmark/audit results (census matches exactly; hashes match)
-   [x]  Fire the alarms on purpose (transcription DRIFTED test, numerals gate test, planted sorry)

## Phase 8: Report

-   [x]  Compile findings into verification report with evidence
-   [x]  Deliver report