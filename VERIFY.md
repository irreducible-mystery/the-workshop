# VERIFY — reproducing the verification from scratch, trusting nothing

This repository makes an unusual promise: **six Lean files, zero imports, checked
by a bare kernel**, plus a floor of self-verifying Python benches. Nothing here
asks you to trust a number printed in prose. Every load-bearing claim is
re-derivable on your own machine from the toolchain up. This file tells you how.

The final census — fixed, and what a clean reproduction returns — is:

> **1,150 theorems · 503 axiom-free · 0 `sorryAx` · 0 `Classical.choice` ·
> six files · zero imports.**

Per file: `Interchange` 21, `MagicSquare` 85, `Anyon` 714, `Exchangeable` 41,
`Rigidity` 214, `Verlinde` 75.

If your reproduction disagrees with any of these, the reproduction is the
authority and something is wrong — that is the whole point of the exercise. The
prose in `PROOFS.md`, `CLOSING.md`, and `REGISTER.md` is *pointed at* the
instruments below; the instruments are what verify.

---

## 0. What you need

- **A POSIX shell with `sha256sum`.** The audit instruments are `/bin/sh`
  scripts using `sha256sum`, `awk`, `sed`, `grep`, and `/tmp`. On Linux/macOS
  this is native. On Windows the project's own runs used **git-bash / MSYS2**
  (the compile transcript records `MINGW64_NT-10.0-26200`); PowerShell and
  `cmd.exe` will not run these scripts.
- **`elan`** (the Lean toolchain manager) — see §1. **No `lake`, no `mathlib`,
  no `Std`.** That is deliberate: the entire claim is that a *bare* kernel checks
  every file. There is no `lakefile`, no `lake-manifest.json`, and no build
  graph to resolve.
- **For the floor only:** Python 3 with **numpy** and **scipy**.

All commands below are run **from the repository root** unless stated otherwise.

### Verify your checkout first

Before trusting anything, confirm your copy of the six sources is byte-identical
to the one the census describes. These SHA-256 prefixes are stamped into the
compile transcript's own output (`audit/transcript-round8.txt`, and the
`transcript` VIEW block in `PROOFS.md`):

```
sha256sum Interchange.lean MagicSquare.lean Anyon.lean \
          Exchangeable.lean Rigidity.lean Verlinde.lean lean-toolchain
```

Expected prefixes:

| file | sha256 (first 24) |
|---|---|
| `Interchange.lean` | `81feebe2b00b5162d17b07fb` |
| `MagicSquare.lean` | `7960b8020bb68fa4ba0ca831` |
| `Anyon.lean` | `bf08795ba09c66f486e7dcdf` |
| `Exchangeable.lean` | `c7d845b5e14e4d2afcceb35c` |
| `Rigidity.lean` | `89f65cc6559f472278dd3886` |
| `Verlinde.lean` | `cf04711c97f7155ffca78f62` |
| `lean-toolchain` | `cc346fd7850a83fb7af3902d` |

The source hashes are platform-independent and **must** match. (The `.olean`
hashes and wall-times in the transcript are *not* cross-platform invariants —
see §2.)

---

## 1. The toolchain — `elan` + Lean **4.32.0**, and nothing else

`lean-toolchain` pins exactly:

```
leanprover/lean4:v4.32.0
```

Install `elan` (from the `leanprover/elan` project). Once installed, the first
invocation of `lean` inside this directory reads `lean-toolchain` and fetches
**precisely** `leanprover/lean4:v4.32.0` — you do not choose a version, the file
does. Confirm:

```
lean --version
# Lean (version 4.32.0, ..., Release)
```

There is nothing else to install. Do **not** run `lake build`; there is no lake
project. Each `.lean` file is checked directly by `lean`.

---

## 2. Compile each of the six files

Because every file has **zero imports**, the six are mutually independent: no
order is required, and each stands entirely on the kernel and `Int`. Compile
them one at a time:

```
lean Interchange.lean   ; echo "exit=$?"
lean MagicSquare.lean   ; echo "exit=$?"
lean Anyon.lean         ; echo "exit=$?"
lean Exchangeable.lean  ; echo "exit=$?"
lean Rigidity.lean      ; echo "exit=$?"
lean Verlinde.lean      ; echo "exit=$?"
```

**The pass condition (house norm 10): exit 0 AND zero bytes of output.** A
warning is a failure. Silence, not speed, is the standard — a file that compiles
but prints anything has not passed. If you want to capture output to be sure it
is empty:

```
lean Anyon.lean > out.txt 2>&1 ; echo "exit=$? bytes=$(wc -c < out.txt)"
# expect: exit=0 bytes=0
```

Indicative wall-times from the reference run (Windows, v4.32.0) — **not
load-bearing**, given only so you are not surprised by the long ones:

| file | ~time | .olean size |
|---|---|---|
| `Interchange.lean` | "2–7 s" | "305 KB" |
| `MagicSquare.lean` | "55–110 s" | "14.8 MB" |
| `Anyon.lean` | "100–165 s" | "14.1 MB" |
| `Exchangeable.lean` | "13–19 s" | "828 KB" |
| `Rigidity.lean` | "120–155 s" | "5.0 MB" |
| `Verlinde.lean` | 6–14 s | 2.8 MB |

Expect roughly five to seven minutes total. The reference `.olean` SHA-256s are
recorded in the transcript for *byte-for-byte comparison across identical
toolchain+platform*, but `.olean` bytes can legitimately differ across OS/arch
and Lean patch builds — so do **not** treat a differing `.olean` hash as a
failure. The cross-machine invariants are: **exit 0, zero bytes, the source
hashes above, and the axiom census in §3.2.**

---

## 3. The audit instruments

Each script prints a report and, critically, **returns an exit code** — an alarm
that a script (not just a human) can read. Run each from the repository root.
The `-round8` text files under `audit/` are the reference outputs captured on the
terminal round; several instruments compare against them.

### 3.1 `transcript.sh` — the compile receipt

```
sh audit/transcript.sh ; echo "exit=$?"
```

Compiles all six files from scratch, records the toolchain identity, hashes each
source and each produced `.olean`, and runs a hygiene sweep. **Proves:** every
deliverable compiles silent (exit 0, zero bytes), an `.olean` is actually
produced (a compile that emits no kernel output is *not* a pass), and no file
contains a top-level `axiom` or `import`. Ends `RESULT: ... PASS.` and exits 0.
Compare its source-hash stanza and theorem counts against
`audit/transcript-round8.txt`; the source hashes and the `TOTAL 1150` line must
match (times and `.olean` hashes are yours).

### 3.2 `axioms.sh` — the axiom census (the authoritative gap check)

```
sh audit/axioms.sh ; echo "exit=$?"
```

Appends one `#print axioms <fully-qualified-name>` per theorem to a copy of each
file and tallies the kernel's report. **This — not `grep` for `sorry` — is the
authoritative check that nothing is unproved:** a `sorry` anywhere in a proof
term surfaces as `sorryAx` here and cannot be hidden by a comment. Expect:

```
TOTAL              1150   503 axiom-free   647 rest
sorryAx            0   (must be 0)
Classical.choice   0   (must be 0)
```

`RESULT: census complete, hygiene clean. PASS.`, exit 0. (The "rest" carry only
`propext` and/or `Quot.sound` — the census header explains this is a
statement-included over-approximation of logical dependence, not a defect.)

### 3.3 `pointers.sh` — does every name in the prose exist?

```
sh audit/pointers.sh ; echo "exit=$?"
```

Every backticked identifier in `PROOFS.md`, `HANDOFF.md`, and `REGISTER.md` must
resolve to a real Lean declaration, a file in the crate, or a VIEW block.
**Proves:** no phantom names — no citation of a theorem that was never written.
**Does not prove** the pointer points at the *right* thing (that is class 7; see
§5). Exits 0 when all resolve.

### 3.4 `views.sh check` — the ledger cannot silently drift

```
sh audit/views.sh check ; echo "exit=$?"
```

The count/hash/date blocks in `PROOFS.md` are *rendered* from instrument output,
never typed. This diffs each `VIEW:` block against the reference round-8
instrument outputs and confirms those outputs stamp the SHA-256 of the sources
now in the tree. **Proves:** the ledger's numbers are a faithful, non-stale
rendering of *these* sources — closing both "a view of the wrong thing" and
"silent staleness." Exits 0 on match. (`sh audit/views.sh render` is the
regenerator; you do not need it to verify.)

### 3.5 `transcription.sh` — the copied rings really are the same rings

```
sh audit/transcription.sh ; echo "exit=$?"
```

`Rigidity.lean` and `Verlinde.lean` **copy** the pentagon machinery and ring
cores from `Anyon.lean` (the zero-imports rule forbids sharing via `import`).
This compares the copied definitions byte-for-byte against their originals,
modulo a short list of declared-and-justified exceptions. **Proves:** the
copying files' theorems are about the *same* pentagon/ring — guarding the
project's worst failure shape (fully kernel-checked, entirely sound, and about
the wrong object). Exits 0 when every copy matches. It explicitly does *not*
verify that the declared exceptions preserve meaning, nor that `pentOK` and
`pentagonCheck` agree across files — a declared boundary (see the gap table).

### 3.6 `numerals.sh` — every asserted number is sourced (the graduated gate)

```
sh audit/numerals.sh ; echo "exit=$?"
```

Every bare-asserted multi-digit number in the ledger prose must match an
instrument output or a labeled exemption; numbers inside code, VIEW blocks, or
`"quotation marks"` are allowed. Graduated from quarantine to a **gate** in the
final round. **Proves:** no fresh count was typed into prose without an
instrument behind it. Exits 0 when every bare number is sourced or labeled.

*(There is also `audit/ship.sh <round>`, which builds and re-reads the outgoing
crate; it is the packaging check, not part of verifying the mathematics, and is
not needed to reproduce the results.)*

---

## 4. The floor — the self-verifying physics benches

The Lean wing formalizes what a floor of Python benches first computed. To run
the floor:

```
cd floor
python run_all.py        # or python3 run_all.py
```

Requires **numpy + scipy**; total runtime ≈ 45 s (the cast-factorization search
dominates). It imports and runs the benches, each of which states a claim,
checks it by machine, and fails loudly otherwise, then writes **`WELD_REPORT.txt`**.
The builder's closing audit reports **29 of 29 pass**.

The bench that most directly meets the Lean side is `floor/sheaf_cohomology.py`:
it independently computes `rank M = 5`, `rank [M|b] = 6`, `coker(M) ≅ Z₂`, and
the all-ones witnessing cocycle — the same facts `MagicSquare.lean` §6½ closes as
kernel-checked theorems (`imageCount_eq_32`, `image_iff_even`, `toZ2_hom`,
`coker_two_classes`). Two independent computations, one answer.

---

## 5. What each check proves — and the one honest boundary

The instruments form a chain, each closing the register the previous one's
defects would flee to:

> **kernel → axioms → transcript → crate → views → pointers → transcription →
> numerals**

Read as a trust ladder:

1. **The kernel** (`lean FILE.lean`) adjudicates whether each theorem *statement*
   is inhabited — the deepest check, and the one with an execution date.
2. **`axioms.sh`** adjudicates proof-term hygiene: `0 sorryAx`, `0
   Classical.choice`. No gap is hidden.
3. **`transcript.sh`** adjudicates the compile claims: silent, `.olean`
   produced, sources stamped.
4. **`views.sh` / `pointers.sh` / `transcription.sh` / `numerals.sh`** adjudicate
   the *prose about* the mathematics: its numbers are rendered not typed, its
   names all exist, its copied definitions have not drifted, its counts are
   sourced.

**The honest boundary.** One register has **no script**: class 7 — *binding and
characterization* prose, i.e. whether a correctly-named, correctly-numbered
sentence actually *describes* what it points at. `REGISTER.md` names this the
declared frontier, and `CLOSING.md`'s final outside audit is candid that the
terminal round shipped several class-7 characterization slips that every gate
passed *by design* (they have no execution date; the gates check names and
numbers, not the edge a human sentence draws between them). So: passing all six
instruments does **not** mean the prose is flawless — it means every claim a
machine *can* adjudicate has been adjudicated and holds. The mathematics is
"never wrong where a kernel could reach," which is where this project put
everything it cared about. Read `PROOFS.md`, `CLOSING.md`, and `REGISTER.md` for
the full account of that boundary.

### Optional: don't trust an alarm you haven't seen fire

The house method (norms 8, 16) for trusting an instrument is to make it fail on
purpose. If you want that assurance yourself: plant a `sorry` in a scratch copy
of a source and confirm `axioms.sh` exits 1; change two characters in a copied
`Fs` definition in `Rigidity.lean` and confirm `transcription.sh` reports
`DRIFTED` and exits 1; add a bare unsourced number to the prose and confirm
`numerals.sh` exits 1. An alarm you cannot make fire is not an alarm.

---

## Reproduction checklist

- [ ] `sha256sum` on the six sources + `lean-toolchain` matches §0.
- [ ] `lean --version` reports 4.32.0.
- [ ] All six files compile: exit 0 **and** zero bytes each.
- [ ] `sh audit/transcript.sh` → PASS (exit 0); `TOTAL 1150`.
- [ ] `sh audit/axioms.sh` → PASS; 1150 theorems, 503 axiom-free, 0 `sorryAx`, 0
      `Classical.choice`.
- [ ] `sh audit/pointers.sh` → PASS.
- [ ] `sh audit/views.sh check` → PASS.
- [ ] `sh audit/transcription.sh` → PASS.
- [ ] `sh audit/numerals.sh` → PASS.
- [ ] `cd floor && python run_all.py` → 29/29, `WELD_REPORT.txt` written.

If all boxes are checked, you have re-derived the project's central claims from
the toolchain up, trusting nothing but your own kernel and interpreter.
