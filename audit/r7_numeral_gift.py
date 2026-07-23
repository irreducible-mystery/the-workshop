#!/usr/bin/env python3
# ---------------------------------------------------------------------------
# r7_numeral_gift.py -- THE NUMERAL GIFT (seat -> builder, round 6 for round 7).
#
# THE RULE (as proposed on the builder's side, built here):
#   every digit-string in the ledger must either trace to an instrument
#   output (verbatim token match after normalization) or be FLAGGED FOR
#   REVIEW.  A flag is not a verdict; it is a numeral whose provenance is
#   the author rather than an execution date -- F4's whole species.
#
# ADJUDICATOR DECLARATION (norm 15):
#   WHAT THIS CHECKS: token-level provenance of numerals in ledger prose.
#   WHAT IT DOES NOT CHECK:
#     - DERIVED numbers (17m20s is the difference of two output tokens; the
#       rule sees 17 and 20, not the subtraction).  F4's arithmetic itself
#       is exactly here: this instrument would have flagged the 12 only
#       because 12 appeared in no output, not because 17:20 was the truth.
#     - NUMBER-WORDS ("twelve minutes", "nine artifact classes") -- invisible
#       to any digit scanner.  The round-6 nine-vs-ten register miscount is
#       this class.  A word-numeral extension is possible and not built.
#     - SINGLE DIGITS (exempt class X3): "rank 3", "five files", "exit 0".
#     - ACCIDENTAL PROVENANCE: a wrong numeral that collides with an
#       unrelated output token (a line number, a month field) matches and
#       is NOT flagged.  In the round-6 corpus the F4 tokens 07 and 12 both
#       have such collisions; in the round-5 corpus 12 does not.  The noise
#       floor is permissive, not strict.
#     - anything in an instrument's own comments, HANDOFF, or the letters:
#       the scan surface is the LEDGER (where counts congregate).
#
# DESIGN DECISIONS (reported, not buried):
#   scanned : integers >= 2 digits, decimals (134.8), comma-formatted
#             (2,610 == 2610), timestamp components (06:54:40 -> 06,54,40),
#             hex hash-prefixes (>=8 hex chars; matched as a PREFIX of an
#             output hash, since prose truncates with ellipses).
#   exempt  : X1 VIEW blocks (rendered by views.sh, adjudicated byte-for-byte
#                by class 5 -- scanning them would only double-count);
#             X2 identifier-embedded digits (F1, Q4, C1, E5, Z5, Ord5:
#                digit PRECEDED by [A-Za-z0-9_]; digits FOLLOWED by letters
#                stay scanned, so 52 in "34+52.." and 72 in "72 pointers" count);
#             X3 standalone single digits (structural noise; boundary above).
#   match   : exact token equality after comma-stripping; no numeric
#             tolerance (a numeral is a claim about a token, not a quantity).
#             COMMA AMBIGUITY, resolved and reported: "2,610" is a thousands
#             group but "(−20,−212,138,40)" is a vector.  A comma token tries
#             the thousands reading first; if that has no provenance, it
#             falls back to its components (each >=2 digits checked alone);
#             if neither reading traces, the THOUSANDS form is what is
#             flagged.  Both readings failing is reported once, not twice.
#   corpus  : instrument outputs audit/{transcript,axioms}-roundK.txt for
#             K <= round (a ledger may cite earlier artifacts still shipped).
#   annotate: flags are cross-checked against the SOURCES (.lean) and the
#             builder certificate r6_gift_hessian.py -- NOT as provenance,
#             but to separate "mathematical content stated in prose"
#             (classes 1/7) from "process numeral with no artifact" for the
#             human classifying the queue.  Annotation never suppresses.
#
# ITERATION LOG (per the house rule that a first run is not evidence):
#   v1 = the rule as literally proposed (--no-exemptions reproduces it):
#        every digit-string, no classes.  On the round-6 ledger it drowns
#        the queue in structural digits -- the permissive-looking direction
#        the builder's Q2 predicted (output a reader learns to skim).
#   v2 = this file: X1-X3 labeled, counts printed every run, nothing
#        removed silently.  The residual flags ARE the product.
#
# Usage:
#   python3 audit/r7_numeral_gift.py --round 6            (live, PROOFS.md)
#   python3 audit/r7_numeral_gift.py --round 5 \
#           --ledger archive/PROOFS-round5.md \
#           --sources archive/src-round5                  (retro-test)
#   add --no-exemptions to reproduce the v1 first run.
# Exit: 0 if the review queue is empty, 1 otherwise (flags are findings for
#       a human, not automatic defects -- but an unreviewed queue must not
#       look like a pass).
# ---------------------------------------------------------------------------
import argparse, glob, os, re, sys

HEX = re.compile(r'(?<![0-9a-zA-Z])[0-9a-f]{8,}(?![0-9a-zA-Z])')
NUM = re.compile(r'\d+(?:,\d{3})*(?:\.\d+)?')
VIEW = re.compile(r'<!-- VIEW:\w+ BEGIN.*?<!-- VIEW:\w+ END -->', re.S)

def is_hexish(tok):
    return len(tok) >= 8 and any(c in 'abcdef' for c in tok)

def harvest(text):
    """(hex tokens, working text with hex blanked)"""
    hexes = [t for t in HEX.findall(text) if is_hexish(t)]
    return set(hexes), HEX.sub(lambda m: ' ' * len(m.group()), text)

def numerals(text):
    """yield (surface, joined, components, line_no, exempt_class)."""
    out = []
    for m in NUM.finditer(text):
        surface = m.group()
        joined = surface.replace(',', '')
        comps = [c for c in surface.split(',') if len(c) >= 2]
        pre = text[m.start() - 1] if m.start() > 0 else ' '
        cls = None
        if pre.isalnum() or pre == '_':
            cls = 'X2-identifier-embedded'
        elif len(joined) == 1:
            cls = 'X3-single-digit'
        line = text.count('\n', 0, m.start()) + 1
        out.append((surface, joined, comps, line, cls))
    return out

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--round', type=int, default=6)
    ap.add_argument('--ledger', default='PROOFS.md')
    ap.add_argument('--sources', default='.',
                    help='dir holding the .lean sources of that round')
    ap.add_argument('--no-exemptions', action='store_true',
                    help='v1: the rule exactly as proposed, no classes')
    a = ap.parse_args()

    raw = open(a.ledger, encoding='utf-8').read()

    # X1: strip VIEW blocks (count what was inside for the report)
    view_text = ' '.join(VIEW.findall(raw))
    _, vwork = harvest(view_text)
    x1_count = sum(1 for _ in NUM.finditer(vwork))
    work_raw = raw if a.no_exemptions else VIEW.sub(
        lambda m: '\n' * m.group().count('\n'), raw)

    led_hex, work = harvest(work_raw)
    toks = numerals(work)

    # corpus: instrument outputs, rounds <= N
    outs = sorted(p for p in glob.glob('audit/*-round[0-9].txt')
                  if int(p[-5]) <= a.round)
    corpus, corpus_hex = set(), set()
    for p in outs:
        t = open(p, encoding='utf-8').read()
        hx, w = harvest(t)
        corpus_hex |= hx
        corpus |= {m.group().replace(',', '') for m in NUM.finditer(w)}

    # annotation corpus (context only, never provenance)
    ann = {}
    ann_files = sorted(glob.glob(os.path.join(a.sources, '*.lean'))) + \
                [p for p in ['audit/r6_gift_hessian.py'] if os.path.exists(p)]
    for p in ann_files:
        t = open(p, encoding='utf-8', errors='replace').read()
        _, w = harvest(t)
        for m in NUM.finditer(w):
            ann.setdefault(m.group().replace(',', ''), set()).add(os.path.basename(p))

    print('=' * 66)
    print(f' NUMERAL GIFT -- provenance of digit-strings in {a.ledger}')
    print(f' outputs corpus : {", ".join(outs) if outs else "(none)"}')
    print(f' mode           : {"v1 (no exemptions)" if a.no_exemptions else "v2 (X1-X3 labeled)"}')
    print('=' * 66)

    lines = raw.split('\n')
    exempt_counts, checked, matched, flagged = {}, 0, 0, {}
    for surface, joined, comps, line, cls in toks:
        if cls and not a.no_exemptions:
            exempt_counts[cls] = exempt_counts.get(cls, 0) + 1
            continue
        checked += 1
        if joined in corpus:
            matched += 1
        elif ',' in surface and comps and all(c in corpus for c in comps):
            matched += 1          # vector reading: every component traces
        else:
            flagged.setdefault(surface, []).append(line)
    hex_checked = 0
    for h in led_hex:
        hex_checked += 1
        if any(c.startswith(h) or h.startswith(c) for c in corpus_hex):
            matched += 1
        else:
            flagged.setdefault(h[:16] + '(hex)', []).append(-1)

    if not a.no_exemptions:
        print(f' exempt X1-view-blocks          : {x1_count} tokens (adjudicated by views.sh, class 5)')
        for k in sorted(exempt_counts):
            print(f' exempt {k:24}: {exempt_counts[k]} tokens')
    print(f' checked: {checked} numeral tokens + {hex_checked} hash prefixes; '
          f'matched occurrences: {matched}; flagged occurrences: '
          f'{sum(len(v) for v in flagged.values())}')
    print()
    if flagged:
        print(f' REVIEW QUEUE ({len(flagged)} distinct tokens) -- no output provenance:')
        for tok in sorted(flagged, key=lambda t: (flagged[t][0], t)):
            ls = flagged[tok]
            where = ','.join(str(l) for l in ls if l > 0) or 'hex'
            note = ''
            keys = [tok.replace(',', '')] + [c for c in tok.split(',') if len(c) >= 2]
            hits = set().union(*[ann.get(k, set()) for k in keys])
            if hits:
                note = f'  [appears in: {", ".join(sorted(hits))}]'
            if ',' in tok:
                note += '  [comma-ambiguous: readings ' + \
                        tok.replace(",", "") + ' | ' + '+'.join(keys[1:]) + ']'
            ctx = ''
            for l in ls:
                if l > 0:
                    ctx = lines[l - 1].strip()[:72]
                    break
            print(f'  REVIEW  {tok:>10}  line(s) {where}{note}')
            if ctx:
                print(f'          | {ctx}')
    else:
        print(' REVIEW QUEUE: empty')

    print()
    if flagged:
        print(f'RESULT: FAIL -- {len(flagged)} numeral(s) with no instrument provenance.')
        print('        Each needs a human verdict: stale / derived / content / external.')
        sys.exit(1)
    print('RESULT: PASS -- every checked numeral traces to an instrument output.')
    sys.exit(0)

main()
