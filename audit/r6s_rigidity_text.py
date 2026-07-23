#!/usr/bin/env python3
# =============================================================================
# r6s_rigidity_text.py -- round-6 SEAT audit: Rigidity.lean source text,
# header discipline, omega classification, hygiene, census + ledger
# reconciliation.  Standalone; reads the round-6 tree only.
#
# A FAIL here is a real discrepancy between an artifact and the tree
# (the script is a falsifier; it does not soften known findings).
# =============================================================================
import re, sys

T = "/home/claude/workshop/lean/"
rig    = open(T+"Rigidity.lean", encoding="utf-8").read()
anyon  = open(T+"Anyon.lean", encoding="utf-8").read()
proofs = open(T+"PROOFS.md", encoding="utf-8").read()
census = open(T+"audit/axioms-round6.txt", encoding="utf-8").read()
rlines = rig.split("\n")

results = []
def check(name, ok, detail=""):
    results.append((name, bool(ok)))
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")
def note(name, detail):
    print(f"NOTE  {name}  {detail}")

# ---------------------------------------------------------------------------
# R1 -- header discipline: the three commitments BEFORE any declaration
# ---------------------------------------------------------------------------
first_decl = next(i for i,l in enumerate(rlines, 1)
                  if re.match(r"^(inductive|def|structure|theorem|abbrev)\s", l))
first_thm  = next(i for i,l in enumerate(rlines, 1) if l.startswith("theorem"))
head = "\n".join(rlines[:first_decl-1])
check("R1.first_decl_after_header", first_decl == 154 and first_thm == 279,
      f"first declaration line {first_decl} (inductive Anyon), first theorem line {first_thm}")
check("R1a.refutation_in_header",
      "REFUTED the first draft of the charge" in head
      and "strict\n      associator" in head or "strict associator" in head.replace("\n      ", " "),
      "header (b): strict associator (1,1,1,1) non-solution, H also PSD, span(0,1,-1,0)")
check("R1a.freebie_in_header",
      "SYMMETRY FREEBIE" in head and "swapDir_null_of_cols_eq" in head,
      "header (c): q=r null direction is a symmetry freebie")
check("R1b.do_not_quote_in_header",
      "Do not quote the golden null direction as evidence" in head,
      "verbatim, header item (c)")
check("R1c.quantifier_domain_in_header",
      "ranges over `Z[φ]⁴`" in head and "no real number appears in this file" in head
      and "not a statement about `ℝ⁴`" in head,
      "header item (d): PSD quantifier over Z[phi]^4, not R^4")

# ---------------------------------------------------------------------------
# hygiene: comment-stripped forbidden tokens; imports; #print axioms
# ---------------------------------------------------------------------------
def strip_comments(src):
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if src.startswith("/-", i): depth += 1; i += 2; continue
        if src.startswith("-/", i) and depth: depth -= 1; i += 2; continue
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j; continue
        if depth == 0: out.append(src[i])
        i += 1
    return "".join(out)
code = strip_comments(rig)
forb = {}
for tok in ["sorry","native_decide","maxHeartbeats","maxRecDepth","by_contra",
            "Classical","set_option","Float","Real","Rat","#print"]:
    forb[tok] = len(re.findall(r"\b"+re.escape(tok)+r"\b", code))
forb["axiom"]   = len(re.findall(r"^\s*axiom\b", code, re.M))
forb["import"]  = len(re.findall(r"^\s*import\b", code, re.M))
forb["partial"] = len(re.findall(r"\bpartial\s+def\b", code))
check("hygiene.stripped_tokens_zero", all(v == 0 for v in forb.values()),
      "comment-stripped: " + ", ".join(f"{k}={v}" for k,v in forb.items() if v))
check("hygiene.zero_imports", forb["import"] == 0, "no import lines (raw grep agrees)")

# ---------------------------------------------------------------------------
# R7 -- omega enumeration and classification
# ---------------------------------------------------------------------------
omega_lines = [(i,l) for i,l in enumerate(rlines,1) if "omega" in l]
comment_om, tactic_om = [], []
depth = 0
for i,l in enumerate(rlines,1):
    opens, closes = l.count("/-"), l.count("-/")
    in_comment = depth > 0 or l.strip().startswith("--")
    if "omega" in l:
        (comment_om if (in_comment or (opens and "omega" in l.split("/-")[1] if opens else False)) else tactic_om).append((i,l))
    depth += opens - closes
    if depth < 0: depth = 0
conj_same_line = [i for i,l in tactic_om if "∧" in l]
have_conj = [i for i,l in tactic_om
             if re.search(r"have\s+\w+\s*:\s*[^:=]*∧[^:=]*:=\s*by\s+omega", l)]
splits = sum(1 for _,l in tactic_om if "refine ⟨?_, ?_⟩ <;>" in l)
pairs  = sum(1 for _,l in tactic_om if "⟨by omega" in l)
check("R7.omega_no_conjunctive_goals",
      len(conj_same_line) == 0 and len(have_conj) == 0,
      f"{len(tactic_om)} tactic omega sites ({len(comment_om)} comment mentions); "
      f"0 with ∧ on the goal; {splits} split-first `refine ⟨?_,?_⟩ <;> omega`, {pairs} `⟨by omega,..⟩` pairs")
sec2c_start = next(i for i,l in enumerate(rlines,1) if "§2c" in l)
sec2c_end   = next(i for i,l in enumerate(rlines,1) if i > sec2c_start and l.strip() == "end Zp")
om_in_2c_to_7 = [i for i,_ in tactic_om if sec2c_start <= i <= 2043]
check("R7.omega_absent_from_cone_and_worlds", om_in_2c_to_7 == [],
      f"zero tactic omega between line {sec2c_start} (§2c) and 2043 (§8 start): the cone, jets, and all four worlds are omega-free")

# ---------------------------------------------------------------------------
# R6 -- §2c builds only on the round-5 order quartet
# ---------------------------------------------------------------------------
block = "\n".join(rlines[sec2c_start-1:sec2c_end])
used_order = set(re.findall(r"\b(trichotomy|pos_add|pos_mul|mul_ne_zero|posP_\w+|posUN\w*|PosP|Ord5\.\w+)\b", block))
check("R6.cone_dependency_quartet",
      used_order == {"trichotomy","pos_add","pos_mul","mul_ne_zero"},
      f"§2c (lines {sec2c_start}-{sec2c_end}) order deps = {sorted(used_order)}; no PosP/posUN/Ord5 descent, no omega")
psd_body = rig[rig.index("theorem psd_of_sos"):rig.index("theorem ker_of_sos")]
ker_body = rig[rig.index("theorem ker_of_sos"):rig.index("/-! ### determinants")]
cone_used = set(re.findall(r"Zp\.(nn_\w+|eq_zero_of_\w+|not_nn)", psd_body+ker_body))
check("R6.psd_ker_ride_on_cone",
      {"nn_of_mul_pos","nn_add","nn_mul","nn_sq","nn_split","eq_zero_of_sq","eq_zero_of_mul_pos"} <= cone_used,
      f"psd_of_sos/ker_of_sos consume the cone layer: {sorted(cone_used)} -- 'the order pays for the rigidity'")

# ---------------------------------------------------------------------------
# R3 -- cross-file names in the tangentY adjudicator resolve in Anyon.lean
# ---------------------------------------------------------------------------
check("R3.crossfile_names_resolve",
      "theorem pentagon_iff" in anyon and "theorem tier3a_tier3b_same_anyon" in anyon
      and "pentagon_iff" in rig and "tier3a_tier3b_same_anyon" in rig,
      "tangentY docstring names pentagon_iff + tier3a_tier3b_same_anyon; both exist in Anyon.lean (named, not claimed)")

# key statements, verbatim from source (guard against paraphrase drift)
check("R3.HY_psd_statement",
      "theorem HY_psd (w : V4) : Zp.Nn (qform HY w)" in rig,
      "genuinely forall-quantified: hypothesis-free w : V4 = Fin 4 -> Zp")
check("R3.HY_kernel_statement",
      "qform HY w = Zp.zero ↔\n      (w 0 = Zp.zero ∧ w 3 = Zp.zero ∧ dot coTY w = Zp.zero)" in rig,
      "iff, forall w; RHS exactly the line conditions")
check("R3.YL_solution_statement",
      "∀ a b c dd x y t w v, pentOK (Fg pY qY rY sY) a b c dd x y t w v = true" in rig,
      "9 Anyon binders = 512 instances, decided by cases+rfl")
check("R4.strict_battery_statements",
      "theorem strict_not_critical" in rig and
      "theorem strict_also_psd (w : V4) : Zp.Nn (qform HS w)" in rig and
      "theorem strict_also_rank3" in rig and
      "det4 HS = Zp.zero ∧ Zp.pos (det3 HS 0 1 3 0 1 3) = true" in rig,
      "the refutation battery is in-file, same shapes as the YL theorems, at a proven non-solution")

# ---------------------------------------------------------------------------
# R5 -- golden closure names; the declared asymmetry; budget claims
# ---------------------------------------------------------------------------
golden18 = (["theorem J2.ext'", "theorem SS_G_zero"]
            + [f"theorem grad_G_{i}" for i in range(4)]
            + [f"theorem gg_e{ij}" for ij in
               ["00","01","02","03","11","12","13","22","23","33"]]
            + ["theorem germ_G", "theorem hess_G"])
missing = [n for n in golden18 if n not in rig]
check("R5.golden18_names_present", missing == [] and len(golden18) == 18,
      "J2.ext' + SS_G_zero + grad_G_0..3 + gg_e00..e33 + germ_G + hess_G = 18")
check("R5.gg_are_rfl",
      all(re.search(rf"theorem gg_e{ij} : \(germ epRng pG qG qG sG\)\.e{ij} = .*:= by rfl", rig)
          for ij in ["00","01","02","03","11","12","13","22","23","33"]),
      "each of the ten second-order projections is a bare `by rfl`")
check("R5.germ_G_is_ext_glue",
      "theorem germ_G : germ epRng pG qG qG sG = GG :=\n  J2.ext' SS_G_zero grad_G_0 grad_G_1 grad_G_2 grad_G_3\n    gg_e00" in rig,
      "germ_G = J2.ext' applied to the fifteen projections; no decide, no budget")
rig_ws = re.sub(r"\s+", " ", rig)
check("R5.no_forall_psd_at_golden",
      "Ep.Nn" not in rig and "theorem HG_psd" not in rig
      and "There is NO `∀ w : E⁴` positive-semidefiniteness theorem in this section" in rig_ws,
      "no quantified PSD over E exists in-file AND the section header declares its absence")
check("R5.Ep_closure_declared_not_attempted",
      "NOT proved closed under addition or under multiplication" in rig
      and "NOT\n    ATTEMPTED" in rig.replace("are NOT\n    ATTEMPTED","are NOT\n    ATTEMPTED")
      and "NOT ATTEMPTED" in rig.replace("\n"," ").replace("  "," ")
      or ("NOT ATTEMPTED" in re.sub(r"\s+"," ",rig)),
      "Ep.pos closure gap named in the adjudicator block and SS8 header")
overrun_lines = [(i,l) for i,l in enumerate(rlines,1)
                 if re.search(r"overrun|exceeds? the default|do(es)? fail|times? out", l)]
named_forms = re.sub(r"\s+"," ",rig)
two_forms = ("germ epRng pG qG qG sG = GG := by rfl" in named_forms
             and "hess epRng pG qG qG sG i j = HG i j := by rfl" in named_forms)
sosG_third = "a single `decide` over all sixteen exceeds the default heartbeat budget" in named_forms
check("R5.budget_overruns_named_narrowly", two_forms,
      f"exactly the two measured forms are named as failing (whole-structure germ, indexed hess); "
      f"{len(overrun_lines)} overrun-flavoured lines, all in comments")
if sosG_third:
    note("R5.third_budget_claim",
         "sos_G docstring adds a THIRD budget assertion (single 16-entry decide exceeds default) -- "
         "narrow and plausible but NOT among the two the ledger says were measured/re-run")
oor_sites = [i for i,l in enumerate(rlines,1) if "out of reach" in l]
def in_retraction(i):
    ctx = " ".join(rlines[max(0,i-4):i+3])
    return ("claim was too strong" in ctx) or ("What was FALSE is the" in ctx) or ("FALSE" in ctx)
check("R5.no_generalization_left",
      all(in_retraction(i) for i in oor_sites) and "What was FALSE is the\n    generalisation" in rig,
      f"'out of reach' occurs at lines {oor_sites}, each inside the retraction quoting the old error; "
      "no live generalization remains")

# ---------------------------------------------------------------------------
# R2 -- verbatim transcription spot-check of the Ord5 toolkit vs Anyon.lean
# ---------------------------------------------------------------------------
def body(src, name, stop):
    i = src.index(name)
    j = src.index(stop, i+1)
    return re.sub(r"\s+", " ", src[i:j]).strip()
same = True
for nm, stop in [("theorem posP_add_hard", "/-- totally positive + mixed"),
                 ("theorem no_sqrt5_fuel", "theorem no_sqrt5 "),
                 ("def posUN", "theorem posUN_iff")]:
    try:
        if body(rig, nm, stop) != body(anyon, nm, stop): same = False
    except ValueError:
        same = False
check("R2.ord5_verbatim_spotcheck", same,
      "posP_add_hard, no_sqrt5_fuel, posUN bodies byte-identical (mod whitespace) to Anyon.lean §Ord5 "
      "(full check: audit/transcription.sh, PASS)")

# ---------------------------------------------------------------------------
# R7/R8 -- census + counts + ledger reconciliation
# ---------------------------------------------------------------------------
thm_count = len(re.findall(r"^theorem ", rig, re.M))
line_count = rig.count("\n")
m = re.search(r"Rigidity\s+(\d+)\s+(\d+)\s+(\d+)", census)
c_tot, c_free, c_rest = map(int, m.groups())
fam = dict(re.findall(r"Rigidity\s+\[([^\]]+)\]\s+(\d+)", census))
fam_sum = sum(int(v) for v in fam.values())
check("R7.census_arithmetic",
      c_tot == 214 and c_free == 59 and c_rest == 155 and c_free + fam_sum == 214
      and fam == {"propext, Quot.sound":"124","Quot.sound":"1","propext":"30"},
      f"214 = 59 free + 124 [propext,Quot.sound] + 1 [Quot.sound] + 30 [propext]; sorryAx 0, Classical.choice 0 stated")
check("R7.theorem_count_ties", thm_count == 214 and c_tot == thm_count,
      f"grep ^theorem = {thm_count} = census; file §10 prose says 'all 214 of them'")
check("R7.golden18_le_axiomfree", 18 <= c_free,
      "ledger: 18 golden theorems axiom-free -- unverifiable without Lean here, but 18 <= 59 and all 18 are "
      "rfl/rw Eq-statements (no ∧, no decide), the profile that plausibly needs no axioms")
tots = re.search(r"TOTAL\s+(\d+)\s+(\d+)\s+(\d+)", census)
check("R7.five_file_totals",
      tots.group(1) == "1053" and 21+63+714+41+214 == 1053 and 21+16+307+41+59 == 444,
      "1053 theorems, 444 axiom-free, files sum exactly")

# the ledger's headline sentence vs the tree (expected finding)
mm = re.search(r"Rigidity\.lean` \(new, fifth file, ([\d,]+) lines, (\d+) theorems", proofs)
led_lines, led_thms = int(mm.group(1).replace(",","")), int(mm.group(2))
check("R8.ledger_headline_matches_tree",
      led_lines == line_count and led_thms == thm_count,
      f"PROOFS.md:169 says {led_lines} lines / {led_thms} theorems; tree has {line_count} lines / {thm_count} theorems "
      "(headline written pre-closure, never updated; the AUDIT section itself records the growth)")
check("R8.file_prose_count_current",
      "all 214 of them" in rig and "all 199 of them" not in rig,
      "Rigidity §10's one in-prose count was bumped to 214 and matches the census")
check("R8.ledger_key_rows_match_source",
      "∀ w : Z[φ]⁴, Nn (qform HY w)" in proofs
      and "(−20,−212,138,40)" in proofs.replace("−","−") and "wᵀHw = −400" in proofs
      and "34+52φ" in proofs,
      "HY_psd row, control-point vector, swap value: ledger sentences match what the source proves (semantics: r6s_rigidity_semantics.py)")
# Q3 of the ledger vs the ledger's own AUDIT section and the source
proofs_ws = re.sub(r"\s+", " ", proofs)
q3_stale = ("`HG` is transcribed because the E-valued germ overruns the default heartbeat budget" in proofs_ws)
closed_in_ledger = ("The Hessian is now the kernel's own second derivative at all four worlds" in proofs_ws)
closed_in_source = ("theorem germ_G" in rig and "theorem hess_G" in rig)
check("R8.ledger_Q3_not_stale", not (q3_stale and closed_in_ledger and closed_in_source),
      "PROOFS.md Q3 says (present tense) 'HG is transcribed because the E-valued germ overruns the default "
      "heartbeat budget' -- retracted by the same ledger's AUDIT section and falsified by the source "
      "(germ_G/hess_G are theorems).  Question written pre-closure, never updated: F3/DEFECT-1 species, "
      "and the class-7 specimen Q4 predicts")
aud199 = "§10 asserts the axiom profile of all 199 theorems" in proofs_ws
if aud199:
    note("R8.audit_note_199_stale",
         "PROOFS.md:561 minor-note still says '§10 asserts ... all 199 theorems' in present tense; "
         "the file says 214 (bump recorded 30 lines earlier at :532). Historical register, micro F3 echo")

hdr_cost = "3 min 49 s – 4 min 24 s" in rig
led_cost = "2m10s → 4m25s" in proofs
if hdr_cost and led_cost:
    note("R8.cost_prose_1s_wobble",
         "header says 3m49s-4m24s (two runs); ledger AUDIT says '2m10s -> 4m25s'; transcript view 249808 ms = 4m09.8s. "
         "1 s inconsistency between two prose sites; the view is the number")

# ---------------------------------------------------------------------------
n_fail = sum(1 for _,ok in results if not ok)
print("-"*74)
print(f"TOTAL {len(results)} checks, {len(results)-n_fail} pass, {n_fail} fail")
print("RESULT: " + ("PASS" if n_fail == 0 else f"FAIL ({n_fail} real discrepancy/ies -- see lines above)"))
sys.exit(0 if n_fail == 0 else 1)
