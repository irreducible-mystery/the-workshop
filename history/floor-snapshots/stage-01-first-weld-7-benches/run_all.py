"""THE WORKSHOP — run every bench, report the weld.

hold still nothing but the joining; make every noun earn its way in
as a fixed point, a sediment, a habit, a role.
"""
import time
import traceback

BENCHES = [
    ("arena_gns",
     "Bench 1 — ARENA: state spaces precipitate from relatings (GNS) [exact]"),
    ("sheaf_contextuality",
     "Bench 2 — SHEAF: local views everywhere, no global view (Mermin-Peres) [exact]"),
    ("habit_definetti",
     "Bench 3 — HABIT: law as sediment (Polya / de Finetti) [rigorous toy — risk budget]"),
    ("fixedpoint_rg",
     "Bench 4 — FIXED POINT: things = invariants of coarse-graining (RG) + quine"),
    ("interaction_bisim",
     "Bench 5 — INTERACTION: identity from relating alone (bisimulation) [exact]"),
    ("cast_factorization",
     "Bench 6 — CAST: the parts discovered from the play (mereology toy)"),
]


def main():
    lines, ok_all = [], True
    lines.append("THE WORKSHOP — WELD REPORT")
    lines.append("=" * 74)
    for mod, title in BENCHES:
        lines.append("")
        lines.append(title)
        t0 = time.time()
        try:
            m = __import__(mod)
            m.demonstrate(lines.append)
            lines.append(f"  [PASS] all self-checks green ({time.time() - t0:.1f}s)")
        except Exception:
            ok_all = False
            lines.append("  [FAIL]")
            lines.append(traceback.format_exc())
    lines.append("")
    lines.append("=" * 74)
    if ok_all:
        lines.append("floor check: every bench stood on one fixture — composition,")
        lines.append("the associative product. It held.")
    else:
        lines.append("WELD INCOMPLETE — see failures above.")
    report = "\n".join(lines)
    print(report)
    with open("WELD_REPORT.txt", "w") as f:
        f.write(report + "\n")
    return 0 if ok_all else 1


if __name__ == "__main__":
    raise SystemExit(main())
