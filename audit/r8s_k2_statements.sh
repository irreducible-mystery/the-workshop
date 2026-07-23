#!/bin/sh
# r8s_k2_statements.sh -- ROUND-8 TERMINAL AUDIT, K2 (the coker seat).
# Quote and pin the load-bearing statements of MagicSquare.lean S6.5:
# the quotient construction (abbrev Coker over cokerSetoid), the iso pair and
# hom property, the two-classes + distinctness pair, image_iff_even,
# imageCount_eq_32; the first-isomorphism-theorem shape; the section header;
# and the updated S6 disclaimer (old cited-not-proved note now points forward).
# Standalone: sh + grep + sed. Exit 0 = PASS, 1 = FAIL.
set -u
F=/home/claude/workshop/lean/MagicSquare.lean
fail=0
need() { # need <label> <exact-line-fragment>
  if grep -qF "$2" "$F"; then echo "  OK   $1"; else echo "  MISS $1  [$2]"; fail=1; fi
}
echo "== the quotient construction =="
need "cokerRel def (difference lands in im M)" "def cokerRel (u w : Ctx → Bool) : Prop := inImageV (vxor u w) = true"
need "cokerSetoid : Setoid (Ctx → Bool)"      "def cokerSetoid : Setoid (Ctx → Bool) where"
need "  .. with r := cokerRel"                "  r := cokerRel"
need "  .. iseqv from refl/symm/trans"        "  iseqv := ⟨cokerRel_refl, cokerRel_symm, cokerRel_trans⟩"
need "Coker = abbrev over cokerSetoid"        "abbrev Coker := Quotient cokerSetoid"
echo "== the iso =="
need "toZ2 via Quotient.lift phiV"            "def toZ2 : Coker → Bool :="
need "  .. lift + well-definedness"           "  Quotient.lift phiV (fun _ _ h => (cokerRel_iff _ _).mp h)"
need "fromZ2 section"                         "def fromZ2 (bit : Bool) : Coker := Quotient.mk cokerSetoid (cond bit bVec zeroVec)"
need "toZ2_fromZ2 (right inverse)"            "theorem toZ2_fromZ2 (bit : Bool) : toZ2 (fromZ2 bit) = bit := by"
need "fromZ2_toZ2 (left inverse)"             "theorem fromZ2_toZ2 (x : Coker) : fromZ2 (toZ2 x) = x := by"
need "toZ2_hom (group hom)"                   "theorem toZ2_hom (u w : Ctx → Bool) :"
need "  .. hom statement"                     "      toZ2 (Quotient.mk cokerSetoid u) ⊻ toZ2 (Quotient.mk cokerSetoid w) := by"
echo "== two classes, distinct =="
need "coker_two_classes"                      "theorem coker_two_classes (x : Coker) : x = fromZ2 false ∨ x = fromZ2 true := by"
need "coker_classes_distinct"                 "theorem coker_classes_distinct : fromZ2 false ≠ fromZ2 true := by"
echo "== im(M) = ker(phi), rank facts =="
need "image_iff_even statement"               "    inImage u0 u1 u2 u3 u4 u5 = !(phiBits u0 u1 u2 u3 u4 u5) := by"
need "imageCount_eq_32"                       "theorem imageCount_eq_32 : imageCount = 32 := rfl"
need "b_not_in_image"                         "theorem b_not_in_image : inImage false false false false false true = false := rfl"
echo "== first-isomorphism-theorem shape =="
need "phi linear (phiV_vxor)"                 "theorem phiV_vxor (u w : Ctx → Bool) : phiV (vxor u w) = phiV u ⊻ phiV w :="
need "phi surjective, value 1 (phiV_bVec)"    "theorem phiV_bVec : phiV bVec = true := rfl"
need "phi surjective, value 0 (phiV_zeroVec)" "theorem phiV_zeroVec : phiV zeroVec = false := rfl"
need "ker phi = im M transported (cokerRel_iff)" "theorem cokerRel_iff (u w : Ctx → Bool) : cokerRel u w ↔ phiV u = phiV w := by"
echo "== section header and updated S6 disclaimer =="
need "S6.5 header present"                    "/-! ## 6½. Item C, completed — the cokernel as a group:"
need "disclaimer: forward-pointing title"     "WHAT THIS SECTION DOES NOT DO, AND WHERE IT IS NOW DONE.  The step"
need "disclaimer: history kept (cited, not proved)" "**cited, not proved** — quotient vector spaces were judged out of scope, and"
need "disclaimer: round 8 closes it"          "textbook fact.  **Round 8 (the capstone) closes it.**  §6½ below does not appeal"
need "disclaimer: names imageCount_eq_32/b_not_in_image" "(\`imageCount_eq_32\`) and \`rank [M|b] = 6\` (\`b_not_in_image\`) rather than citing"
# the disclaimer's old flat form must be GONE:
if grep -qF "WHAT IS **NOT** PROVED HERE, STATED PLAINLY." "$F"; then
  echo "  FAIL old round-7 disclaimer text still present"; fail=1
else echo "  OK   old round-7 disclaimer text removed"; fi
# positional pins
for pin in "474:/-! ## 6½" "608:abbrev Coker := Quotient cokerSetoid" "310:WHAT THIS SECTION DOES NOT DO"; do
  ln=${pin%%:*}; frag=${pin#*:}
  if sed -n "${ln}p" "$F" | grep -qF "$frag"; then echo "  OK   line $ln pins [$frag]"
  else echo "  FAIL line $ln does not pin [$frag]"; fail=1; fi
done
if [ "$fail" = "0" ]; then echo "r8s_k2_statements: PASS"; exit 0
else echo "r8s_k2_statements: FAIL"; exit 1; fi
