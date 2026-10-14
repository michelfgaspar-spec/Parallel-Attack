import Mathlib.Data.Nat.Basic

/-! Literal historical reports from the frozen tables, not recomputed counts.
UNCOMPILED. No definition here asserts an executed or accepted traversal. -/
namespace Partials.WilfStructural.Packing

structure ReportedCountRow where
  claimId : String
  rowLabel : String
  columns : List String
  entries : List ℕ
  sourceMember : String
  sourceLine : ℕ
  sourceExcerpt : String
  lastColumnIsMaximum : Bool
  validated : Bool := false

structure ReportedZeroRange where
  firstN : ℕ
  lastN : ℕ
  sourceMember : String
  sourceExcerpt : String
  lastColumnIsMaximum : Bool
  validated : Bool := false

def reported_COUNT_ALLOCATION_n33 : ReportedCountRow := {
  claimId := "WILF-COUNT-ALLOCATION-n33"
  rowLabel := "33"
  columns := ["Allocations", "Remain", "Tuples", "Roots", "Labels"]
  entries := [440, 6, 78, 62, 12734]
  sourceMember := "manuscript/counts-packing.tex"
  sourceLine := 6
  sourceExcerpt := "33 & 440 & 6 & 78 & 62 & 12734 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_ALLOCATION_n34 : ReportedCountRow := {
  claimId := "WILF-COUNT-ALLOCATION-n34"
  rowLabel := "34"
  columns := ["Allocations", "Remain", "Tuples", "Roots", "Labels"]
  entries := [1327, 19, 342, 295, 156972]
  sourceMember := "manuscript/counts-packing.tex"
  sourceLine := 7
  sourceExcerpt := "34 & 1327 & 19 & 342 & 295 & 156972 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_ALLOCATION_n35 : ReportedCountRow := {
  claimId := "WILF-COUNT-ALLOCATION-n35"
  rowLabel := "35"
  columns := ["Allocations", "Remain", "Tuples", "Roots", "Labels"]
  entries := [3521, 31, 661, 560, 407977]
  sourceMember := "manuscript/counts-packing.tex"
  sourceLine := 8
  sourceExcerpt := "35 & 3521 & 31 & 661 & 560 & 407977 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_ALLOCATION_n36 : ReportedCountRow := {
  claimId := "WILF-COUNT-ALLOCATION-n36"
  rowLabel := "36"
  columns := ["Allocations", "Remain", "Tuples", "Roots", "Labels"]
  entries := [7644, 58, 864, 687, 837497]
  sourceMember := "manuscript/counts-packing.tex"
  sourceLine := 9
  sourceExcerpt := "36 & 7644 & 58 & 864 & 687 & 837497 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_ALLOCATION_n37 : ReportedCountRow := {
  claimId := "WILF-COUNT-ALLOCATION-n37"
  rowLabel := "37"
  columns := ["Allocations", "Remain", "Tuples", "Roots", "Labels"]
  entries := [13593, 105, 1469, 1122, 2626961]
  sourceMember := "manuscript/counts-packing.tex"
  sourceLine := 10
  sourceExcerpt := "37 & 13593 & 105 & 1469 & 1122 & 2626961 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_ALLOCATION_total : ReportedCountRow := {
  claimId := "WILF-COUNT-ALLOCATION-total"
  rowLabel := "Total"
  columns := ["Allocations", "Remain", "Tuples", "Roots", "Labels"]
  entries := [26525, 219, 3414, 2726, 4042141]
  sourceMember := "manuscript/counts-packing.tex"
  sourceLine := 12
  sourceExcerpt := "Total & 26525 & 219 & 3414 & 2726 & 4042141 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_BOX_n33 : ReportedCountRow := {
  claimId := "WILF-COUNT-BOX-n33"
  rowLabel := "33"
  columns := ["Boxes", "Splits", "Singletons", "Max. depth"]
  entries := [12734, 0, 0, 0]
  sourceMember := "manuscript/counts-packing.tex"
  sourceLine := 20
  sourceExcerpt := "33 & 12734 & 0 & 0 & 0 \\\\"
  lastColumnIsMaximum := true
}

def reported_COUNT_BOX_n34 : ReportedCountRow := {
  claimId := "WILF-COUNT-BOX-n34"
  rowLabel := "34"
  columns := ["Boxes", "Splits", "Singletons", "Max. depth"]
  entries := [156990, 9, 0, 2]
  sourceMember := "manuscript/counts-packing.tex"
  sourceLine := 21
  sourceExcerpt := "34 & 156990 & 9 & 0 & 2 \\\\"
  lastColumnIsMaximum := true
}

def reported_COUNT_BOX_n35 : ReportedCountRow := {
  claimId := "WILF-COUNT-BOX-n35"
  rowLabel := "35"
  columns := ["Boxes", "Splits", "Singletons", "Max. depth"]
  entries := [408619, 321, 1734, 10]
  sourceMember := "manuscript/counts-packing.tex"
  sourceLine := 22
  sourceExcerpt := "35 & 408619 & 321 & 1734 & 10 \\\\"
  lastColumnIsMaximum := true
}

def reported_COUNT_BOX_n36 : ReportedCountRow := {
  claimId := "WILF-COUNT-BOX-n36"
  rowLabel := "36"
  columns := ["Boxes", "Splits", "Singletons", "Max. depth"]
  entries := [838067, 285, 4881, 7]
  sourceMember := "manuscript/counts-packing.tex"
  sourceLine := 23
  sourceExcerpt := "36 & 838067 & 285 & 4881 & 7 \\\\"
  lastColumnIsMaximum := true
}

def reported_COUNT_BOX_n37 : ReportedCountRow := {
  claimId := "WILF-COUNT-BOX-n37"
  rowLabel := "37"
  columns := ["Boxes", "Splits", "Singletons", "Max. depth"]
  entries := [2627241, 140, 3371, 9]
  sourceMember := "manuscript/counts-packing.tex"
  sourceLine := 24
  sourceExcerpt := "37 & 2627241 & 140 & 3371 & 9 \\\\"
  lastColumnIsMaximum := true
}

def reported_COUNT_BOX_total : ReportedCountRow := {
  claimId := "WILF-COUNT-BOX-total"
  rowLabel := "Total/max."
  columns := ["Boxes", "Splits", "Singletons", "Max. depth"]
  entries := [4043651, 755, 9986, 10]
  sourceMember := "manuscript/counts-packing.tex"
  sourceLine := 26
  sourceExcerpt := "Total/max. & 4043651 & 755 & 9986 & 10 \\\\"
  lastColumnIsMaximum := true
}

def reported_COUNT_PROFILE_n14 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n14"
  rowLabel := "14"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [14, 6, 8, 0, 0]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 7
  sourceExcerpt := "14 & 14 & 6 & 8 & 0 & 0 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n15 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n15"
  rowLabel := "15"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [39, 12, 27, 0, 0]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 8
  sourceExcerpt := "15 & 39 & 12 & 27 & 0 & 0 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n16 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n16"
  rowLabel := "16"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [46, 13, 33, 0, 0]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 9
  sourceExcerpt := "16 & 46 & 13 & 33 & 0 & 0 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n17 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n17"
  rowLabel := "17"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [55, 14, 41, 0, 0]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 10
  sourceExcerpt := "17 & 55 & 14 & 41 & 0 & 0 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n18 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n18"
  rowLabel := "18"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [110, 34, 76, 0, 0]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 11
  sourceExcerpt := "18 & 110 & 34 & 76 & 0 & 0 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n19 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n19"
  rowLabel := "19"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [131, 37, 94, 0, 0]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 12
  sourceExcerpt := "19 & 131 & 37 & 94 & 0 & 0 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n20 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n20"
  rowLabel := "20"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [154, 41, 113, 0, 0]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 13
  sourceExcerpt := "20 & 154 & 41 & 113 & 0 & 0 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n21 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n21"
  rowLabel := "21"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [271, 69, 202, 0, 0]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 14
  sourceExcerpt := "21 & 271 & 69 & 202 & 0 & 0 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n22 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n22"
  rowLabel := "22"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [320, 76, 240, 120, 0]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 15
  sourceExcerpt := "22 & 320 & 76 & 240 & 120 & 0 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n23 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n23"
  rowLabel := "23"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [379, 83, 286, 299, 0]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 16
  sourceExcerpt := "23 & 379 & 83 & 286 & 299 & 0 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n24 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n24"
  rowLabel := "24"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [606, 155, 428, 654, 0]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 17
  sourceExcerpt := "24 & 606 & 155 & 428 & 654 & 0 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n25 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n25"
  rowLabel := "25"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [720, 171, 504, 1530, 0]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 18
  sourceExcerpt := "25 & 720 & 171 & 504 & 1530 & 0 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n26 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n26"
  rowLabel := "26"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [847, 191, 582, 3010, 0]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 19
  sourceExcerpt := "26 & 847 & 191 & 582 & 3010 & 0 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n27 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n27"
  rowLabel := "27"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [1283, 294, 874, 5006, 0]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 20
  sourceExcerpt := "27 & 1283 & 294 & 874 & 5006 & 0 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n28 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n28"
  rowLabel := "28"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [1513, 327, 1027, 7344, 0]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 21
  sourceExcerpt := "28 & 1513 & 327 & 1027 & 7344 & 0 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n29 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n29"
  rowLabel := "29"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [1786, 362, 1199, 11055, 0]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 22
  sourceExcerpt := "29 & 1786 & 362 & 1199 & 11055 & 0 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n30 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n30"
  rowLabel := "30"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [2577, 592, 1678, 17195, 0]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 23
  sourceExcerpt := "30 & 2577 & 592 & 1678 & 17195 & 0 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n31 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n31"
  rowLabel := "31"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [3044, 661, 1934, 28093, 0]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 24
  sourceExcerpt := "31 & 3044 & 661 & 1934 & 28093 & 0 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n32 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n32"
  rowLabel := "32"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [3573, 738, 2205, 43390, 0]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 25
  sourceExcerpt := "32 & 3573 & 738 & 2205 & 43390 & 0 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n33 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n33"
  rowLabel := "33"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [4996, 1075, 3046, 64896, 60]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 26
  sourceExcerpt := "33 & 4996 & 1075 & 3046 & 64896 & 60 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n34 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n34"
  rowLabel := "34"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [5871, 1201, 3556, 89551, 173]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 27
  sourceExcerpt := "34 & 5871 & 1201 & 3556 & 89551 & 173 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n35 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n35"
  rowLabel := "35"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [6894, 1338, 4151, 122870, 379]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 28
  sourceExcerpt := "35 & 6894 & 1338 & 4151 & 122870 & 379 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n36 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n36"
  rowLabel := "36"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [9355, 2019, 5483, 176079, 707]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 29
  sourceExcerpt := "36 & 9355 & 2019 & 5483 & 176079 & 707 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_n37 : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-n37"
  rowLabel := "37"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [10985, 2259, 6279, 248503, 1216]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 30
  sourceExcerpt := "37 & 10985 & 2259 & 6279 & 248503 & 1216 \\\\"
  lastColumnIsMaximum := false
}

def reported_COUNT_PROFILE_total : ReportedCountRow := {
  claimId := "WILF-COUNT-PROFILE-total"
  rowLabel := "Total"
  columns := ["alpha", "Empty", "Raw", "kappa", "Survive"]
  entries := [55569, 11768, 34066, 819595, 2535]
  sourceMember := "manuscript/counts-profiles.tex"
  sourceLine := 32
  sourceExcerpt := "Total & 55569 & 11768 & 34066 & 819595 & 2535 \\\\"
  lastColumnIsMaximum := false
}

def reported_U62 : ReportedZeroRange := {
  firstN := 14
  lastN := 32
  sourceMember := "manuscript/counts-packing.tex"
  sourceExcerpt := "$n=14,\\ldots,32$ are zero. The last column is a maximum, not an additive count.}"
  lastColumnIsMaximum := true
}

end Partials.WilfStructural.Packing
