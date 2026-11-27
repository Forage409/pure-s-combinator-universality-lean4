import formal_q10_q5_simplified.chunks.q5s_chunk_0
import formal_q10_q5_simplified.chunks.q5s_chunk_1
import formal_q10_q5_simplified.chunks.q5s_chunk_2
import formal_q10_q5_simplified.chunks.q5s_chunk_3
import formal_q10_q5_simplified.chunks.q5s_chunk_4
import formal_q10_q5_simplified.chunks.q5s_chunk_5
import formal_q10_q5_simplified.chunks.q5s_chunk_6
import formal_q10_q5_simplified.chunks.q5s_chunk_7

/-!
# Simplified Resolution of Barendregt et al. Open Question 5 (`A_P`, 39 States)
# & Exact 113-State Myhill-Nerode Minimality of `PH ⊆ A_P × A_HN`

1. **Soundness of `A_P` (`evalP_ne_p37_implies_productive`)**.
2. **Exact 113-State Myhill-Nerode Minimality (`ph_113_nerode_minimal`, `ph_113_quotient_lower_bound`)**:
   Proves via 113 closed combinators and a greedy cover of ONLY 17 closed contexts that NO smaller
   quotient of `CL(S)` can decide `(Productive, HasHNF)`.
3. **Collapsed `tripleRankP`** (2D `msP` + 35 overrides) & **Unified Rank-10 Stratification**:
   Compresses 17 ranks down to 10 ranks, deletes `rWeakRank` and the odd/even parity split,
   and shrinks `c3_s2` to 174 entries across 98 `(x, z)` pairs via `directN1N2Rank`.

Zero `sorry`, zero `Classical.choice`, zero `native_decide`, zero custom axioms.
-/

namespace SimplifiedQ10Q5
set_option linter.constructorNameAsVariable false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
open FormalAlgebra

private theorem dp_s_law_all {x : Nat} (hx : x < 39) : dp_s_law_row x = true :=
  match x, hx with
  | 0, _ => dp_s_law_r0 | 1, _ => dp_s_law_r1 | 2, _ => dp_s_law_r2 | 3, _ => dp_s_law_r3 | 4, _ => dp_s_law_r4
  | 5, _ => dp_s_law_r5 | 6, _ => dp_s_law_r6 | 7, _ => dp_s_law_r7 | 8, _ => dp_s_law_r8 | 9, _ => dp_s_law_r9
  | 10, _ => dp_s_law_r10 | 11, _ => dp_s_law_r11 | 12, _ => dp_s_law_r12 | 13, _ => dp_s_law_r13 | 14, _ => dp_s_law_r14
  | 15, _ => dp_s_law_r15 | 16, _ => dp_s_law_r16 | 17, _ => dp_s_law_r17 | 18, _ => dp_s_law_r18 | 19, _ => dp_s_law_r19
  | 20, _ => dp_s_law_r20 | 21, _ => dp_s_law_r21 | 22, _ => dp_s_law_r22 | 23, _ => dp_s_law_r23 | 24, _ => dp_s_law_r24
  | 25, _ => dp_s_law_r25 | 26, _ => dp_s_law_r26 | 27, _ => dp_s_law_r27 | 28, _ => dp_s_law_r28 | 29, _ => dp_s_law_r29
  | 30, _ => dp_s_law_r30 | 31, _ => dp_s_law_r31 | 32, _ => dp_s_law_r32 | 33, _ => dp_s_law_r33 | 34, _ => dp_s_law_r34
  | 35, _ => dp_s_law_r35 | 36, _ => dp_s_law_r36 | 37, _ => dp_s_law_r37 | 38, _ => dp_s_law_r38
  | _ + 39, hbad => False.elim (by omega)
private theorem rankP_idx_all {x : Nat} (hx : x < 39) : rankP_idx_row x = true :=
  match x, hx with
  | 0, _ => rankP_idx_r0 | 1, _ => rankP_idx_r1 | 2, _ => rankP_idx_r2 | 3, _ => rankP_idx_r3 | 4, _ => rankP_idx_r4
  | 5, _ => rankP_idx_r5 | 6, _ => rankP_idx_r6 | 7, _ => rankP_idx_r7 | 8, _ => rankP_idx_r8 | 9, _ => rankP_idx_r9
  | 10, _ => rankP_idx_r10 | 11, _ => rankP_idx_r11 | 12, _ => rankP_idx_r12 | 13, _ => rankP_idx_r13 | 14, _ => rankP_idx_r14
  | 15, _ => rankP_idx_r15 | 16, _ => rankP_idx_r16 | 17, _ => rankP_idx_r17 | 18, _ => rankP_idx_r18 | 19, _ => rankP_idx_r19
  | 20, _ => rankP_idx_r20 | 21, _ => rankP_idx_r21 | 22, _ => rankP_idx_r22 | 23, _ => rankP_idx_r23 | 24, _ => rankP_idx_r24
  | 25, _ => rankP_idx_r25 | 26, _ => rankP_idx_r26 | 27, _ => rankP_idx_r27 | 28, _ => rankP_idx_r28 | 29, _ => rankP_idx_r29
  | 30, _ => rankP_idx_r30 | 31, _ => rankP_idx_r31 | 32, _ => rankP_idx_r32 | 33, _ => rankP_idx_r33 | 34, _ => rankP_idx_r34
  | 35, _ => rankP_idx_r35 | 36, _ => rankP_idx_r36 | 37, _ => rankP_idx_r37 | 38, _ => rankP_idx_r38
  | _ + 39, hbad => False.elim (by omega)
private theorem dph_bridge_all {x : Nat} (hx : x < 113) : dph_bridge_row x = true :=
  match x, hx with
  | 0, _ => dph_bridge_r0 | 1, _ => dph_bridge_r1 | 2, _ => dph_bridge_r2 | 3, _ => dph_bridge_r3 | 4, _ => dph_bridge_r4
  | 5, _ => dph_bridge_r5 | 6, _ => dph_bridge_r6 | 7, _ => dph_bridge_r7 | 8, _ => dph_bridge_r8 | 9, _ => dph_bridge_r9
  | 10, _ => dph_bridge_r10 | 11, _ => dph_bridge_r11 | 12, _ => dph_bridge_r12 | 13, _ => dph_bridge_r13 | 14, _ => dph_bridge_r14
  | 15, _ => dph_bridge_r15 | 16, _ => dph_bridge_r16 | 17, _ => dph_bridge_r17 | 18, _ => dph_bridge_r18 | 19, _ => dph_bridge_r19
  | 20, _ => dph_bridge_r20 | 21, _ => dph_bridge_r21 | 22, _ => dph_bridge_r22 | 23, _ => dph_bridge_r23 | 24, _ => dph_bridge_r24
  | 25, _ => dph_bridge_r25 | 26, _ => dph_bridge_r26 | 27, _ => dph_bridge_r27 | 28, _ => dph_bridge_r28 | 29, _ => dph_bridge_r29
  | 30, _ => dph_bridge_r30 | 31, _ => dph_bridge_r31 | 32, _ => dph_bridge_r32 | 33, _ => dph_bridge_r33 | 34, _ => dph_bridge_r34
  | 35, _ => dph_bridge_r35 | 36, _ => dph_bridge_r36 | 37, _ => dph_bridge_r37 | 38, _ => dph_bridge_r38 | 39, _ => dph_bridge_r39
  | 40, _ => dph_bridge_r40 | 41, _ => dph_bridge_r41 | 42, _ => dph_bridge_r42 | 43, _ => dph_bridge_r43 | 44, _ => dph_bridge_r44
  | 45, _ => dph_bridge_r45 | 46, _ => dph_bridge_r46 | 47, _ => dph_bridge_r47 | 48, _ => dph_bridge_r48 | 49, _ => dph_bridge_r49
  | 50, _ => dph_bridge_r50 | 51, _ => dph_bridge_r51 | 52, _ => dph_bridge_r52 | 53, _ => dph_bridge_r53 | 54, _ => dph_bridge_r54
  | 55, _ => dph_bridge_r55 | 56, _ => dph_bridge_r56 | 57, _ => dph_bridge_r57 | 58, _ => dph_bridge_r58 | 59, _ => dph_bridge_r59
  | 60, _ => dph_bridge_r60 | 61, _ => dph_bridge_r61 | 62, _ => dph_bridge_r62 | 63, _ => dph_bridge_r63 | 64, _ => dph_bridge_r64
  | 65, _ => dph_bridge_r65 | 66, _ => dph_bridge_r66 | 67, _ => dph_bridge_r67 | 68, _ => dph_bridge_r68 | 69, _ => dph_bridge_r69
  | 70, _ => dph_bridge_r70 | 71, _ => dph_bridge_r71 | 72, _ => dph_bridge_r72 | 73, _ => dph_bridge_r73 | 74, _ => dph_bridge_r74
  | 75, _ => dph_bridge_r75 | 76, _ => dph_bridge_r76 | 77, _ => dph_bridge_r77 | 78, _ => dph_bridge_r78 | 79, _ => dph_bridge_r79
  | 80, _ => dph_bridge_r80 | 81, _ => dph_bridge_r81 | 82, _ => dph_bridge_r82 | 83, _ => dph_bridge_r83 | 84, _ => dph_bridge_r84
  | 85, _ => dph_bridge_r85 | 86, _ => dph_bridge_r86 | 87, _ => dph_bridge_r87 | 88, _ => dph_bridge_r88 | 89, _ => dph_bridge_r89
  | 90, _ => dph_bridge_r90 | 91, _ => dph_bridge_r91 | 92, _ => dph_bridge_r92 | 93, _ => dph_bridge_r93 | 94, _ => dph_bridge_r94
  | 95, _ => dph_bridge_r95 | 96, _ => dph_bridge_r96 | 97, _ => dph_bridge_r97 | 98, _ => dph_bridge_r98 | 99, _ => dph_bridge_r99
  | 100, _ => dph_bridge_r100 | 101, _ => dph_bridge_r101 | 102, _ => dph_bridge_r102 | 103, _ => dph_bridge_r103 | 104, _ => dph_bridge_r104
  | 105, _ => dph_bridge_r105 | 106, _ => dph_bridge_r106 | 107, _ => dph_bridge_r107 | 108, _ => dph_bridge_r108 | 109, _ => dph_bridge_r109
  | 110, _ => dph_bridge_r110 | 111, _ => dph_bridge_r111 | 112, _ => dph_bridge_r112
  | _ + 113, hbad => False.elim (by omega)
private theorem nerode_sep_all {x : Nat} (hx : x < 113) : nerode_sep_row x = true :=
  match x, hx with
  | 0, _ => nerode_sep_r0 | 1, _ => nerode_sep_r1 | 2, _ => nerode_sep_r2 | 3, _ => nerode_sep_r3 | 4, _ => nerode_sep_r4
  | 5, _ => nerode_sep_r5 | 6, _ => nerode_sep_r6 | 7, _ => nerode_sep_r7 | 8, _ => nerode_sep_r8 | 9, _ => nerode_sep_r9
  | 10, _ => nerode_sep_r10 | 11, _ => nerode_sep_r11 | 12, _ => nerode_sep_r12 | 13, _ => nerode_sep_r13 | 14, _ => nerode_sep_r14
  | 15, _ => nerode_sep_r15 | 16, _ => nerode_sep_r16 | 17, _ => nerode_sep_r17 | 18, _ => nerode_sep_r18 | 19, _ => nerode_sep_r19
  | 20, _ => nerode_sep_r20 | 21, _ => nerode_sep_r21 | 22, _ => nerode_sep_r22 | 23, _ => nerode_sep_r23 | 24, _ => nerode_sep_r24
  | 25, _ => nerode_sep_r25 | 26, _ => nerode_sep_r26 | 27, _ => nerode_sep_r27 | 28, _ => nerode_sep_r28 | 29, _ => nerode_sep_r29
  | 30, _ => nerode_sep_r30 | 31, _ => nerode_sep_r31 | 32, _ => nerode_sep_r32 | 33, _ => nerode_sep_r33 | 34, _ => nerode_sep_r34
  | 35, _ => nerode_sep_r35 | 36, _ => nerode_sep_r36 | 37, _ => nerode_sep_r37 | 38, _ => nerode_sep_r38 | 39, _ => nerode_sep_r39
  | 40, _ => nerode_sep_r40 | 41, _ => nerode_sep_r41 | 42, _ => nerode_sep_r42 | 43, _ => nerode_sep_r43 | 44, _ => nerode_sep_r44
  | 45, _ => nerode_sep_r45 | 46, _ => nerode_sep_r46 | 47, _ => nerode_sep_r47 | 48, _ => nerode_sep_r48 | 49, _ => nerode_sep_r49
  | 50, _ => nerode_sep_r50 | 51, _ => nerode_sep_r51 | 52, _ => nerode_sep_r52 | 53, _ => nerode_sep_r53 | 54, _ => nerode_sep_r54
  | 55, _ => nerode_sep_r55 | 56, _ => nerode_sep_r56 | 57, _ => nerode_sep_r57 | 58, _ => nerode_sep_r58 | 59, _ => nerode_sep_r59
  | 60, _ => nerode_sep_r60 | 61, _ => nerode_sep_r61 | 62, _ => nerode_sep_r62 | 63, _ => nerode_sep_r63 | 64, _ => nerode_sep_r64
  | 65, _ => nerode_sep_r65 | 66, _ => nerode_sep_r66 | 67, _ => nerode_sep_r67 | 68, _ => nerode_sep_r68 | 69, _ => nerode_sep_r69
  | 70, _ => nerode_sep_r70 | 71, _ => nerode_sep_r71 | 72, _ => nerode_sep_r72 | 73, _ => nerode_sep_r73 | 74, _ => nerode_sep_r74
  | 75, _ => nerode_sep_r75 | 76, _ => nerode_sep_r76 | 77, _ => nerode_sep_r77 | 78, _ => nerode_sep_r78 | 79, _ => nerode_sep_r79
  | 80, _ => nerode_sep_r80 | 81, _ => nerode_sep_r81 | 82, _ => nerode_sep_r82 | 83, _ => nerode_sep_r83 | 84, _ => nerode_sep_r84
  | 85, _ => nerode_sep_r85 | 86, _ => nerode_sep_r86 | 87, _ => nerode_sep_r87 | 88, _ => nerode_sep_r88 | 89, _ => nerode_sep_r89
  | 90, _ => nerode_sep_r90 | 91, _ => nerode_sep_r91 | 92, _ => nerode_sep_r92 | 93, _ => nerode_sep_r93 | 94, _ => nerode_sep_r94
  | 95, _ => nerode_sep_r95 | 96, _ => nerode_sep_r96 | 97, _ => nerode_sep_r97 | 98, _ => nerode_sep_r98 | 99, _ => nerode_sep_r99
  | 100, _ => nerode_sep_r100 | 101, _ => nerode_sep_r101 | 102, _ => nerode_sep_r102 | 103, _ => nerode_sep_r103 | 104, _ => nerode_sep_r104
  | 105, _ => nerode_sep_r105 | 106, _ => nerode_sep_r106 | 107, _ => nerode_sep_r107 | 108, _ => nerode_sep_r108 | 109, _ => nerode_sep_r109
  | 110, _ => nerode_sep_r110 | 111, _ => nerode_sep_r111 | 112, _ => nerode_sep_r112
  | _ + 113, hbad => False.elim (by omega)
private theorem out2d_trans_all {x : Nat} (hx : x < 95) : out2d_trans_idx_row x = true :=
  match x, hx with
  | 0, _ => out2d_trans_r0 | 1, _ => out2d_trans_r1 | 2, _ => out2d_trans_r2 | 3, _ => out2d_trans_r3 | 4, _ => out2d_trans_r4
  | 5, _ => out2d_trans_r5 | 6, _ => out2d_trans_r6 | 7, _ => out2d_trans_r7 | 8, _ => out2d_trans_r8 | 9, _ => out2d_trans_r9
  | 10, _ => out2d_trans_r10 | 11, _ => out2d_trans_r11 | 12, _ => out2d_trans_r12 | 13, _ => out2d_trans_r13 | 14, _ => out2d_trans_r14
  | 15, _ => out2d_trans_r15 | 16, _ => out2d_trans_r16 | 17, _ => out2d_trans_r17 | 18, _ => out2d_trans_r18 | 19, _ => out2d_trans_r19
  | 20, _ => out2d_trans_r20 | 21, _ => out2d_trans_r21 | 22, _ => out2d_trans_r22 | 23, _ => out2d_trans_r23 | 24, _ => out2d_trans_r24
  | 25, _ => out2d_trans_r25 | 26, _ => out2d_trans_r26 | 27, _ => out2d_trans_r27 | 28, _ => out2d_trans_r28 | 29, _ => out2d_trans_r29
  | 30, _ => out2d_trans_r30 | 31, _ => out2d_trans_r31 | 32, _ => out2d_trans_r32 | 33, _ => out2d_trans_r33 | 34, _ => out2d_trans_r34
  | 35, _ => out2d_trans_r35 | 36, _ => out2d_trans_r36 | 37, _ => out2d_trans_r37 | 38, _ => out2d_trans_r38 | 39, _ => out2d_trans_r39
  | 40, _ => out2d_trans_r40 | 41, _ => out2d_trans_r41 | 42, _ => out2d_trans_r42 | 43, _ => out2d_trans_r43 | 44, _ => out2d_trans_r44
  | 45, _ => out2d_trans_r45 | 46, _ => out2d_trans_r46 | 47, _ => out2d_trans_r47 | 48, _ => out2d_trans_r48 | 49, _ => out2d_trans_r49
  | 50, _ => out2d_trans_r50 | 51, _ => out2d_trans_r51 | 52, _ => out2d_trans_r52 | 53, _ => out2d_trans_r53 | 54, _ => out2d_trans_r54
  | 55, _ => out2d_trans_r55 | 56, _ => out2d_trans_r56 | 57, _ => out2d_trans_r57 | 58, _ => out2d_trans_r58 | 59, _ => out2d_trans_r59
  | 60, _ => out2d_trans_r60 | 61, _ => out2d_trans_r61 | 62, _ => out2d_trans_r62 | 63, _ => out2d_trans_r63 | 64, _ => out2d_trans_r64
  | 65, _ => out2d_trans_r65 | 66, _ => out2d_trans_r66 | 67, _ => out2d_trans_r67 | 68, _ => out2d_trans_r68 | 69, _ => out2d_trans_r69
  | 70, _ => out2d_trans_r70 | 71, _ => out2d_trans_r71 | 72, _ => out2d_trans_r72 | 73, _ => out2d_trans_r73 | 74, _ => out2d_trans_r74
  | 75, _ => out2d_trans_r75 | 76, _ => out2d_trans_r76 | 77, _ => out2d_trans_r77 | 78, _ => out2d_trans_r78 | 79, _ => out2d_trans_r79
  | 80, _ => out2d_trans_r80 | 81, _ => out2d_trans_r81 | 82, _ => out2d_trans_r82 | 83, _ => out2d_trans_r83 | 84, _ => out2d_trans_r84
  | 85, _ => out2d_trans_r85 | 86, _ => out2d_trans_r86 | 87, _ => out2d_trans_r87 | 88, _ => out2d_trans_r88 | 89, _ => out2d_trans_r89
  | 90, _ => out2d_trans_r90 | 91, _ => out2d_trans_r91 | 92, _ => out2d_trans_r92 | 93, _ => out2d_trans_r93 | 94, _ => out2d_trans_r94
  | _ + 95, hbad => False.elim (by omega)
private theorem ob2_idx_all {x : Nat} (hx : x < 95) : ob2_idx_row x = true :=
  match x, hx with
  | 0, _ => ob2_r0 | 1, _ => ob2_r1 | 2, _ => ob2_r2 | 3, _ => ob2_r3 | 4, _ => ob2_r4
  | 5, _ => ob2_r5 | 6, _ => ob2_r6 | 7, _ => ob2_r7 | 8, _ => ob2_r8 | 9, _ => ob2_r9
  | 10, _ => ob2_r10 | 11, _ => ob2_r11 | 12, _ => ob2_r12 | 13, _ => ob2_r13 | 14, _ => ob2_r14
  | 15, _ => ob2_r15 | 16, _ => ob2_r16 | 17, _ => ob2_r17 | 18, _ => ob2_r18 | 19, _ => ob2_r19
  | 20, _ => ob2_r20 | 21, _ => ob2_r21 | 22, _ => ob2_r22 | 23, _ => ob2_r23 | 24, _ => ob2_r24
  | 25, _ => ob2_r25 | 26, _ => ob2_r26 | 27, _ => ob2_r27 | 28, _ => ob2_r28 | 29, _ => ob2_r29
  | 30, _ => ob2_r30 | 31, _ => ob2_r31 | 32, _ => ob2_r32 | 33, _ => ob2_r33 | 34, _ => ob2_r34
  | 35, _ => ob2_r35 | 36, _ => ob2_r36 | 37, _ => ob2_r37 | 38, _ => ob2_r38 | 39, _ => ob2_r39
  | 40, _ => ob2_r40 | 41, _ => ob2_r41 | 42, _ => ob2_r42 | 43, _ => ob2_r43 | 44, _ => ob2_r44
  | 45, _ => ob2_r45 | 46, _ => ob2_r46 | 47, _ => ob2_r47 | 48, _ => ob2_r48 | 49, _ => ob2_r49
  | 50, _ => ob2_r50 | 51, _ => ob2_r51 | 52, _ => ob2_r52 | 53, _ => ob2_r53 | 54, _ => ob2_r54
  | 55, _ => ob2_r55 | 56, _ => ob2_r56 | 57, _ => ob2_r57 | 58, _ => ob2_r58 | 59, _ => ob2_r59
  | 60, _ => ob2_r60 | 61, _ => ob2_r61 | 62, _ => ob2_r62 | 63, _ => ob2_r63 | 64, _ => ob2_r64
  | 65, _ => ob2_r65 | 66, _ => ob2_r66 | 67, _ => ob2_r67 | 68, _ => ob2_r68 | 69, _ => ob2_r69
  | 70, _ => ob2_r70 | 71, _ => ob2_r71 | 72, _ => ob2_r72 | 73, _ => ob2_r73 | 74, _ => ob2_r74
  | 75, _ => ob2_r75 | 76, _ => ob2_r76 | 77, _ => ob2_r77 | 78, _ => ob2_r78 | 79, _ => ob2_r79
  | 80, _ => ob2_r80 | 81, _ => ob2_r81 | 82, _ => ob2_r82 | 83, _ => ob2_r83 | 84, _ => ob2_r84
  | 85, _ => ob2_r85 | 86, _ => ob2_r86 | 87, _ => ob2_r87 | 88, _ => ob2_r88 | 89, _ => ob2_r89
  | 90, _ => ob2_r90 | 91, _ => ob2_r91 | 92, _ => ob2_r92 | 93, _ => ob2_r93 | 94, _ => ob2_r94
  | _ + 95, hbad => False.elim (by omega)
private theorem ob3_idx_all {x : Nat} (hx : x < 95) : ob3_idx_row x = true :=
  match x, hx with
  | 0, _ => ob3_r0 | 1, _ => ob3_r1 | 2, _ => ob3_r2 | 3, _ => ob3_r3 | 4, _ => ob3_r4
  | 5, _ => ob3_r5 | 6, _ => ob3_r6 | 7, _ => ob3_r7 | 8, _ => ob3_r8 | 9, _ => ob3_r9
  | 10, _ => ob3_r10 | 11, _ => ob3_r11 | 12, _ => ob3_r12 | 13, _ => ob3_r13 | 14, _ => ob3_r14
  | 15, _ => ob3_r15 | 16, _ => ob3_r16 | 17, _ => ob3_r17 | 18, _ => ob3_r18 | 19, _ => ob3_r19
  | 20, _ => ob3_r20 | 21, _ => ob3_r21 | 22, _ => ob3_r22 | 23, _ => ob3_r23 | 24, _ => ob3_r24
  | 25, _ => ob3_r25 | 26, _ => ob3_r26 | 27, _ => ob3_r27 | 28, _ => ob3_r28 | 29, _ => ob3_r29
  | 30, _ => ob3_r30 | 31, _ => ob3_r31 | 32, _ => ob3_r32 | 33, _ => ob3_r33 | 34, _ => ob3_r34
  | 35, _ => ob3_r35 | 36, _ => ob3_r36 | 37, _ => ob3_r37 | 38, _ => ob3_r38 | 39, _ => ob3_r39
  | 40, _ => ob3_r40 | 41, _ => ob3_r41 | 42, _ => ob3_r42 | 43, _ => ob3_r43 | 44, _ => ob3_r44
  | 45, _ => ob3_r45 | 46, _ => ob3_r46 | 47, _ => ob3_r47 | 48, _ => ob3_r48 | 49, _ => ob3_r49
  | 50, _ => ob3_r50 | 51, _ => ob3_r51 | 52, _ => ob3_r52 | 53, _ => ob3_r53 | 54, _ => ob3_r54
  | 55, _ => ob3_r55 | 56, _ => ob3_r56 | 57, _ => ob3_r57 | 58, _ => ob3_r58 | 59, _ => ob3_r59
  | 60, _ => ob3_r60 | 61, _ => ob3_r61 | 62, _ => ob3_r62 | 63, _ => ob3_r63 | 64, _ => ob3_r64
  | 65, _ => ob3_r65 | 66, _ => ob3_r66 | 67, _ => ob3_r67 | 68, _ => ob3_r68 | 69, _ => ob3_r69
  | 70, _ => ob3_r70 | 71, _ => ob3_r71 | 72, _ => ob3_r72 | 73, _ => ob3_r73 | 74, _ => ob3_r74
  | 75, _ => ob3_r75 | 76, _ => ob3_r76 | 77, _ => ob3_r77 | 78, _ => ob3_r78 | 79, _ => ob3_r79
  | 80, _ => ob3_r80 | 81, _ => ob3_r81 | 82, _ => ob3_r82 | 83, _ => ob3_r83 | 84, _ => ob3_r84
  | 85, _ => ob3_r85 | 86, _ => ob3_r86 | 87, _ => ob3_r87 | 88, _ => ob3_r88 | 89, _ => ob3_r89
  | 90, _ => ob3_r90 | 91, _ => ob3_r91 | 92, _ => ob3_r92 | 93, _ => ob3_r93 | 94, _ => ob3_r94
  | _ + 95, hbad => False.elim (by omega)
private theorem ob4_idx_all {x : Nat} (hx : x < 95) : ob4_idx_row x = true :=
  match x, hx with
  | 0, _ => ob4_r0 | 1, _ => ob4_r1 | 2, _ => ob4_r2 | 3, _ => ob4_r3 | 4, _ => ob4_r4
  | 5, _ => ob4_r5 | 6, _ => ob4_r6 | 7, _ => ob4_r7 | 8, _ => ob4_r8 | 9, _ => ob4_r9
  | 10, _ => ob4_r10 | 11, _ => ob4_r11 | 12, _ => ob4_r12 | 13, _ => ob4_r13 | 14, _ => ob4_r14
  | 15, _ => ob4_r15 | 16, _ => ob4_r16 | 17, _ => ob4_r17 | 18, _ => ob4_r18 | 19, _ => ob4_r19
  | 20, _ => ob4_r20 | 21, _ => ob4_r21 | 22, _ => ob4_r22 | 23, _ => ob4_r23 | 24, _ => ob4_r24
  | 25, _ => ob4_r25 | 26, _ => ob4_r26 | 27, _ => ob4_r27 | 28, _ => ob4_r28 | 29, _ => ob4_r29
  | 30, _ => ob4_r30 | 31, _ => ob4_r31 | 32, _ => ob4_r32 | 33, _ => ob4_r33 | 34, _ => ob4_r34
  | 35, _ => ob4_r35 | 36, _ => ob4_r36 | 37, _ => ob4_r37 | 38, _ => ob4_r38 | 39, _ => ob4_r39
  | 40, _ => ob4_r40 | 41, _ => ob4_r41 | 42, _ => ob4_r42 | 43, _ => ob4_r43 | 44, _ => ob4_r44
  | 45, _ => ob4_r45 | 46, _ => ob4_r46 | 47, _ => ob4_r47 | 48, _ => ob4_r48 | 49, _ => ob4_r49
  | 50, _ => ob4_r50 | 51, _ => ob4_r51 | 52, _ => ob4_r52 | 53, _ => ob4_r53 | 54, _ => ob4_r54
  | 55, _ => ob4_r55 | 56, _ => ob4_r56 | 57, _ => ob4_r57 | 58, _ => ob4_r58 | 59, _ => ob4_r59
  | 60, _ => ob4_r60 | 61, _ => ob4_r61 | 62, _ => ob4_r62 | 63, _ => ob4_r63 | 64, _ => ob4_r64
  | 65, _ => ob4_r65 | 66, _ => ob4_r66 | 67, _ => ob4_r67 | 68, _ => ob4_r68 | 69, _ => ob4_r69
  | 70, _ => ob4_r70 | 71, _ => ob4_r71 | 72, _ => ob4_r72 | 73, _ => ob4_r73 | 74, _ => ob4_r74
  | 75, _ => ob4_r75 | 76, _ => ob4_r76 | 77, _ => ob4_r77 | 78, _ => ob4_r78 | 79, _ => ob4_r79
  | 80, _ => ob4_r80 | 81, _ => ob4_r81 | 82, _ => ob4_r82 | 83, _ => ob4_r83 | 84, _ => ob4_r84
  | 85, _ => ob4_r85 | 86, _ => ob4_r86 | 87, _ => ob4_r87 | 88, _ => ob4_r88 | 89, _ => ob4_r89
  | 90, _ => ob4_r90 | 91, _ => ob4_r91 | 92, _ => ob4_r92 | 93, _ => ob4_r93 | 94, _ => ob4_r94
  | _ + 95, hbad => False.elim (by omega)

/-! ## 1. `StateP` & `PH` Bridges and Soundness of `A_P` -/

theorem pIdx_ofPIdx {i : Nat} (hi : i < 39) : pIdx (ofPIdx i) = i :=
  Nat.eq_of_beq_eq_true (checkNat1_sound 39 _ pIdx_ofPIdx_chk hi)

theorem pIdx_deltaP (a b : StateP) : pIdx (deltaP a b) = dpIdx (pIdx a) (pIdx b) ∧ dpIdx (pIdx a) (pIdx b) < 39 := by
  have h := checkNat2_sound 39 39 _ dp_bridge_chk (pIdx_lt_39 a) (pIdx_lt_39 b)
  rw [ofPIdx_pIdx, ofPIdx_pIdx] at h
  exact ⟨Nat.eq_of_beq_eq_true (and_left h), Nat.le_of_ble_eq_true (and_right h)⟩

theorem deltaP_s_law (x y z : StateP) : deltaP (deltaP (deltaP .p0 x) y) z = deltaP (deltaP x z) (deltaP y z) := by
  have h := Nat.eq_of_beq_eq_true (checkNat2_sound 39 39 _ (dp_s_law_all (pIdx_lt_39 x)) (pIdx_lt_39 y) (pIdx_lt_39 z))
  have hL : pIdx (deltaP (deltaP (deltaP .p0 x) y) z) = dpIdx (dpIdx (dpIdx 0 (pIdx x)) (pIdx y)) (pIdx z) := by
    rw [(pIdx_deltaP _ z).1, (pIdx_deltaP _ y).1, (pIdx_deltaP .p0 x).1]; rfl
  have hR : pIdx (deltaP (deltaP x z) (deltaP y z)) = dpIdx (dpIdx (pIdx x) (pIdx z)) (dpIdx (pIdx y) (pIdx z)) := by
    rw [(pIdx_deltaP _ _).1, (pIdx_deltaP x z).1, (pIdx_deltaP y z).1]
  exact eq_of_beqP (Nat.beq_eq.mpr (hL.trans (h.trans hR.symm)))

theorem evalP_step {a b : Term} (hs : Step a b) : evalP a = evalP b := by
  induction hs with | root _ _ _ => exact deltaP_s_law _ _ _ | left _ ih => simp [evalP, ih] | right _ ih => simp [evalP, ih]
theorem evalP_reduces {a b : Term} (hr : Reduces a b) : evalP a = evalP b := by
  induction hr with | refl _ => rfl | next hs _ ih => exact (evalP_step hs).trans ih
theorem evalPH_step {a b : Term} (hs : Step a b) : evalPH a = evalPH b := Prod.ext (evalP_step hs) (evalHN_step hs)
theorem evalPH_reduces {a b : Term} (hr : Reduces a b) : evalPH a = evalPH b := Prod.ext (evalP_reduces hr) (evalHN_reduces hr)

private theorem dp_meta_unpack {x y : Nat} (hx : x < 39) (hy : y < 39) :
    Nat.beq (dpIdx 37 y) 37 = true ∧
    Nat.beq (dpIdx x 37) 37 = true ∧
    (!Nat.beq (dpIdx 0 x) 37) = (!Nat.beq x 37) ∧
    (!Nat.beq (dpIdx (dpIdx 0 x) y) 37) = (!Nat.beq x 37 && !Nat.beq y 37) ∧
    (!Nat.beq (dpIdx x y) 0) = true ∧
    Nat.beq (dpIdx 29 y) 37 = true ∧
    (!Nat.beq (dpIdx 0 x) 1 || Nat.beq x 0) = true ∧
    (!Nat.beq (dpIdx (dpIdx 0 x) y) 1) = true ∧
    (!isZachosPIdx (dpIdx 0 x)) = true ∧
    (!Nat.beq (dpIdx (dpIdx 0 x) y) 14 || (Nat.beq x 1 && Nat.beq y 1)) = true ∧
    (!Nat.beq (dpIdx (dpIdx 0 x) y) 32 || (Nat.beq x 0 && isZachosPIdx y)) = true ∧
    (Nat.beq x 37 || Nat.beq y 37 || Nat.beq (dpIdx (dpIdx 0 x) y) 37 || isS2PTree.lookup (dpIdx (dpIdx 0 x) y)) = true := by
  have h := checkNat2_sound 39 39 _ dp_meta_chk hx hy
  have ⟨p10, c11⟩ := (Bool.and_eq_true _ _).mp h
  have ⟨p9, c10⟩ := (Bool.and_eq_true _ _).mp p10
  have ⟨p8, c9⟩ := (Bool.and_eq_true _ _).mp p9
  have ⟨p7, c8⟩ := (Bool.and_eq_true _ _).mp p8
  have ⟨p6, c7⟩ := (Bool.and_eq_true _ _).mp p7
  have ⟨p5, c6⟩ := (Bool.and_eq_true _ _).mp p6
  have ⟨p4, c5⟩ := (Bool.and_eq_true _ _).mp p5
  have ⟨p3, c4⟩ := (Bool.and_eq_true _ _).mp p4
  have ⟨p2, c3⟩ := (Bool.and_eq_true _ _).mp p3
  have ⟨p1, c2⟩ := (Bool.and_eq_true _ _).mp p2
  have ⟨c0, c1⟩ := (Bool.and_eq_true _ _).mp p1
  exact ⟨c0, c1, eq_of_boolBeq c2, eq_of_boolBeq c3, c4, c5, c6, c7, c8, c9, c10, c11⟩

theorem deltaP_sink (x : StateP) : deltaP .p37 x = .p37 ∧ deltaP x .p37 = .p37 := by
  have ⟨hL, hR, _⟩ := dp_meta_unpack (pIdx_lt_39 x) (pIdx_lt_39 x)
  refine ⟨eq_of_beqP (by unfold beqP; rw [(pIdx_deltaP .p37 x).1]; exact hL),
          eq_of_beqP (by unfold beqP; rw [(pIdx_deltaP x .p37).1]; exact hR)⟩

theorem isZachosP_eq_idx (q : StateP) : isZachosP q = isZachosPIdx (pIdx q) := by cases q <;> rfl

theorem ofPhIdx_phIdx {q : PH} (hr : isReachPH q = true) : ofPhIdx (phIdx q) = q ∧ phIdx q < 113 := by
  rcases q with ⟨p, h⟩
  have hp := checkNat2_sound 39 35 _ phIdx_sound_chk (pIdx_lt_39 p) (hnIdx_lt_35 h)
  dsimp only [] at hp
  rw [ofPIdx_pIdx, ofHnIdx_hnIdx] at hp
  have hlt : phIdx (p, h) < 113 := Nat.le_of_ble_eq_true hr
  rcases (Bool.or_eq_true _ _).mp hp with h127 | hok
  · have h127' := Nat.eq_of_beq_eq_true h127; exact False.elim (by omega)
  · exact ⟨eq_of_beqPH (and_right hok), hlt⟩

theorem ofPhIdx_spec {i : Nat} (hi : i < 113) :
    phIdx (ofPhIdx i) = i ∧ isReachPH (ofPhIdx i) = true ∧
    (!beqP (ofPhIdx i).1 .p37) = isAccIdx i ∧
    isHN34PH (ofPhIdx i) = isHN34Idx i ∧
    isZachosPH (ofPhIdx i) = isZachosIdx i ∧
    (isAccIdx i = true → isAccIdx (dphIdx 0 i) = true ∧ kindIdx (dphIdx 0 i) = 1) := by
  have h := checkNat1_sound 113 _ reach_1d_chk hi
  have h1 := Nat.eq_of_beq_eq_true (and_left (and_left (and_left (and_left h))))
  have h2 := eq_of_boolBeq (and_right (and_left (and_left (and_left h))))
  have h3 := eq_of_boolBeq (and_right (and_left (and_left h)))
  have h4 := eq_of_boolBeq (and_right (and_left h))
  have h5 := and_right h
  have hr : isReachPH (ofPhIdx i) = true := by unfold isReachPH isReachIdx; rw [h1]; exact Nat.ble_eq.mpr hi
  refine ⟨h1, hr, h2, h3, h4, fun ha => ?_⟩
  have hk := imp_bool ha h5
  exact ⟨and_left hk, Nat.eq_of_beq_eq_true (and_right hk)⟩

theorem reach_1d_props {q : PH} (hr : isReachPH q = true) :
    ofPhIdx (phIdx q) = q ∧ phIdx q < 113 ∧
    (!beqP q.1 .p37) = isAccIdx (phIdx q) ∧
    isHN34PH q = isHN34Idx (phIdx q) ∧
    isZachosPH q = isZachosIdx (phIdx q) ∧
    (isAccPH q = true → isAccIdx (dphIdx 0 (phIdx q)) = true ∧ kindIdx (dphIdx 0 (phIdx q)) = 1) := by
  have ⟨hof, hlt⟩ := ofPhIdx_phIdx hr
  have hs := ofPhIdx_spec hlt
  rw [hof] at hs
  exact ⟨hof, hlt, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2⟩

theorem phIdx_lt_113 {q : PH} (hr : isReachPH q = true) : phIdx q < 113 := (reach_1d_props hr).2.1
theorem phIdx_lt_95  {q : PH} (ha : isAccPH q = true) : phIdx q < 95 := Nat.le_of_ble_eq_true ha
theorem isReachPH_of_isAccPH {q : PH} (ha : isAccPH q = true) : isReachPH q = true := by
  have h95 := phIdx_lt_95 ha; unfold isReachPH isReachIdx; exact Nat.ble_eq.mpr (by omega)

theorem isReachPH_deltaPH_and_idx {a b : PH} (ha : isReachPH a = true) (hb : isReachPH b = true) :
    isReachPH (deltaPH a b) = true ∧ phIdx (deltaPH a b) = dphIdx (phIdx a) (phIdx b) := by
  have ⟨hofa, hlta⟩ := ofPhIdx_phIdx ha
  have ⟨hofb, hltb⟩ := ofPhIdx_phIdx hb
  have h := checkNat1_sound 113 _ (dph_bridge_all hlta) hltb
  rw [hofa, hofb] at h
  exact ⟨and_left h, Nat.eq_of_beq_eq_true (and_right h)⟩

theorem isReachPH_deltaPH {a b : PH} (ha : isReachPH a = true) (hb : isReachPH b = true) : isReachPH (deltaPH a b) = true :=
  (isReachPH_deltaPH_and_idx ha hb).1
theorem phIdx_deltaPH {a b : PH} (ha : isReachPH a = true) (hb : isReachPH b = true) : phIdx (deltaPH a b) = dphIdx (phIdx a) (phIdx b) :=
  (isReachPH_deltaPH_and_idx ha hb).2

theorem evalPH_isReach {t : Term} (hv : noVars t = true) : isReachPH (evalPH t) = true := by
  induction t with
  | s => rfl | var _ => cases hv
  | app a b iha ihb =>
    have ⟨hva, hvb⟩ := (Bool.and_eq_true _ _).mp hv
    exact isReachPH_deltaPH (iha hva) (ihb hvb)

theorem isAccPH_evalPH_iff {t : Term} (hv : noVars t = true) : isAccPH (evalPH t) = true ↔ evalP t ≠ .p37 := by
  have hp := (reach_1d_props (evalPH_isReach hv)).2.2.1
  change isAccIdx (phIdx (evalPH t)) = true ↔ evalP t ≠ .p37
  rw [← hp]
  change (!beqP (evalP t) .p37) = true ↔ evalP t ≠ .p37
  cases hb : beqP (evalP t) .p37 with
  | false => exact ⟨fun _ => ne_of_beqP_false hb, fun _ => rfl⟩
  | true => exact ⟨(fun h => by cases h), fun hne => False.elim (hne (eq_of_beqP hb))⟩

theorem evalHN_eq_hn34_implies_evalP_eq_p37 {t : Term} (hv : noVars t = true) (h34 : evalHN t = .hn34) : evalP t = .p37 := by
  have hr := evalPH_isReach hv
  have hp := reach_1d_props hr
  have hi34 : isHN34Idx (phIdx (evalPH t)) = true := by
    rw [← hp.2.2.2.1]; unfold isHN34PH; change beq_StateHN (evalHN t) .hn34 = true; rw [h34]; rfl
  have hi112 : phIdx (evalPH t) = 112 := Nat.eq_of_beq_eq_true hi34
  have hacc_f : (!beqP (evalP t) .p37) = false := by
    change (!beqP (evalPH t).1 .p37) = false; rw [hp.2.2.1, hi112]; rfl
  cases hb : beqP (evalP t) .p37 with
  | true => exact eq_of_beqP hb
  | false => rw [hb] at hacc_f; cases hacc_f

theorem hasBotWithin_implies_evalP_p37 {d : Nat} {t : Term} (hv : noVars t = true) (hb : HasBotWithin d t) : evalP t = .p37 := by
  induction hb with
  | bot_div hno => exact evalHN_eq_hn34_implies_evalP_eq_p37 hv (closed_not_hasHNF_evalHN_hn34 hv hno)
  | @bot_s1 _ _ a hr _ ih =>
    have hva := ((Bool.and_eq_true _ _).mp (noVars_reduces hr hv)).2
    rw [evalP_reduces hr]; change deltaP .p0 (evalP a) = .p37; rw [ih hva]; rfl
  | @bot_s2_l _ _ a b hr _ ih =>
    have ⟨hsa, _⟩ := (Bool.and_eq_true _ _).mp (noVars_reduces hr hv)
    have hva := ((Bool.and_eq_true _ _).mp hsa).2
    rw [evalP_reduces hr]; change deltaP (deltaP .p0 (evalP a)) (evalP b) = .p37; rw [ih hva]; exact (deltaP_sink _).1
  | @bot_s2_r _ _ a b hr _ ih =>
    have hvb := ((Bool.and_eq_true _ _).mp (noVars_reduces hr hv)).2
    rw [evalP_reduces hr]; change deltaP (deltaP .p0 (evalP a)) (evalP b) = .p37; rw [ih hvb]; exact (deltaP_sink _).2

/-- **Soundness of `A_P` (Direction 1 of Open Question 5)**. -/
theorem evalP_ne_p37_implies_productive {t : Term} (hv : noVars t = true) (hacc : evalP t ≠ .p37) : Productive t :=
  fun ⟨_, hb⟩ => hacc (hasBotWithin_implies_evalP_p37 hv hb)

theorem deltaPH_ne_ph0 (x y : PH) : deltaPH x y ≠ ph0 := by
  intro h; have hp : deltaP x.1 y.1 = .p0 := congrArg Prod.fst h
  have ⟨_, _, _, _, hne0, _⟩ := dp_meta_unpack (pIdx_lt_39 x.1) (pIdx_lt_39 y.1)
  have heq0 : dpIdx (pIdx x.1) (pIdx y.1) = 0 := by have hd := (pIdx_deltaP x.1 y.1).1; rw [hp] at hd; exact hd.symm
  rw [heq0] at hne0; cases hne0

/-! ## 2. Exact 113-State Myhill–Nerode Minimality of `PH` (17 Closed Contexts) -/

theorem witTerm_spec {i : Nat} (hi : i < 113) : noVars (witTerm i) = true ∧ phIdx (evalPH (witTerm i)) = i := by
  have h := checkNat1_sound 113 _ witTerm_chk hi
  exact ⟨and_left h, Nat.eq_of_beq_eq_true (and_right h)⟩

private theorem applyCtxOps_spec : ∀ (ops : List (Bool × Nat)) {t : Term},
    allNat (fun x => Nat.ble (x + 1) 113) (ops.map Prod.snd) = true →
    noVars t = true →
    noVars (applyCtxOps ops t) = true ∧ phIdx (evalPH (applyCtxOps ops t)) = evalCtxOpsIdx ops (phIdx (evalPH t))
  | [], _, _, hv => ⟨hv, rfl⟩
  | (true, r) :: rest, t, hall, hv => by
    have ⟨hr113_b, hrest⟩ := (Bool.and_eq_true _ _).mp hall
    have hr113 : r < 113 := Nat.le_of_ble_eq_true hr113_b
    have ⟨hvw, hiw⟩ := witTerm_spec hr113
    have hv' : noVars (t ⋅ witTerm r) = true := (Bool.and_eq_true _ _).mpr ⟨hv, hvw⟩
    have ⟨hv_fin, hi_fin⟩ := applyCtxOps_spec rest hrest hv'
    have hidx_step : phIdx (evalPH (t ⋅ witTerm r)) = dphIdx (phIdx (evalPH t)) r := by
      change phIdx (deltaPH (evalPH t) (evalPH (witTerm r))) = _
      rw [phIdx_deltaPH (evalPH_isReach hv) (evalPH_isReach hvw), hiw]
    rw [hidx_step] at hi_fin
    exact ⟨hv_fin, hi_fin⟩
  | (false, l) :: rest, t, hall, hv => by
    have ⟨hl113_b, hrest⟩ := (Bool.and_eq_true _ _).mp hall
    have hl113 : l < 113 := Nat.le_of_ble_eq_true hl113_b
    have ⟨hvw, hiw⟩ := witTerm_spec hl113
    have hv' : noVars (witTerm l ⋅ t) = true := (Bool.and_eq_true _ _).mpr ⟨hvw, hv⟩
    have ⟨hv_fin, hi_fin⟩ := applyCtxOps_spec rest hrest hv'
    have hidx_step : phIdx (evalPH (witTerm l ⋅ t)) = dphIdx l (phIdx (evalPH t)) := by
      change phIdx (deltaPH (evalPH (witTerm l)) (evalPH t)) = _
      rw [phIdx_deltaPH (evalPH_isReach hvw) (evalPH_isReach hv), hiw]
    rw [hidx_step] at hi_fin
    exact ⟨hv_fin, hi_fin⟩

private theorem applyCtxOps_congr {Q : Type} (evalQ : Term → Q) (δQ : Q → Q → Q)
    (hhom : ∀ a b : Term, evalQ (a ⋅ b) = δQ (evalQ a) (evalQ b)) :
    ∀ (ops : List (Bool × Nat)) {t1 t2 : Term}, evalQ t1 = evalQ t2 → evalQ (applyCtxOps ops t1) = evalQ (applyCtxOps ops t2)
  | [], _, _, heq => heq
  | (true, r) :: rest, t1, t2, heq => applyCtxOps_congr evalQ δQ hhom rest (by rw [hhom, hhom, heq])
  | (false, l) :: rest, t1, t2, heq => applyCtxOps_congr evalQ δQ hhom rest (by rw [hhom, hhom, heq])

/-! ## 3. Zachos Family `zachosG`, Canonical Productive Values (`PVal`), and `out2d` Invariant -/

def zachosT : Term := S ⋅ S
def zachosG : Nat → Term | 0 => S ⋅ zachosT ⋅ zachosT | k + 1 => zachosT ⋅ zachosG k

theorem noVars_zachosG : ∀ k : Nat, noVars (zachosG k) = true
  | 0 => rfl | k + 1 => (Bool.and_eq_true _ _).mpr ⟨rfl, noVars_zachosG k⟩
theorem evalP_zachosG_zero : evalP (zachosG 0) = .p14 := rfl
theorem evalHN_zachosG_zero : evalHN (zachosG 0) = .hn16 := rfl
theorem evalP_zachosG_succ : ∀ k : Nat, evalP (zachosG (k + 1)) = .p32
  | 0 => rfl | k + 1 => by change deltaP (evalP zachosT) (evalP (zachosG (k + 1))) = .p32; rw [evalP_zachosG_succ k]; rfl
theorem evalHN_zachosG_succ : ∀ k : Nat, evalHN (zachosG (k + 1)) = .hn13
  | 0 => rfl | k + 1 => by change deltaHN (evalHN zachosT) (evalHN (zachosG (k + 1))) = .hn13; rw [evalHN_zachosG_succ k]; rfl
theorem evalP_zachos_pair (m n : Nat) : evalP (zachosG m ⋅ zachosG n) = .p29 := by
  cases m <;> cases n <;> simp only [evalP, evalP_zachosG_zero, evalP_zachosG_succ] <;> rfl
theorem evalHN_zachos_pair (m n : Nat) :
    evalHN (zachosG m ⋅ zachosG n) = .hn23 ∨ evalHN (zachosG m ⋅ zachosG n) = .hn24 := by
  cases m <;> cases n <;> simp only [evalHN, evalHN_zachosG_zero, evalHN_zachosG_succ]
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem zachos_chain_hasBot : ∀ (n : Nat) {z w : Term},
    noVars z = true → noVars w = true → evalHN ((zachosG 0 ⋅ z) ⋅ w) = .hn34 → HasBot ((zachosG n ⋅ z) ⋅ w)
  | 0, z, w, hvz, hvw, h34 =>
    ⟨0, closed_evalHN_hn34_hasBot0 ((Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨noVars_zachosG 0, hvz⟩, hvw⟩) h34⟩
  | n + 1, z, w, hvz, hvw, h34 => by
    obtain ⟨d, hd⟩ := zachos_chain_hasBot n hvz hvw h34
    have hvzw : noVars (z ⋅ w) = true := (Bool.and_eq_true _ _).mpr ⟨hvz, hvw⟩
    have hvgnzw : noVars ((zachosG n ⋅ z) ⋅ w) = true := (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨noVars_zachosG n, hvz⟩, hvw⟩
    have hrhs := hasBotWithin_app_right hvzw hvgnzw hd
    have hred : Reduces ((zachosG (n + 1) ⋅ z) ⋅ w) ((z ⋅ w) ⋅ ((zachosG n ⋅ z) ⋅ w)) :=
      Reduces.next (Step.left (Step.root S (zachosG n) z)) (Reduces.next (Step.root z (zachosG n ⋅ z) w) (Reduces.refl _))
    exact ⟨d + 1, hasBotWithin_backward_reduces hred hrhs⟩

theorem hasBot_zachos_succ (k n : Nat) {z : Term} (hvz : noVars z = true) :
    HasBot ((zachosG (k + 1) ⋅ zachosG n) ⋅ z) := by
  let w := (zachosG k ⋅ zachosG n) ⋅ z
  have hvw : noVars w = true := (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨noVars_zachosG k, noVars_zachosG n⟩, hvz⟩
  have hchk := checkNat1_sound 35 _ zachos_hn_chk (hnIdx_lt_35 (evalHN z))
  have hc1 := and_left (and_left (and_left hchk))
  have hc2 := and_right (and_left (and_left hchk))
  have hc3 := and_right (and_left hchk)
  have hc4 := and_right hchk
  have hw_idx : hnIdx (evalHN w) = 34 ∨ hnIdx (evalHN w) = 23 := by
    change hnIdx (deltaHN (evalHN (zachosG k ⋅ zachosG n)) (evalHN z)) = 34 ∨
           hnIdx (deltaHN (evalHN (zachosG k ⋅ zachosG n)) (evalHN z)) = 23
    rcases evalHN_zachos_pair k n with h23 | h24
    · rw [h23, (hnIdx_deltaHN .hn23 _).1]; change dhnIdx 23 (hnIdx (evalHN z)) = 34 ∨ dhnIdx 23 (hnIdx (evalHN z)) = 23
      rcases (Bool.or_eq_true _ _).mp hc1 with hL | hR
      · exact Or.inl (Nat.eq_of_beq_eq_true hL)
      · exact Or.inr (Nat.eq_of_beq_eq_true hR)
    · rw [h24, (hnIdx_deltaHN .hn24 _).1]; change dhnIdx 24 (hnIdx (evalHN z)) = 34 ∨ dhnIdx 24 (hnIdx (evalHN z)) = 23
      rcases (Bool.or_eq_true _ _).mp hc2 with hL | hR
      · exact Or.inl (Nat.eq_of_beq_eq_true hL)
      · exact Or.inr (Nat.eq_of_beq_eq_true hR)
  have h0_34 : evalHN ((zachosG 0 ⋅ z) ⋅ w) = .hn34 := by
    apply eq_of_beq_StateHN; unfold beq_StateHN
    change Nat.beq (hnIdx (deltaHN (deltaHN (evalHN (zachosG 0)) (evalHN z)) (evalHN w))) 34 = true
    rw [evalHN_zachosG_zero, (hnIdx_deltaHN _ (evalHN w)).1, (hnIdx_deltaHN .hn16 (evalHN z)).1]
    rcases hw_idx with hw34 | hw23
    · rw [hw34]; exact hc4
    · rw [hw23]; exact hc3
  obtain ⟨d, hd⟩ := zachos_chain_hasBot n hvz hvw h0_34
  have hred : Reduces ((zachosG (k + 1) ⋅ zachosG n) ⋅ z) ((zachosG n ⋅ z) ⋅ w) :=
    Reduces.next (Step.left (Step.root S (zachosG k) (zachosG n))) (Reduces.next (Step.root (zachosG n) (zachosG k ⋅ zachosG n) z) (Reduces.refl _))
  exact ⟨d, hasBotWithin_backward_reduces hred hd⟩

theorem hasBot_zachos_app (m n : Nat) {z : Term} (hvz : noVars z = true) :
    HasBot ((zachosG m ⋅ zachosG n) ⋅ z) := by
  cases m with
  | succ k => exact hasBot_zachos_succ k n hvz
  | zero =>
    obtain ⟨d, hd⟩ := hasBot_zachos_succ n (n + 1) hvz
    exact ⟨d, hasBotWithin_backward_reduces (Reduces.next (Step.left (Step.root zachosT zachosT (zachosG n))) (Reduces.refl _)) hd⟩

inductive PVal : Type where
  | s : PVal | s1 : PVal → PVal | s2 : PVal → PVal → PVal | zachos : Nat → Nat → PVal

namespace PVal
def toTerm : PVal → Term
  | .s => S | .s1 u => S ⋅ u.toTerm | .s2 a b => S ⋅ a.toTerm ⋅ b.toTerm | .zachos m n => zachosG m ⋅ zachosG n
def size : PVal → Nat
  | .s => 1 | .s1 u => u.size + 1 | .s2 a b => a.size + b.size + 1 | .zachos _ _ => 1
theorem size_pos : ∀ v : PVal, 1 ≤ v.size
  | .s => Nat.le_refl 1 | .s1 _ => Nat.le_add_left 1 _ | .s2 _ _ => Nat.le_add_left 1 _ | .zachos _ _ => Nat.le_refl 1
theorem noVars_toTerm : ∀ v : PVal, noVars v.toTerm = true
  | .s => rfl
  | .s1 u => (Bool.and_eq_true _ _).mpr ⟨rfl, noVars_toTerm u⟩
  | .s2 a b => (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨rfl, noVars_toTerm a⟩, noVars_toTerm b⟩
  | .zachos m n => (Bool.and_eq_true _ _).mpr ⟨noVars_zachosG m, noVars_zachosG n⟩

theorem evalP_ne_p37 : ∀ v : PVal, evalP v.toTerm ≠ .p37
  | .s => ne_of_beqP_false rfl
  | .s1 u => by
    intro h37; change deltaP .p0 (evalP u.toTerm) = .p37 at h37
    have ⟨_, _, hiff, _⟩ := dp_meta_unpack (pIdx_lt_39 (evalP u.toTerm)) (by decide : 0 < 39)
    have hs37 : dpIdx 0 (pIdx (evalP u.toTerm)) = 37 := by
      have hd := (pIdx_deltaP .p0 (evalP u.toTerm)).1; rw [h37] at hd; exact hd.symm
    rw [hs37] at hiff
    cases hc : Nat.beq (pIdx (evalP u.toTerm)) 37 with
    | false => rw [hc] at hiff; cases hiff
    | true => exact evalP_ne_p37 u (eq_of_beqP hc)
  | .s2 a b => by
    intro h37; change deltaP (deltaP .p0 (evalP a.toTerm)) (evalP b.toTerm) = .p37 at h37
    have ⟨_, _, _, hiff, _⟩ := dp_meta_unpack (pIdx_lt_39 (evalP a.toTerm)) (pIdx_lt_39 (evalP b.toTerm))
    have hs37 : dpIdx (dpIdx 0 (pIdx (evalP a.toTerm))) (pIdx (evalP b.toTerm)) = 37 := by
      have hd := (pIdx_deltaP (deltaP .p0 (evalP a.toTerm)) (evalP b.toTerm)).1
      rw [(pIdx_deltaP .p0 _).1, h37] at hd; exact hd.symm
    rw [hs37] at hiff
    cases hca : Nat.beq (pIdx (evalP a.toTerm)) 37 with
    | true => exact evalP_ne_p37 a (eq_of_beqP hca)
    | false =>
      cases hcb : Nat.beq (pIdx (evalP b.toTerm)) 37 with
      | true => exact evalP_ne_p37 b (eq_of_beqP hcb)
      | false => rw [hca, hcb] at hiff; cases hiff
  | .zachos m n => by rw [toTerm, evalP_zachos_pair]; exact ne_of_beqP_false rfl

theorem isAccPH_toTerm (v : PVal) : isAccPH (evalPH v.toTerm) = true :=
  (isAccPH_evalPH_iff (noVars_toTerm v)).mpr (evalP_ne_p37 v)
end PVal

theorem deltaP_p29_sink (b : StateP) : deltaP .p29 b = .p37 := by
  have ⟨_, _, _, _, _, h29, _⟩ := dp_meta_unpack (by decide : 0 < 39) (pIdx_lt_39 b)
  exact eq_of_beqP (by unfold beqP; rw [(pIdx_deltaP .p29 b).1]; exact h29)

theorem pval_eq_s_of_p0 : ∀ (v : PVal), evalP v.toTerm = .p0 → v = .s
  | .s, _ => rfl
  | .s1 u, h => False.elim (by
    change deltaP .p0 (evalP u.toTerm) = .p0 at h
    have ⟨_, _, _, _, hne, _⟩ := dp_meta_unpack (by decide : 0 < 39) (pIdx_lt_39 (evalP u.toTerm))
    have heq : dpIdx 0 (pIdx (evalP u.toTerm)) = 0 := by
      have hd := (pIdx_deltaP .p0 (evalP u.toTerm)).1; rw [h] at hd; exact hd.symm
    rw [heq] at hne; cases hne)
  | .s2 a b, h => False.elim (by
    change deltaP (evalP (S ⋅ a.toTerm)) (evalP b.toTerm) = .p0 at h
    have ⟨_, _, _, _, hne, _⟩ := dp_meta_unpack (pIdx_lt_39 (evalP (S ⋅ a.toTerm))) (pIdx_lt_39 (evalP b.toTerm))
    have heq : dpIdx (pIdx (evalP (S ⋅ a.toTerm))) (pIdx (evalP b.toTerm)) = 0 := by
      have hd := (pIdx_deltaP (evalP (S ⋅ a.toTerm)) (evalP b.toTerm)).1; rw [h] at hd; exact hd.symm
    rw [heq] at hne; cases hne)
  | .zachos m n, h => by rw [PVal.toTerm, evalP_zachos_pair] at h; cases h

theorem pval_eq_s1s_of_p1 : ∀ (v : PVal), evalP v.toTerm = .p1 → v = .s1 .s
  | .s, h => by cases h
  | .s1 u, h => by
    change deltaP .p0 (evalP u.toTerm) = .p1 at h
    have ⟨_, _, _, _, _, _, hc, _⟩ := dp_meta_unpack (pIdx_lt_39 (evalP u.toTerm)) (by decide : 0 < 39)
    have heq : dpIdx 0 (pIdx (evalP u.toTerm)) = 1 := by
      have hd := (pIdx_deltaP .p0 (evalP u.toTerm)).1; rw [h] at hd; exact hd.symm
    rw [heq] at hc
    change beqP (evalP u.toTerm) .p0 = true at hc
    exact congrArg PVal.s1 (pval_eq_s_of_p0 u (eq_of_beqP hc))
  | .s2 a b, h => False.elim (by
    change deltaP (deltaP .p0 (evalP a.toTerm)) (evalP b.toTerm) = .p1 at h
    have ⟨_, _, _, _, _, _, _, hc, _⟩ := dp_meta_unpack (pIdx_lt_39 (evalP a.toTerm)) (pIdx_lt_39 (evalP b.toTerm))
    have heq : dpIdx (dpIdx 0 (pIdx (evalP a.toTerm))) (pIdx (evalP b.toTerm)) = 1 := by
      have hd := (pIdx_deltaP (deltaP .p0 (evalP a.toTerm)) (evalP b.toTerm)).1
      rw [(pIdx_deltaP .p0 _).1, h] at hd; exact hd.symm
    rw [heq] at hc; cases hc)
  | .zachos m n, h => by rw [PVal.toTerm, evalP_zachos_pair] at h; cases h

def pvalZachosIdx : PVal → Nat | .s2 .s b => pvalZachosIdx b + 1 | _ => 0

theorem pvalZachosIdx_spec : ∀ (v : PVal), isZachosP (evalP v.toTerm) = true → v.toTerm = zachosG (pvalZachosIdx v)
  | .s, h => by cases h
  | .s1 u, h => False.elim (by
    have ⟨_, _, _, _, _, _, _, _, hc, _⟩ := dp_meta_unpack (pIdx_lt_39 (evalP u.toTerm)) (by decide : 0 < 39)
    change isZachosP (deltaP .p0 (evalP u.toTerm)) = true at h
    rw [isZachosP_eq_idx, (pIdx_deltaP .p0 _).1] at h
    change isZachosPIdx (dpIdx 0 (pIdx (evalP u.toTerm))) = true at h
    rw [h] at hc; cases hc)
  | .zachos m n, h => by rw [PVal.toTerm, evalP_zachos_pair] at h; cases h
  | .s2 a b, h => by
    have ⟨_, _, _, _, _, _, _, _, _, hc14, hc32, _⟩ := dp_meta_unpack (pIdx_lt_39 (evalP a.toTerm)) (pIdx_lt_39 (evalP b.toTerm))
    change isZachosP (deltaP (deltaP .p0 (evalP a.toTerm)) (evalP b.toTerm)) = true at h
    have hd_eq : pIdx (deltaP (deltaP .p0 (evalP a.toTerm)) (evalP b.toTerm)) = dpIdx (dpIdx 0 (pIdx (evalP a.toTerm))) (pIdx (evalP b.toTerm)) := by
      rw [(pIdx_deltaP _ _).1, (pIdx_deltaP .p0 _).1]; rfl
    cases hd : deltaP (deltaP .p0 (evalP a.toTerm)) (evalP b.toTerm) <;> rw [hd] at h hd_eq <;> try cases h
    · have hb14 : Nat.beq (dpIdx (dpIdx 0 (pIdx (evalP a.toTerm))) (pIdx (evalP b.toTerm))) 14 = true := Nat.beq_eq.mpr hd_eq.symm
      have h14 := imp_bool hb14 hc14
      rw [pval_eq_s1s_of_p1 a (eq_of_beqP (and_left h14)), pval_eq_s1s_of_p1 b (eq_of_beqP (and_right h14))]; rfl
    · have hb32 : Nat.beq (dpIdx (dpIdx 0 (pIdx (evalP a.toTerm))) (pIdx (evalP b.toTerm))) 32 = true := Nat.beq_eq.mpr hd_eq.symm
      have h32 := imp_bool hb32 hc32
      have ha_s : a = .s := pval_eq_s_of_p0 a (eq_of_beqP (and_left h32))
      subst ha_s
      have hbz : isZachosP (evalP b.toTerm) = true := by rw [isZachosP_eq_idx]; exact and_right h32
      have ih := pvalZachosIdx_spec b hbz
      change S ⋅ S ⋅ b.toTerm = zachosT ⋅ zachosG (pvalZachosIdx b); rw [ih]; rfl

theorem isS2StateP_intro {a b : StateP} (ha : a ≠ .p37) (hb : b ≠ .p37) (hf : deltaP (deltaP .p0 a) b ≠ .p37) :
    isS2StateP (deltaP (deltaP .p0 a) b) = true := by
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hm⟩ := dp_meta_unpack (pIdx_lt_39 a) (pIdx_lt_39 b)
  have hca : Nat.beq (pIdx a) 37 = false := by cases hc : Nat.beq (pIdx a) 37 with | false => rfl | true => exact False.elim (ha (eq_of_beqP hc))
  have hcb : Nat.beq (pIdx b) 37 = false := by cases hc : Nat.beq (pIdx b) 37 with | false => rfl | true => exact False.elim (hb (eq_of_beqP hc))
  have hcf : Nat.beq (dpIdx (dpIdx 0 (pIdx a)) (pIdx b)) 37 = false := by
    cases hc : Nat.beq (dpIdx (dpIdx 0 (pIdx a)) (pIdx b)) 37 with
    | false => rfl
    | true => exfalso; apply hf; apply eq_of_beqP; unfold beqP; rw [(pIdx_deltaP _ _).1, (pIdx_deltaP .p0 _).1]; exact hc
  rw [hca, hcb, hcf, Bool.false_or, Bool.false_or, Bool.false_or] at hm
  unfold isS2StateP; rw [(pIdx_deltaP _ _).1, (pIdx_deltaP .p0 _).1]; exact hm

theorem kindPH_s1 (q : PH) (ha : isAccPH q = true) : isAccPH (deltaPH ph0 q) = true ∧ kindPH (deltaPH ph0 q) = 1 := by
  have hr := isReachPH_of_isAccPH ha
  have ⟨hs1_acc, hs1_k⟩ := (reach_1d_props hr).2.2.2.2.2 ha
  have hi : phIdx (deltaPH ph0 q) = dphIdx 0 (phIdx q) := phIdx_deltaPH (by rfl) hr
  unfold isAccPH kindPH; rw [hi]; exact ⟨hs1_acc, hs1_k⟩

theorem out2d_2d_idx_at {x y : Nat} (hx : x < 95) (hy : y < 95) :
    let s1 := dphIdx 0 x; let s2 := dphIdx s1 y
    isAccIdx s2 = true ∧ kindIdx s2 = 2 ∧
    memNat (95 * x + y) (out2dListIdx s1 y) = true ∧
    (let f0 := dphIdx (dphIdx 0 0) x; let n1 := dphIdx 0 y; let n2 := dphIdx x y
     (isAccIdx f0 && isAccIdx (dphIdx f0 y) && !(isZachosIdx f0 && isZachosIdx y) && !(isZachosIdx n1 && isZachosIdx n2)) = true →
       isAccIdx n2 = true ∧ memNat (95 * y + n2) (out2dListIdx f0 y) = true) := by
  have hxy := checkNat2_sound 95 95 _ out2d_2d_idx_thm hx hy
  have ⟨h3, h4⟩ := (Bool.and_eq_true _ _).mp hxy
  have ⟨h2, h3'⟩ := (Bool.and_eq_true _ _).mp h3
  have ⟨h1, h2'⟩ := (Bool.and_eq_true _ _).mp h2
  refine ⟨h1, Nat.eq_of_beq_eq_true h2', h3', fun hc0 => ?_⟩
  dsimp only [] at h4; rw [hc0, if_true_eq_true] at h4; exact (Bool.and_eq_true _ _).mp h4

theorem kindPH_s2 (x y : PH) (hx : isAccPH x = true) (hy : isAccPH y = true) :
    isAccPH (deltaPH (deltaPH ph0 x) y) = true ∧ kindPH (deltaPH (deltaPH ph0 x) y) = 2 := by
  have hrx := isReachPH_of_isAccPH hx; have hry := isReachPH_of_isAccPH hy
  have h := out2d_2d_idx_at (phIdx_lt_95 hx) (phIdx_lt_95 hy)
  have hi2 : phIdx (deltaPH (deltaPH ph0 x) y) = dphIdx (dphIdx 0 (phIdx x)) (phIdx y) := by
    rw [phIdx_deltaPH (isReachPH_deltaPH (by rfl) hrx) hry, phIdx_deltaPH (by rfl) hrx]; rfl
  unfold isAccPH kindPH; rw [hi2]; exact ⟨h.1, h.2.1⟩

theorem out2dAllPairs_sound {f w c d : PH} {P : PH → PH → Bool}
    (hall : out2dAllPairs f w P = true) (hmem : out2dHas f w c d = true) : P c d = true := by
  unfold out2dHas at hmem
  have ⟨hcd, hm⟩ := (Bool.and_eq_true _ _).mp hmem
  have ⟨hca, hda⟩ := (Bool.and_eq_true _ _).mp hcd
  have hlt_c := phIdx_lt_95 hca; have hlt_d := phIdx_lt_95 hda
  have hd1 : (95 * phIdx c + phIdx d) / 95 = phIdx c := by omega
  have hd2 : (95 * phIdx c + phIdx d) % 95 = phIdx d := by omega
  have hP := allNat_mem hall hm
  unfold idxToU1 idxToU2 at hP
  rw [hd1, hd2, (ofPhIdx_phIdx (isReachPH_of_isAccPH hca)).1, (ofPhIdx_phIdx (isReachPH_of_isAccPH hda)).1] at hP
  exact hP

theorem out2d_s1_mem (u w : PH) (hu : isAccPH u = true) (hw : isAccPH w = true) :
    out2dHas (deltaPH ph0 u) w u w = true := by
  have h := out2d_2d_idx_at (phIdx_lt_95 hu) (phIdx_lt_95 hw)
  have hi1 : phIdx (deltaPH ph0 u) = dphIdx 0 (phIdx u) := phIdx_deltaPH (by rfl) (isReachPH_of_isAccPH hu)
  unfold out2dHas out2dList; rw [hu, hw, hi1]; exact h.2.2.1

theorem out2d_s2_a0 (b w : PH) (hb : isAccPH b = true) (hw : isAccPH w = true)
    (hf : isAccPH (deltaPH (deltaPH ph0 ph0) b) = true)
    (hfw : isAccPH (deltaPH (deltaPH (deltaPH ph0 ph0) b) w) = true)
    (hnz1 : (isZachosPH (deltaPH (deltaPH ph0 ph0) b) && isZachosPH w) = false)
    (hnz2 : (isZachosPH (deltaPH ph0 w) && isZachosPH (deltaPH b w)) = false) :
    out2dHas (deltaPH (deltaPH ph0 ph0) b) w w (deltaPH b w) = true := by
  have hrb := isReachPH_of_isAccPH hb; have hrw := isReachPH_of_isAccPH hw
  have h := out2d_2d_idx_at (phIdx_lt_95 hb) (phIdx_lt_95 hw)
  have hrf : isReachPH (deltaPH (deltaPH ph0 ph0) b) = true := isReachPH_deltaPH (by rfl) hrb
  have hrn1 : isReachPH (deltaPH ph0 w) = true := isReachPH_deltaPH (by rfl) hrw
  have hrn2 : isReachPH (deltaPH b w) = true := isReachPH_deltaPH hrb hrw
  have hif : phIdx (deltaPH (deltaPH ph0 ph0) b) = dphIdx (dphIdx 0 0) (phIdx b) := phIdx_deltaPH (by rfl) hrb
  have hifw : phIdx (deltaPH (deltaPH (deltaPH ph0 ph0) b) w) = dphIdx (dphIdx (dphIdx 0 0) (phIdx b)) (phIdx w) := by rw [phIdx_deltaPH hrf hrw, hif]
  have hin1 : phIdx (deltaPH ph0 w) = dphIdx 0 (phIdx w) := phIdx_deltaPH (by rfl) hrw
  have hin2 : phIdx (deltaPH b w) = dphIdx (phIdx b) (phIdx w) := phIdx_deltaPH hrb hrw
  have hcond : (isAccIdx (dphIdx (dphIdx 0 0) (phIdx b)) && isAccIdx (dphIdx (dphIdx (dphIdx 0 0) (phIdx b)) (phIdx w)) &&
      !(isZachosIdx (dphIdx (dphIdx 0 0) (phIdx b)) && isZachosIdx (phIdx w)) &&
      !(isZachosIdx (dphIdx 0 (phIdx w)) && isZachosIdx (dphIdx (phIdx b) (phIdx w)))) = true := by
    rw [← hifw, ← hif, ← hin1, ← hin2,
        ← (reach_1d_props hrf).2.2.2.2.1, ← (reach_1d_props hrw).2.2.2.2.1,
        ← (reach_1d_props hrn1).2.2.2.2.1, ← (reach_1d_props hrn2).2.2.2.2.1]
    change (isAccPH (deltaPH (deltaPH ph0 ph0) b) && isAccPH (deltaPH (deltaPH (deltaPH ph0 ph0) b) w) &&
            !(isZachosPH (deltaPH (deltaPH ph0 ph0) b) && isZachosPH w) &&
            !(isZachosPH (deltaPH ph0 w) && isZachosPH (deltaPH b w))) = true
    rw [hf, hfw, hnz1, hnz2]; rfl
  have ⟨hn2_acc, hmem⟩ := h.2.2.2 hcond
  unfold out2dHas out2dList; rw [hw]; unfold isAccPH; rw [hin2, hn2_acc, hif]; exact hmem

theorem out2d_trans {a b w u1 u2 c d : PH}
    (ha : isAccPH a = true) (hb : isAccPH b = true) (hw : isAccPH w = true)
    (hf : isAccPH (deltaPH (deltaPH ph0 a) b) = true)
    (hfw : isAccPH (deltaPH (deltaPH (deltaPH ph0 a) b) w) = true)
    (hnz1 : (isZachosPH (deltaPH (deltaPH ph0 a) b) && isZachosPH w) = false)
    (hnz2 : (isZachosPH (deltaPH a w) && isZachosPH (deltaPH b w)) = false)
    (hnz3 : (isZachosPH (deltaPH (deltaPH ph0 u1) u2) && isZachosPH (deltaPH b w)) = false)
    (hmem1 : out2dHas a w u1 u2 = true)
    (hmem2 : out2dHas (deltaPH (deltaPH ph0 u1) u2) (deltaPH b w) c d = true) :
    out2dHas (deltaPH (deltaPH ph0 a) b) w c d = true := by
  have hra := isReachPH_of_isAccPH ha; have hrb := isReachPH_of_isAccPH hb; have hrw := isReachPH_of_isAccPH hw
  have hrow_a := out2d_trans_all (phIdx_lt_95 ha)
  have hrb_row := checkNat1_sound 95 _ hrow_a (phIdx_lt_95 hb)
  dsimp only [] at hrb_row
  have hrf : isReachPH (deltaPH (deltaPH ph0 a) b) = true := isReachPH_deltaPH (isReachPH_deltaPH (by rfl) hra) hrb
  have hrn1 : isReachPH (deltaPH a w) = true := isReachPH_deltaPH hra hrw
  have hrn2 : isReachPH (deltaPH b w) = true := isReachPH_deltaPH hrb hrw
  have hif : phIdx (deltaPH (deltaPH ph0 a) b) = dphIdx (dphIdx 0 (phIdx a)) (phIdx b) := by
    rw [phIdx_deltaPH (isReachPH_deltaPH (by rfl) hra) hrb, phIdx_deltaPH (by rfl) hra]; rfl
  have hifw : phIdx (deltaPH (deltaPH (deltaPH ph0 a) b) w) = dphIdx (dphIdx (dphIdx 0 (phIdx a)) (phIdx b)) (phIdx w) := by rw [phIdx_deltaPH hrf hrw, hif]
  have hin1 : phIdx (deltaPH a w) = dphIdx (phIdx a) (phIdx w) := phIdx_deltaPH hra hrw
  have hin2 : phIdx (deltaPH b w) = dphIdx (phIdx b) (phIdx w) := phIdx_deltaPH hrb hrw
  have hfi : (!isAccIdx (dphIdx (dphIdx 0 (phIdx a)) (phIdx b))) = false := by
    rw [← hif]; change (!isAccPH (deltaPH (deltaPH ph0 a) b)) = false; rw [hf]; rfl
  rw [hfi, if_false_eq_true] at hrb_row
  have hrw_row := checkNat1_sound 95 _ hrb_row (phIdx_lt_95 hw)
  have hg2 : (!isAccIdx (dphIdx (dphIdx (dphIdx 0 (phIdx a)) (phIdx b)) (phIdx w)) ||
      (isZachosIdx (dphIdx (dphIdx 0 (phIdx a)) (phIdx b)) && isZachosIdx (phIdx w)) ||
      (isZachosIdx (dphIdx (phIdx a) (phIdx w)) && isZachosIdx (dphIdx (phIdx b) (phIdx w)))) = false := by
    rw [← hifw, ← hif, ← hin1, ← hin2,
        ← (reach_1d_props hrf).2.2.2.2.1, ← (reach_1d_props hrw).2.2.2.2.1,
        ← (reach_1d_props hrn1).2.2.2.2.1, ← (reach_1d_props hrn2).2.2.2.2.1]
    change (!isAccPH (deltaPH (deltaPH (deltaPH ph0 a) b) w) ||
            (isZachosPH (deltaPH (deltaPH ph0 a) b) && isZachosPH w) ||
            (isZachosPH (deltaPH a w) && isZachosPH (deltaPH b w))) = false
    rw [hfw, hnz1, hnz2]; rfl
  rw [hg2, if_false_eq_true] at hrw_row
  unfold out2dHas out2dList at hmem1 hmem2 ⊢
  have ⟨hu12_acc, hm1⟩ := (Bool.and_eq_true _ _).mp hmem1
  have ⟨hu1_a, hu2_a⟩ := (Bool.and_eq_true _ _).mp hu12_acc
  have hru1 := isReachPH_of_isAccPH hu1_a; have hru2 := isReachPH_of_isAccPH hu2_a
  have hlt1 := phIdx_lt_95 hu1_a; have hlt2 := phIdx_lt_95 hu2_a
  have hd1 : (95 * phIdx u1 + phIdx u2) / 95 = phIdx u1 := by omega
  have hd2 : (95 * phIdx u1 + phIdx u2) % 95 = phIdx u2 := by omega
  have hbit := allNat_mem hrw_row hm1; try dsimp only [] at hbit
  rw [hd1, hd2] at hbit
  have hru12 : isReachPH (deltaPH (deltaPH ph0 u1) u2) = true := isReachPH_deltaPH (isReachPH_deltaPH (by rfl) hru1) hru2
  have hiu12 : phIdx (deltaPH (deltaPH ph0 u1) u2) = dphIdx (dphIdx 0 (phIdx u1)) (phIdx u2) := by
    rw [phIdx_deltaPH (isReachPH_deltaPH (by rfl) hru1) hru2, phIdx_deltaPH (by rfl) hru1]; rfl
  have hz3_f : (isZachosIdx (dphIdx (dphIdx 0 (phIdx u1)) (phIdx u2)) && isZachosIdx (dphIdx (phIdx b) (phIdx w))) = false := by
    rw [← hiu12, ← hin2, ← (reach_1d_props hru12).2.2.2.2.1, ← (reach_1d_props hrn2).2.2.2.2.1]
    exact hnz3
  rw [hz3_f, if_false_eq_true] at hbit
  have ⟨hcd, hm2⟩ := (Bool.and_eq_true _ _).mp hmem2
  rw [hiu12, hin2] at hm2; rw [hif]
  exact (Bool.and_eq_true _ _).mpr ⟨hcd, subsetNat_mem hbit hm2⟩

structure PValAppRes (f w : PVal) : Type where
  val : PVal
  red : Reduces (f.toTerm ⋅ w.toTerm) val.toTerm
  from_s : f = .s → val = .s1 w
  from_s1 : ∀ u : PVal, f = .s1 u → val = .s2 u w
  s1_imp : ∀ u : PVal, val = .s1 u → f = .s ∧ u = w
  s2_mem : ∀ c d : PVal, val = .s2 c d → out2dHas (evalPH f.toTerm) (evalPH w.toTerm) (evalPH c.toTerm) (evalPH d.toTerm) = true

private theorem rankP_unpack {x y z : StateP}
    (hx : x ≠ .p37) (hy : y ≠ .p37) (hz : z ≠ .p37)
    (hf : deltaP (deltaP .p0 x) y ≠ .p37)
    (hfz : deltaP (deltaP (deltaP .p0 x) y) z ≠ .p37)
    (hnz : !(isZachosP (deltaP (deltaP .p0 x) y) && isZachosP z) = true) :
    let r := tripleRankP x y z; let n1 := deltaP x z; let n2 := deltaP y z
    (1 ≤ r ∧ r ≤ maxSubRankP (deltaP (deltaP .p0 x) y) z ∧ maxSubRankP x z ≤ r ∧ maxSubRankP y z ≤ r) ∧
    (¬(isZachosP n1 && isZachosP n2) = true →
      (isS2StateP x = true → maxSubRankP n1 n2 + 1 ≤ r) ∧
      (∀ u, u ≠ .p37 → deltaP .p0 u = x → tripleRankP u z n2 + 1 ≤ r)) := by
  have h := checkNat2_sound 39 39 _ (rankP_idx_all (pIdx_lt_39 x)) (pIdx_lt_39 y) (pIdx_lt_39 z)
  have hif : pIdx (deltaP (deltaP .p0 x) y) = dpIdx (dpIdx 0 (pIdx x)) (pIdx y) := by rw [(pIdx_deltaP _ _).1, (pIdx_deltaP .p0 _).1]; rfl
  have hifz : pIdx (deltaP (deltaP (deltaP .p0 x) y) z) = dpIdx (dpIdx (dpIdx 0 (pIdx x)) (pIdx y)) (pIdx z) := by rw [(pIdx_deltaP _ z).1, hif]
  have hcx : Nat.beq (pIdx x) 37 = false := by cases hc : Nat.beq (pIdx x) 37 with | false => rfl | true => exact False.elim (hx (eq_of_beqP hc))
  have hcy : Nat.beq (pIdx y) 37 = false := by cases hc : Nat.beq (pIdx y) 37 with | false => rfl | true => exact False.elim (hy (eq_of_beqP hc))
  have hcz : Nat.beq (pIdx z) 37 = false := by cases hc : Nat.beq (pIdx z) 37 with | false => rfl | true => exact False.elim (hz (eq_of_beqP hc))
  have hcf : Nat.beq (dpIdx (dpIdx 0 (pIdx x)) (pIdx y)) 37 = false := by
    cases hc : Nat.beq (dpIdx (dpIdx 0 (pIdx x)) (pIdx y)) 37 with | false => rfl | true => exfalso; apply hf; apply eq_of_beqP; unfold beqP; rw [hif]; exact hc
  have hcfz : Nat.beq (dpIdx (dpIdx (dpIdx 0 (pIdx x)) (pIdx y)) (pIdx z)) 37 = false := by
    cases hc : Nat.beq (dpIdx (dpIdx (dpIdx 0 (pIdx x)) (pIdx y)) (pIdx z)) 37 with | false => rfl | true => exfalso; apply hfz; apply eq_of_beqP; unfold beqP; rw [hifz]; exact hc
  have hczz : (isZachosPIdx (dpIdx (dpIdx 0 (pIdx x)) (pIdx y)) && isZachosPIdx (pIdx z)) = false := by
    rw [← hif, ← isZachosP_eq_idx, ← isZachosP_eq_idx]
    cases hzz : (isZachosP (deltaP (deltaP .p0 x) y) && isZachosP z)
    · rfl
    · rw [hzz] at hnz; cases hnz
  change (if (Nat.beq (pIdx x) 37 || Nat.beq (pIdx y) 37 || Nat.beq (pIdx z) 37 ||
              Nat.beq (dpIdx (dpIdx 0 (pIdx x)) (pIdx y)) 37 ||
              Nat.beq (dpIdx (dpIdx (dpIdx 0 (pIdx x)) (pIdx y)) (pIdx z)) 37 ||
              (isZachosPIdx (dpIdx (dpIdx 0 (pIdx x)) (pIdx y)) && isZachosPIdx (pIdx z))) = true then true else _) = true at h
  rw [hcx, hcy, hcz, hcf, hcfz, hczz] at h
  simp only [Bool.false_or, if_false_eq_true] at h
  have ⟨hb1, hb2⟩ := (Bool.and_eq_true _ _).mp h
  have ⟨hb1a, hb1d⟩ := (Bool.and_eq_true _ _).mp hb1
  have ⟨hb1b, hb1c⟩ := (Bool.and_eq_true _ _).mp hb1a
  have ⟨hc1, hc2⟩ := (Bool.and_eq_true _ _).mp hb1b
  have hc2' : tripleRankP x y z ≤ maxSubRankP (deltaP (deltaP .p0 x) y) z := by unfold maxSubRankP; rw [hif]; exact Nat.le_of_ble_eq_true hc2
  refine ⟨⟨Nat.le_of_ble_eq_true hc1, hc2', Nat.le_of_ble_eq_true hb1c, Nat.le_of_ble_eq_true hb1d⟩, fun hnz2 => ?_⟩
  have hin1 : pIdx (deltaP x z) = dpIdx (pIdx x) (pIdx z) := (pIdx_deltaP x z).1
  have hin2 : pIdx (deltaP y z) = dpIdx (pIdx y) (pIdx z) := (pIdx_deltaP y z).1
  have hzz2 : (isZachosPIdx (dpIdx (pIdx x) (pIdx z)) && isZachosPIdx (dpIdx (pIdx y) (pIdx z))) = false := by
    rw [← hin1, ← hin2, ← isZachosP_eq_idx, ← isZachosP_eq_idx]
    cases hz12 : (isZachosP (deltaP x z) && isZachosP (deltaP y z))
    · rfl
    · exact False.elim (hnz2 hz12)
  rw [hzz2, if_false_eq_true] at hb2
  have ⟨hm, hall⟩ := (Bool.and_eq_true _ _).mp hb2
  refine ⟨fun hs2 => ?_, fun u hu hdu => ?_⟩
  · unfold maxSubRankP; rw [hin1, hin2]; exact Nat.le_of_ble_eq_true (imp_bool hs2 hm)
  · have hu_chk := checkNat1_sound 39 _ hall (pIdx_lt_39 u)
    have hcu : Nat.beq (pIdx u) 37 = false := by cases hc : Nat.beq (pIdx u) 37 with | false => rfl | true => exact False.elim (hu (eq_of_beqP hc))
    have hdu_i : Nat.beq (dpIdx 0 (pIdx u)) (pIdx x) = true := by
      have := (pIdx_deltaP .p0 u).1; rw [hdu] at this; exact Nat.beq_eq.mpr this.symm
    rw [hcu, hdu_i] at hu_chk; simp only [Bool.not_true, Bool.false_or, if_false_eq_true] at hu_chk
    unfold tripleRankP; rw [hin2]; exact Nat.le_of_ble_eq_true hu_chk

def pvalRank : PVal → StateP → Nat
  | .s2 a b, z => if isZachosP (evalP (PVal.s2 a b).toTerm) && isZachosP z then 0 else tripleRankP (evalP a.toTerm) (evalP b.toTerm) z
  | _, _ => 0

private theorem pvalRank_le_maxSubRankP (f : PVal) {z : StateP} (hz : z ≠ .p37) (hfz : deltaP (evalP f.toTerm) z ≠ .p37) :
    pvalRank f z ≤ maxSubRankP (evalP f.toTerm) z := by
  cases f with
  | s => exact Nat.zero_le _ | s1 _ => exact Nat.zero_le _ | zachos _ _ => exact Nat.zero_le _
  | s2 a b =>
    dsimp only [pvalRank]
    cases hzz : (isZachosP (evalP (PVal.s2 a b).toTerm) && isZachosP z)
    · rw [if_false_eq_true]
      have hnz : !(isZachosP (evalP (PVal.s2 a b).toTerm) && isZachosP z) = true := by rw [hzz]; rfl
      exact (rankP_unpack (PVal.evalP_ne_p37 a) (PVal.evalP_ne_p37 b) hz (PVal.evalP_ne_p37 (.s2 a b)) hfz hnz).1.2.1
    · rw [if_true_eq_true]; exact Nat.zero_le _

private def pvalAppS (w : PVal) : PValAppRes .s w :=
  { val := .s1 w, red := Reduces.refl _, from_s := fun _ => rfl, from_s1 := fun _ h => (by cases h),
    s1_imp := fun _ h => ⟨rfl, (by injection h with h'; exact h'.symm)⟩, s2_mem := fun _ _ h => (by cases h) }

private def pvalAppS1 (u w : PVal) : PValAppRes (.s1 u) w :=
  { val := .s2 u w, red := Reduces.refl _, from_s := fun h => (by cases h),
    from_s1 := fun _ h => (by injection h with hu; subst hu; rfl),
    s1_imp := fun _ h => (by cases h),
    s2_mem := fun c d h => (by
      injection h with hc hd; subst hc; subst hd
      exact out2d_s1_mem (evalPH u.toTerm) (evalPH w.toTerm) (PVal.isAccPH_toTerm u) (PVal.isAccPH_toTerm w)) }

private def pvalAppZachos (m n : Nat) (w : PVal) (hfw : deltaP (evalP (PVal.zachos m n).toTerm) (evalP w.toTerm) ≠ .p37) :
    PValAppRes (.zachos m n) w :=
  False.elim (by rw [PVal.toTerm, evalP_zachos_pair m n, deltaP_p29_sink] at hfw; exact hfw rfl)

def pvalApplyStep (rk' : Nat)
    (ih_rk : ∀ (f w : PVal), deltaP (evalP f.toTerm) (evalP w.toTerm) ≠ .p37 → pvalRank f (evalP w.toTerm) ≤ rk' → PValAppRes f w) :
    (f : PVal) → ∀ (w : PVal), deltaP (evalP f.toTerm) (evalP w.toTerm) ≠ .p37 → pvalRank f (evalP w.toTerm) ≤ rk' + 1 → PValAppRes f w
  | .s => fun w _ _ => pvalAppS w
  | .s1 u => fun w _ _ => pvalAppS1 u w
  | .zachos m n => fun w hfw _ => pvalAppZachos m n w hfw
  | .s2 a b => fun w hfw hrk =>
      match hzf : isZachosP (evalP (PVal.s2 a b).toTerm) && isZachosP (evalP w.toTerm) with
      | true =>
        let m := pvalZachosIdx (.s2 a b); let n := pvalZachosIdx w
        { val := .zachos m n,
          red := (by
            have ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hzf
            change Reduces ((PVal.s2 a b).toTerm ⋅ w.toTerm) (zachosG m ⋅ zachosG n)
            rw [pvalZachosIdx_spec (.s2 a b) h1, pvalZachosIdx_spec w h2]; exact Reduces.refl _),
          from_s := fun h => (by cases h), from_s1 := fun _ h => (by cases h),
          s1_imp := fun _ h => (by cases h), s2_mem := fun _ _ h => (by cases h) }
      | false =>
        have hnz_f : !(isZachosP (evalP (PVal.s2 a b).toTerm) && isZachosP (evalP w.toTerm)) = true := by rw [hzf]; rfl
        have hunp := rankP_unpack (PVal.evalP_ne_p37 a) (PVal.evalP_ne_p37 b) (PVal.evalP_ne_p37 w) (PVal.evalP_ne_p37 (.s2 a b)) hfw hnz_f
        have htr_le : tripleRankP (evalP a.toTerm) (evalP b.toTerm) (evalP w.toTerm) ≤ rk' + 1 := by
          dsimp only [pvalRank] at hrk; rw [hzf, if_false_eq_true] at hrk; exact hrk
        have haw_ne : deltaP (evalP a.toTerm) (evalP w.toTerm) ≠ .p37 := fun hbad => hfw (by
          change deltaP (deltaP (deltaP .p0 (evalP a.toTerm)) (evalP b.toTerm)) (evalP w.toTerm) = .p37
          rw [deltaP_s_law, hbad, (deltaP_sink _).1])
        have hbw_ne : deltaP (evalP b.toTerm) (evalP w.toTerm) ≠ .p37 := fun hbad => hfw (by
          change deltaP (deltaP (deltaP .p0 (evalP a.toTerm)) (evalP b.toTerm)) (evalP w.toTerm) = .p37
          rw [deltaP_s_law, hbad, (deltaP_sink _).2])
        let ra := pvalApplyStep rk' ih_rk a w haw_ne (Nat.le_trans (pvalRank_le_maxSubRankP a (PVal.evalP_ne_p37 w) haw_ne) (Nat.le_trans hunp.1.2.2.1 htr_le))
        let rb := pvalApplyStep rk' ih_rk b w hbw_ne (Nat.le_trans (pvalRank_le_maxSubRankP b (PVal.evalP_ne_p37 w) hbw_ne) (Nat.le_trans hunp.1.2.2.2 htr_le))
        have hp_ra : evalP ra.val.toTerm = deltaP (evalP a.toTerm) (evalP w.toTerm) := (evalP_reduces ra.red).symm
        have hp_rb : evalP rb.val.toTerm = deltaP (evalP b.toTerm) (evalP w.toTerm) := (evalP_reduces rb.red).symm
        have hph_ra : evalPH ra.val.toTerm = deltaPH (evalPH a.toTerm) (evalPH w.toTerm) := (evalPH_reduces ra.red).symm
        have hph_rb : evalPH rb.val.toTerm = deltaPH (evalPH b.toTerm) (evalPH w.toTerm) := (evalPH_reduces rb.red).symm
        have hstep_root : Reduces ((PVal.s2 a b).toTerm ⋅ w.toTerm) (ra.val.toTerm ⋅ rb.val.toTerm) :=
          Reduces.next (Step.root a.toTerm b.toTerm w.toTerm) (reduces_trans (reduces_left ra.red _) (reduces_right _ rb.red))
        match hzn : isZachosP (evalP ra.val.toTerm) && isZachosP (evalP rb.val.toTerm) with
        | true =>
          let m := pvalZachosIdx ra.val; let n := pvalZachosIdx rb.val
          { val := .zachos m n,
            red := (by
              have ⟨hz1, hz2⟩ := (Bool.and_eq_true _ _).mp hzn
              change Reduces ((PVal.s2 a b).toTerm ⋅ w.toTerm) (zachosG m ⋅ zachosG n)
              rw [← pvalZachosIdx_spec ra.val hz1, ← pvalZachosIdx_spec rb.val hz2]; exact hstep_root),
            from_s := fun h => (by cases h), from_s1 := fun _ h => (by cases h),
            s1_imp := fun _ h => (by cases h), s2_mem := fun _ _ h => (by cases h) }
        | false =>
          have hnz_n : ¬(isZachosP (deltaP (evalP a.toTerm) (evalP w.toTerm)) && isZachosP (deltaP (evalP b.toTerm) (evalP w.toTerm))) = true := by
            intro hbad; rw [← hp_ra, ← hp_rb, hzn] at hbad; cases hbad
          have hprod_ne : deltaP (evalP ra.val.toTerm) (evalP rb.val.toTerm) ≠ .p37 := fun hbad => hfw (by
            change deltaP (deltaP (deltaP .p0 (evalP a.toTerm)) (evalP b.toTerm)) (evalP w.toTerm) = .p37
            rw [deltaP_s_law, ← hp_ra, ← hp_rb]; exact hbad)
          have hsub_rk : pvalRank ra.val (evalP rb.val.toTerm) ≤ rk' := by
            have ha_cases : (∃ u, a = .s1 u) ∨ (a = .s) ∨ (∃ m n, a = .zachos m n) ∨ (∃ a1 a2, a = .s2 a1 a2) :=
              match a with | .s1 u => Or.inl ⟨u, rfl⟩ | .s => Or.inr (Or.inl rfl) | .zachos m n => Or.inr (Or.inr (Or.inl ⟨m, n, rfl⟩)) | .s2 a1 a2 => Or.inr (Or.inr (Or.inr ⟨a1, a2, rfl⟩))
            rcases ha_cases with ⟨u, ha_s1⟩ | ha_s | ⟨m, n, ha_z⟩ | ⟨a1, a2, ha_s2⟩
            · rw [ra.from_s1 u ha_s1]; dsimp only [pvalRank]
              cases hzz2 : (isZachosP (evalP (PVal.s2 u w).toTerm) && isZachosP (evalP rb.val.toTerm))
              · rw [if_false_eq_true, hp_rb]
                have hdu : deltaP .p0 (evalP u.toTerm) = evalP a.toTerm := by rw [ha_s1]; rfl
                have hle_u := (hunp.2 hnz_n).2 (evalP u.toTerm) (PVal.evalP_ne_p37 u) hdu
                omega
              · rw [if_true_eq_true]; exact Nat.zero_le _
            · rw [ra.from_s ha_s]; exact Nat.zero_le _
            · exfalso; have hp29 : evalP a.toTerm = .p29 := by rw [ha_z, PVal.toTerm]; exact evalP_zachos_pair m n
              rw [hp29, deltaP_p29_sink] at haw_ne; exact haw_ne rfl
            · have hs2 : isS2StateP (evalP a.toTerm) = true := by rw [ha_s2]; exact isS2StateP_intro (PVal.evalP_ne_p37 a1) (PVal.evalP_ne_p37 a2) (PVal.evalP_ne_p37 (.s2 a1 a2))
              have hmax_le : maxSubRankP (evalP ra.val.toTerm) (evalP rb.val.toTerm) ≤ rk' := by
                rw [hp_ra, hp_rb]; have hle1 := (hunp.2 hnz_n).1 hs2; omega
              exact Nat.le_trans (pvalRank_le_maxSubRankP ra.val (PVal.evalP_ne_p37 rb.val) hprod_ne) hmax_le
          let rfin := ih_rk ra.val rb.val hprod_ne hsub_rk
          { val := rfin.val, red := reduces_trans hstep_root rfin.red,
            from_s := fun h => (by cases h), from_s1 := fun _ h => (by cases h),
            s1_imp := fun u hu => (by
              obtain ⟨hra_s, _⟩ := rfin.s1_imp u hu; exfalso
              have hph0 : evalPH ra.val.toTerm = ph0 := by rw [hra_s]; rfl
              rw [hph_ra] at hph0; exact deltaPH_ne_ph0 _ _ hph0),
            s2_mem := fun c d hcd => (by
              have hacc_fw : isAccPH (deltaPH (evalPH (PVal.s2 a b).toTerm) (evalPH w.toTerm)) = true :=
                (isAccPH_evalPH_iff (t := (PVal.s2 a b).toTerm ⋅ w.toTerm) ((Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm (.s2 a b), PVal.noVars_toTerm w⟩)).mpr hfw
              have hnz_f_ph : (isZachosPH (deltaPH (deltaPH ph0 (evalPH a.toTerm)) (evalPH b.toTerm)) && isZachosPH (evalPH w.toTerm)) = false := hzf
              have hnz_n_ph : (isZachosPH (deltaPH (evalPH a.toTerm) (evalPH w.toTerm)) && isZachosPH (deltaPH (evalPH b.toTerm) (evalPH w.toTerm))) = false := by
                change (isZachosP (deltaP (evalP a.toTerm) (evalP w.toTerm)) && isZachosP (deltaP (evalP b.toTerm) (evalP w.toTerm))) = false
                rw [← hp_ra, ← hp_rb]; exact hzn
              cases hra_v : ra.val with
              | s => exfalso; have hph0 : evalPH ra.val.toTerm = ph0 := by rw [hra_v]; rfl
                     rw [hph_ra] at hph0; exact deltaPH_ne_ph0 _ _ hph0
              | zachos m n => exfalso; have hp29 : evalP ra.val.toTerm = .p29 := by rw [hra_v, PVal.toTerm]; exact evalP_zachos_pair m n
                              rw [hp29, deltaP_p29_sink] at hprod_ne; exact hprod_ne rfl
              | s1 u =>
                obtain ⟨ha_s, hu_w⟩ := ra.s1_imp u hra_v; rw [hu_w] at hra_v
                have hrfin_eq : rfin.val = .s2 w rb.val := rfin.from_s1 w hra_v
                rw [hrfin_eq] at hcd; injection hcd with hc_eq hd_eq; subst hc_eq; subst hd_eq
                rw [hph_rb]; rw [ha_s] at hacc_fw hnz_f_ph hnz_n_ph ⊢
                exact out2d_s2_a0 (evalPH b.toTerm) (evalPH w.toTerm) (PVal.isAccPH_toTerm b) (PVal.isAccPH_toTerm w) (PVal.isAccPH_toTerm (.s2 .s b)) hacc_fw hnz_f_ph hnz_n_ph
              | s2 u1 u2 =>
                have hmem_aw := ra.s2_mem u1 u2 hra_v
                have hmem_fin := rfin.s2_mem c d hcd
                rw [hra_v] at hmem_fin
                change out2dHas (deltaPH (deltaPH ph0 (evalPH u1.toTerm)) (evalPH u2.toTerm)) (evalPH rb.val.toTerm) (evalPH c.toTerm) (evalPH d.toTerm) = true at hmem_fin
                rw [hph_rb] at hmem_fin
                have hnz_u12 : (isZachosPH (deltaPH (deltaPH ph0 (evalPH u1.toTerm)) (evalPH u2.toTerm)) && isZachosPH (deltaPH (evalPH b.toTerm) (evalPH w.toTerm))) = false := by
                  have heq_u12 : deltaPH (deltaPH ph0 (evalPH u1.toTerm)) (evalPH u2.toTerm) = deltaPH (evalPH a.toTerm) (evalPH w.toTerm) := by rw [← hph_ra, hra_v]; rfl
                  rw [heq_u12]; exact hnz_n_ph
                exact out2d_trans (PVal.isAccPH_toTerm a) (PVal.isAccPH_toTerm b) (PVal.isAccPH_toTerm w) (PVal.isAccPH_toTerm (.s2 a b)) hacc_fw hnz_f_ph hnz_n_ph hnz_u12 hmem_aw hmem_fin) }

def pvalApplyRk : (rk : Nat) → ∀ (f w : PVal),
    deltaP (evalP f.toTerm) (evalP w.toTerm) ≠ .p37 → pvalRank f (evalP w.toTerm) ≤ rk → PValAppRes f w
  | 0 => fun f w hfw hrk =>
      match f, hfw, hrk with
      | .s, _, _ => pvalAppS w
      | .s1 u, _, _ => pvalAppS1 u w
      | .zachos m n, hfw, _ => pvalAppZachos m n w hfw
      | .s2 a b, hfw, hrk =>
        match hzf : isZachosP (evalP (PVal.s2 a b).toTerm) && isZachosP (evalP w.toTerm) with
        | true =>
          let m := pvalZachosIdx (.s2 a b); let n := pvalZachosIdx w
          { val := .zachos m n,
            red := (by
              have ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hzf
              change Reduces ((PVal.s2 a b).toTerm ⋅ w.toTerm) (zachosG m ⋅ zachosG n)
              rw [pvalZachosIdx_spec (.s2 a b) h1, pvalZachosIdx_spec w h2]; exact Reduces.refl _),
            from_s := fun h => (by cases h), from_s1 := fun _ h => (by cases h),
            s1_imp := fun _ h => (by cases h), s2_mem := fun _ _ h => (by cases h) }
        | false =>
          have hnz_f : !(isZachosP (evalP (PVal.s2 a b).toTerm) && isZachosP (evalP w.toTerm)) = true := by rw [hzf]; rfl
          have hunp := rankP_unpack (PVal.evalP_ne_p37 a) (PVal.evalP_ne_p37 b) (PVal.evalP_ne_p37 w) (PVal.evalP_ne_p37 (.s2 a b)) hfw hnz_f
          have htr_le : tripleRankP (evalP a.toTerm) (evalP b.toTerm) (evalP w.toTerm) ≤ 0 := by
            dsimp only [pvalRank] at hrk; rw [hzf, if_false_eq_true] at hrk; exact hrk
          False.elim (Nat.not_succ_le_zero 0 (Nat.le_trans hunp.1.1 htr_le))
  | rk' + 1 => fun f w hfw hrk => pvalApplyStep rk' (pvalApplyRk rk') f w hfw hrk

def pvalApply (f w : PVal) (hfw : deltaP (evalP f.toTerm) (evalP w.toTerm) ≠ .p37) : PValAppRes f w :=
  pvalApplyRk (pvalRank f (evalP w.toTerm)) f w hfw (Nat.le_refl _)

def toPVal : (t : Term) → noVars t = true → evalP t ≠ .p37 → Σ' v : PVal, Reduces t v.toTerm
  | .s, _, _ => ⟨.s, Reduces.refl S⟩
  | .var _, hv, _ => False.elim (by cases hv)
  | .app a b, hv, hab =>
    have ⟨hva, hvb⟩ := (Bool.and_eq_true _ _).mp hv
    have ha_ne : evalP a ≠ .p37 := fun h37 => hab (by change deltaP (evalP a) (evalP b) = .p37; rw [h37]; exact (deltaP_sink _).1)
    have hb_ne : evalP b ≠ .p37 := fun h37 => hab (by change deltaP (evalP a) (evalP b) = .p37; rw [h37]; exact (deltaP_sink _).2)
    let ⟨va, hra⟩ := toPVal a hva ha_ne
    let ⟨vb, hrb⟩ := toPVal b hvb hb_ne
    have hprod_ne : deltaP (evalP va.toTerm) (evalP vb.toTerm) ≠ .p37 := by rw [← evalP_reduces hra, ← evalP_reduces hrb]; exact hab
    let r := pvalApply va vb hprod_ne
    ⟨r.val, reduces_trans (reduces_trans (reduces_left hra b) (reduces_right va.toTerm hrb)) r.red⟩

/-! ## 4. Unified Rank-10 Completeness (`RankSolvedUpTo 10` — Zero Parity Split) -/

theorem directN1N2_eq_idx {x z n2 : PH} (hx : isReachPH x = true) (hz : isReachPH z = true) (hn2 : isReachPH n2 = true) :
    directN1N2Rank x z n2 = directN1N2Idx (phIdx x) (phIdx z) (phIdx n2) := by
  have hr1 := isReachPH_deltaPH hx hz
  have hr12 := isReachPH_deltaPH hr1 hn2
  simp only [directN1N2Rank, directN1N2Idx, kindPH, isAccPH, pairRank,
             (reach_1d_props hr12).2.2.2.1, phIdx_deltaPH hr1 hn2, phIdx_deltaPH hx hz]

theorem tripleRank_eq_idx {x y z : PH} (hx : isReachPH x = true) (hy : isReachPH y = true) (hz : isReachPH z = true) :
    tripleRank x y z = tripleRankIdx (phIdx x) (phIdx y) (phIdx z) := by
  have hr1 := isReachPH_deltaPH hx hz
  have hr2 := isReachPH_deltaPH hy hz
  simp only [tripleRank, tripleRankIdx, pairRank, c3Rank, isAccPH,
             (reach_1d_props hr1).2.2.2.1, (reach_1d_props hr2).2.2.2.1,
             directN1N2_eq_idx hx hz hr2, phIdx_deltaPH hx hz, phIdx_deltaPH hy hz]; rfl

theorem minPos_cases {a b rk : Nat} (hpos : 1 ≤ minPos a b) (hle : minPos a b ≤ rk) :
    (1 ≤ a ∧ a ≤ rk) ∨ (1 ≤ b ∧ b ≤ rk) := by
  unfold minPos at hpos hle
  cases ha : Nat.beq a 0
  · rw [ha, if_false_eq_true] at hpos hle
    have hapos : 1 ≤ a := by cases a with | zero => cases ha | succ _ => omega
    cases hb : Nat.beq b 0
    · rw [hb, if_false_eq_true] at hpos hle
      have hbpos : 1 ≤ b := by cases b with | zero => cases hb | succ _ => omega
      cases hab : Nat.ble a b
      · rw [hab, if_false_eq_true] at hle; exact Or.inr ⟨hbpos, hle⟩
      · rw [hab, if_true_eq_true] at hle; exact Or.inl ⟨hapos, hle⟩
    · rw [hb, if_true_eq_true] at hle; exact Or.inl ⟨hapos, hle⟩
  · rw [ha, if_true_eq_true] at hpos hle; exact Or.inr ⟨hpos, hle⟩

theorem tripleRank_cases {x y z : PH} {rk : Nat}
    (hpos : 1 ≤ tripleRank x y z) (hle : tripleRank x y z ≤ rk) :
    isHN34PH (deltaPH y z) = true ∨
    isHN34PH (deltaPH x z) = true ∨
    (1 ≤ pairRank x z ∧ pairRank x z ≤ rk) ∨
    (isAccPH y = true ∧ 1 ≤ pairRank y z ∧ pairRank y z ≤ rk) ∨
    (1 ≤ directN1N2Rank x z (deltaPH y z) ∧ directN1N2Rank x z (deltaPH y z) ≤ rk) ∨
    (1 ≤ c3Rank x z (deltaPH y z) ∧ c3Rank x z (deltaPH y z) ≤ rk) := by
  unfold tripleRank at hpos hle
  cases hn2 : isHN34PH (deltaPH y z)
  · cases hn1 : isHN34PH (deltaPH x z)
    · simp only [hn2, hn1, Bool.false_or, if_false_eq_true] at hpos hle
      rcases minPos_cases hpos hle with hL | hrest1
      · exact Or.inr (Or.inr (Or.inl hL))
      · rcases minPos_cases hrest1.1 hrest1.2 with hR | hrest2
        · cases hy : isAccPH y
          · rw [hy, if_false_eq_true] at hR; exact False.elim (Nat.not_succ_le_zero 0 hR.1)
          · rw [hy, if_true_eq_true] at hR; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hR.1, hR.2⟩)))
        · rcases minPos_cases hrest2.1 hrest2.2 with hD | hC
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hD))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hC))))
    · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

def ob1_fn (f z : PH) : Bool :=
  (if Nat.ble 1 (pairRank f z) then Nat.beq (kindPH f) 2 && !isAccPH (deltaPH f z) else true) &&
  (if isAccPH f && isAccPH z && !isAccPH (deltaPH f z) then Nat.ble 1 (pairRank f z) && Nat.ble (pairRank f z) 10 else true)

theorem ob1_chk (f z : PH) (hf : isAccPH f = true) (hz : isReachPH z = true) : ob1_fn f z = true := by
  have h := checkNat2_sound 95 113 _ ob1_idx_thm (phIdx_lt_95 hf) (phIdx_lt_113 hz)
  have hidfz : phIdx (deltaPH f z) = dphIdx (phIdx f) (phIdx z) := phIdx_deltaPH (isReachPH_of_isAccPH hf) hz
  unfold ob1_fn pairRank kindPH isAccPH
  rw [hidfz]; exact h

def ob2_fn (a b z : PH) : Bool :=
  let f := deltaPH (deltaPH ph0 a) b; let pr := pairRank f z
  if Nat.beq pr 0 || isHN34PH z || isHN34PH (deltaPH f z) then true
  else let tr := tripleRank a b z; Nat.ble 1 tr && Nat.ble tr pr

theorem ob2_chk (a b z : PH) (ha : isAccPH a = true) (hb : isAccPH b = true) (hz : isReachPH z = true) : ob2_fn a b z = true := by
  have hra := isReachPH_of_isAccPH ha; have hrb := isReachPH_of_isAccPH hb
  have h := checkNat2_sound 95 113 _ (ob2_idx_all (phIdx_lt_95 ha)) (phIdx_lt_95 hb) (phIdx_lt_113 hz)
  dsimp only [] at h
  have hrf : isReachPH (deltaPH (deltaPH ph0 a) b) = true := isReachPH_deltaPH (isReachPH_deltaPH (by rfl) hra) hrb
  have hrfz : isReachPH (deltaPH (deltaPH (deltaPH ph0 a) b) z) = true := isReachPH_deltaPH hrf hz
  have hif : phIdx (deltaPH (deltaPH ph0 a) b) = dphIdx (dphIdx 0 (phIdx a)) (phIdx b) := by
    rw [phIdx_deltaPH (isReachPH_deltaPH (by rfl) hra) hrb, phIdx_deltaPH (by rfl) hra]; rfl
  have hifz : phIdx (deltaPH (deltaPH (deltaPH ph0 a) b) z) = dphIdx (dphIdx (dphIdx 0 (phIdx a)) (phIdx b)) (phIdx z) := by
    rw [phIdx_deltaPH hrf hz, hif]
  simp only [ob2_fn, pairRank, (reach_1d_props hz).2.2.2.1, (reach_1d_props hrfz).2.2.2.1,
             hifz, hif, tripleRank_eq_idx hra hrb hz]
  exact h

theorem c3Rank_ph0 (z n2 : PH) (hz : isReachPH z = true) (hn2 : isReachPH n2 = true) : c3Rank ph0 z n2 = 0 :=
  Nat.eq_of_beq_eq_true (checkNat2_sound 113 113 _ c3_ph0_idx_thm (phIdx_lt_113 hz) (phIdx_lt_113 hn2))

def ob3_fn (u z n2 : PH) : Bool :=
  let x := deltaPH ph0 u; let cr := c3Rank x z n2
  if Nat.beq cr 0 || isHN34PH z || isHN34PH n2 then true
  else
    let un2 := deltaPH u n2
    if isHN34PH un2 then true
    else if !isAccPH un2 && Nat.beq (kindPH u) 2 then Nat.ble 1 (pairRank u n2) && Nat.ble (pairRank u n2) cr
    else isHN34PH (deltaPH (deltaPH x z) n2) ||
         (let tr := tripleRank u z n2; Nat.ble 1 tr && (if isAccPH z then Nat.ble (tr + 1) cr else Nat.ble tr cr))

theorem ob3_chk (u z n2 : PH) (hu : isAccPH u = true) (hz : isReachPH z = true) (hn2 : isReachPH n2 = true) : ob3_fn u z n2 = true := by
  have hru := isReachPH_of_isAccPH hu
  have hrow := ob3_idx_all (phIdx_lt_95 hu)
  dsimp only [ob3_idx_row] at hrow
  have h1 := checkNat1_sound 113 _ hrow (phIdx_lt_113 hz)
  dsimp only [ob3_fn]
  cases htop : (Nat.beq (c3Rank (deltaPH ph0 u) z n2) 0 || isHN34PH z || isHN34PH n2)
  · rw [if_false_eq_true]
    have ⟨htop12, hn2_f⟩ := Bool.or_eq_false_iff.mp htop
    have ⟨hcr_f, hz_f⟩ := Bool.or_eq_false_iff.mp htop12
    have hzi : isHN34Idx (phIdx z) = false := by rw [← (reach_1d_props hz).2.2.2.1]; exact hz_f
    rw [hzi, if_false_eq_true] at h1
    have h2 := checkNat1_sound 113 _ h1 (phIdx_lt_113 hn2)
    have hrx : isReachPH (deltaPH ph0 u) = true := isReachPH_deltaPH (by rfl) hru
    have hix : phIdx (deltaPH ph0 u) = dphIdx 0 (phIdx u) := phIdx_deltaPH (by rfl) hru
    have hcr_fi : Nat.beq (c3RankIdx (dphIdx 0 (phIdx u)) (phIdx z) (phIdx n2)) 0 = false := by
      unfold c3Rank at hcr_f; rw [hix] at hcr_f; exact hcr_f
    have hg1 : (Nat.beq (c3RankIdx (dphIdx 0 (phIdx u)) (phIdx z) (phIdx n2)) 0 || isHN34Idx (phIdx n2)) = false := by
      rw [← (reach_1d_props hn2).2.2.2.1]; exact Bool.or_eq_false_iff.mpr ⟨hcr_fi, hn2_f⟩
    rw [hg1, if_false_eq_true] at h2
    have hrun2 := isReachPH_deltaPH hru hn2
    have hiun2 := phIdx_deltaPH hru hn2
    have hrxz := isReachPH_deltaPH hrx hz
    have hrxzn2 := isReachPH_deltaPH hrxz hn2
    have hixzn2 : phIdx (deltaPH (deltaPH (deltaPH ph0 u) z) n2) = dphIdx (dphIdx (dphIdx 0 (phIdx u)) (phIdx z)) (phIdx n2) := by
      rw [phIdx_deltaPH hrxz hn2, phIdx_deltaPH hrx hz, hix]
    simp only [c3Rank, pairRank, kindPH, isAccPH,
               (reach_1d_props hrun2).2.2.2.1, hiun2,
               (reach_1d_props hrxzn2).2.2.2.1, hixzn2, hix,
               tripleRank_eq_idx hru hz hn2]
    exact h2
  · rw [if_true_eq_true]

def ob4_fn (x z n2 : PH) : Bool :=
  let cr := c3Rank x z n2
  if Nat.beq cr 0 || !Nat.beq (kindPH x) 2 || isHN34PH z || isHN34PH n2 then true
  else isAccPH z && isAccPH (deltaPH x z) &&
       out2dAllPairs x z (fun a b =>
         isHN34PH (deltaPH (deltaPH (deltaPH ph0 a) b) n2) ||
         (let tr := tripleRank a b n2; Nat.ble 1 tr && Nat.ble (tr + 1) cr))

theorem ob4_chk (x z n2 : PH) (hx : isAccPH x = true) (hz : isReachPH z = true) (hn2 : isReachPH n2 = true) : ob4_fn x z n2 = true := by
  have hrx := isReachPH_of_isAccPH hx
  have hrow := ob4_idx_all (phIdx_lt_95 hx)
  dsimp only [ob4_idx_row] at hrow
  dsimp only [ob4_fn]
  cases htop : (Nat.beq (c3Rank x z n2) 0 || !Nat.beq (kindPH x) 2 || isHN34PH z || isHN34PH n2)
  · rw [if_false_eq_true]
    have ⟨ht123, hn2_f⟩ := Bool.or_eq_false_iff.mp htop
    have ⟨ht12, hz_f⟩ := Bool.or_eq_false_iff.mp ht123
    have ⟨hcr_f, hk2_f⟩ := Bool.or_eq_false_iff.mp ht12
    have hk2_eq : (!Nat.beq (kindIdx (phIdx x)) 2) = false := hk2_f
    rw [hk2_eq, if_false_eq_true] at hrow
    have h1 := checkNat1_sound 113 _ hrow (phIdx_lt_113 hz)
    have hzi : isHN34Idx (phIdx z) = false := by rw [← (reach_1d_props hz).2.2.2.1]; exact hz_f
    rw [hzi, if_false_eq_true] at h1
    have h2 := checkNat1_sound 113 _ h1 (phIdx_lt_113 hn2)
    have hg2 : (Nat.beq (c3RankIdx (phIdx x) (phIdx z) (phIdx n2)) 0 || isHN34Idx (phIdx n2)) = false := by
      rw [← (reach_1d_props hn2).2.2.2.1]; exact Bool.or_eq_false_iff.mpr ⟨hcr_f, hn2_f⟩
    rw [hg2, if_false_eq_true] at h2
    have ⟨hacc_pair, hall_i⟩ := (Bool.and_eq_true _ _).mp h2
    have ⟨hz_ai, hxz_ai⟩ := (Bool.and_eq_true _ _).mp hacc_pair
    have hz_acc : isAccPH z = true := hz_ai
    have hxz_acc : isAccPH (deltaPH x z) = true := by unfold isAccPH; rw [phIdx_deltaPH hrx hz]; exact hxz_ai
    rw [hz_acc, hxz_acc]; simp only [Bool.true_and]
    unfold out2dAllPairs out2dList
    generalize out2dListIdx (phIdx x) (phIdx z) = xs at hall_i ⊢
    induction xs with
    | nil => rfl
    | cons idx rest ih =>
      have ⟨hhead, htail⟩ := (Bool.and_eq_true _ _).mp hall_i
      refine (Bool.and_eq_true _ _).mpr ⟨?_, ih htail⟩
      have ⟨hidx_lt, hbody⟩ := (Bool.and_eq_true _ _).mp hhead
      have hlt9025 : idx < 9025 := Nat.le_of_ble_eq_true hidx_lt
      have ha113 : idx / 95 < 113 := by omega
      have hb113 : idx % 95 < 113 := by omega
      have ⟨hia, hra, _⟩ := ofPhIdx_spec ha113
      have ⟨hib, hrb, _⟩ := ofPhIdx_spec hb113
      have hrsab : isReachPH (deltaPH (deltaPH ph0 (idxToU1 idx)) (idxToU2 idx)) = true :=
        isReachPH_deltaPH (isReachPH_deltaPH (by rfl) hra) hrb
      have hrsabn2 : isReachPH (deltaPH (deltaPH (deltaPH ph0 (idxToU1 idx)) (idxToU2 idx)) n2) = true :=
        isReachPH_deltaPH hrsab hn2
      have hisabn2 : phIdx (deltaPH (deltaPH (deltaPH ph0 (idxToU1 idx)) (idxToU2 idx)) n2) =
          dphIdx (dphIdx (dphIdx 0 (idx / 95)) (idx % 95)) (phIdx n2) := by
        rw [phIdx_deltaPH hrsab hn2]; unfold idxToU1 idxToU2
        rw [phIdx_deltaPH (isReachPH_deltaPH (by rfl) hra) hrb, phIdx_deltaPH (by rfl) hra, hia, hib]; rfl
      have htr_eq : tripleRank (idxToU1 idx) (idxToU2 idx) n2 = tripleRankIdx (idx / 95) (idx % 95) (phIdx n2) := by
        unfold idxToU1 idxToU2; rw [tripleRank_eq_idx hra hrb hn2, hia, hib]
      dsimp only []
      rw [(reach_1d_props hrsabn2).2.2.2.1, hisabn2, htr_eq]; exact hbody
  · rw [if_true_eq_true]

inductive Arg : Type where
  | pval : PVal → Arg
  | raw : Term → Arg

def Arg.toTerm : Arg → Term | .pval v => v.toTerm | .raw t => t
def Arg.pvalSize : Arg → Nat | .pval v => v.size | .raw _ => 0

structure ValidArg (a : Arg) : Prop where
  hv : noVars a.toTerm = true
  not_hn34 : isHN34PH (evalPH a.toTerm) = false
  acc_is_pval : isAccPH (evalPH a.toTerm) = true → ∃ v : PVal, a = .pval v
  not_acc_pvalSize_zero : isAccPH (evalPH a.toTerm) = false → a.pvalSize = 0

theorem ValidArg.reach {a : Arg} (ha : ValidArg a) : isReachPH (evalPH a.toTerm) = true :=
  evalPH_isReach ha.hv

theorem validArg_pval (v : PVal) : ValidArg (.pval v) := by
  have hacc := PVal.isAccPH_toTerm v
  have hr := isReachPH_of_isAccPH hacc
  have hlt95 := phIdx_lt_95 hacc
  have hnot34 : isHN34PH (evalPH v.toTerm) = false := by
    rw [(reach_1d_props hr).2.2.2.1]; unfold isHN34Idx
    cases hc : Nat.beq (phIdx (evalPH v.toTerm)) 112 with
    | false => rfl
    | true => have hc' := Nat.eq_of_beq_eq_true hc; exact False.elim (by omega)
  exact ⟨PVal.noVars_toTerm v, hnot34, fun _ => ⟨v, rfl⟩,
         fun hf => by change isAccPH (evalPH v.toTerm) = false at hf; rw [hacc] at hf; cases hf⟩

def mkValidArg (t : Term) (hv : noVars t = true) (hnot34 : isHN34PH (evalPH t) = false) :
    Σ' a : Arg, Reduces t a.toTerm ∧ evalPH a.toTerm = evalPH t ∧ ValidArg a :=
  match hb : beqP (evalP t) .p37 with
  | false =>
    let ⟨v, hred⟩ := toPVal t hv (ne_of_beqP_false hb)
    ⟨.pval v, hred, (evalPH_reduces hred).symm, validArg_pval v⟩
  | true =>
    ⟨.raw t, Reduces.refl t, rfl,
     ⟨hv, hnot34, fun hacc => False.elim (((isAccPH_evalPH_iff hv).mp hacc) (eq_of_beqP hb)), fun _ => rfl⟩⟩

private theorem hasBot_from_hn34_ph {t : Term} (hv : noVars t = true) (h34 : isHN34PH (evalPH t) = true) : HasBot t :=
  ⟨0, closed_evalHN_hn34_hasBot0 hv (eq_of_beq_StateHN h34)⟩

private theorem hasBot_app_left_bot {y z : Term} (hvy : noVars y = true) (hvz : noVars z = true) (hb : HasBot y) : HasBot (y ⋅ z) :=
  let ⟨d, hd⟩ := hb; ⟨d, hasBotWithin_app_left hvy hvz hd⟩

private theorem hasBot_app_right_bot {f w : Term} (hvf : noVars f = true) (hvw : noVars w = true) (hb : HasBot w) : HasBot (f ⋅ w) :=
  let ⟨d, hd⟩ := hb; ⟨d + 1, hasBotWithin_app_right hvf hvw hd⟩

private theorem hasBot_back {a b : Term} (hr : Reduces a b) (hb : HasBot b) : HasBot a :=
  let ⟨d, hd⟩ := hb; ⟨d, hasBotWithin_backward_reduces hr hd⟩

def RankSolvedUpTo (rk : Nat) : Prop :=
  (∀ (f : PVal) (z : Arg), ValidArg z →
    1 ≤ pairRank (evalPH f.toTerm) (evalPH z.toTerm) →
    pairRank (evalPH f.toTerm) (evalPH z.toTerm) ≤ rk →
    HasBot (f.toTerm ⋅ z.toTerm)) ∧
  (∀ (x : PVal) (y z : Arg), ValidArg y → ValidArg z →
    1 ≤ tripleRank (evalPH x.toTerm) (evalPH y.toTerm) (evalPH z.toTerm) →
    tripleRank (evalPH x.toTerm) (evalPH y.toTerm) (evalPH z.toTerm) ≤ rk →
    HasBot ((S ⋅ x.toTerm ⋅ y.toTerm) ⋅ z.toTerm))

theorem rankSolved_zero : RankSolvedUpTo 0 :=
  ⟨fun _ _ _ h1 h0 => False.elim (Nat.not_succ_le_zero 0 (Nat.le_trans h1 h0)),
   fun _ _ _ _ _ h1 h0 => False.elim (Nat.not_succ_le_zero 0 (Nat.le_trans h1 h0))⟩

private theorem solve_directN1N2_step {rk : Nat} (ih_rk : RankSolvedUpTo rk)
    (x : PVal) (y z : Arg) (hy : ValidArg y) (hz : ValidArg z)
    (hdpos : 1 ≤ directN1N2Rank (evalPH x.toTerm) (evalPH z.toTerm) (deltaPH (evalPH y.toTerm) (evalPH z.toTerm)))
    (hdle : directN1N2Rank (evalPH x.toTerm) (evalPH z.toTerm) (deltaPH (evalPH y.toTerm) (evalPH z.toTerm)) ≤ rk + 1) :
    HasBot ((S ⋅ x.toTerm ⋅ y.toTerm) ⋅ z.toTerm) := by
  let n1 := deltaPH (evalPH x.toTerm) (evalPH z.toTerm)
  let n2 := deltaPH (evalPH y.toTerm) (evalPH z.toTerm)
  have hvyz : noVars (y.toTerm ⋅ z.toTerm) = true := (Bool.and_eq_true _ _).mpr ⟨hy.hv, hz.hv⟩
  have hvxz : noVars (x.toTerm ⋅ z.toTerm) = true := (Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm x, hz.hv⟩
  have hroot : Reduces ((S ⋅ x.toTerm ⋅ y.toTerm) ⋅ z.toTerm) ((x.toTerm ⋅ z.toTerm) ⋅ (y.toTerm ⋅ z.toTerm)) :=
    Reduces.next (Step.root x.toTerm y.toTerm z.toTerm) (Reduces.refl _)
  dsimp only [directN1N2Rank] at hdpos hdle
  cases hcond : (Nat.beq (kindPH (evalPH x.toTerm)) 2 && isAccPH (evalPH z.toTerm) && isAccPH n1)
  · rw [hcond, if_false_eq_true] at hdpos; exact False.elim (Nat.not_succ_le_zero 0 hdpos)
  · rw [hcond, if_true_eq_true] at hdpos hdle
    have hz_acc : isAccPH (evalPH z.toTerm) = true := and_right (and_left hcond)
    have hn1_acc : isAccPH n1 = true := and_right hcond
    cases hn2_34 : isHN34PH n2
    · obtain ⟨vz, hvz_eq⟩ := hz.acc_is_pval hz_acc; subst hvz_eq
      have hxz_ne : deltaP (evalP x.toTerm) (evalP vz.toTerm) ≠ .p37 :=
        (isAccPH_evalPH_iff (t := x.toTerm ⋅ vz.toTerm) ((Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm x, PVal.noVars_toTerm vz⟩)).mp hn1_acc
      let rap := pvalApply x vz hxz_ne
      let ⟨yn2, hred_yn2, hph_yn2, hval_yn2⟩ := mkValidArg (y.toTerm ⋅ vz.toTerm) hvyz hn2_34
      have hred_all : Reduces ((S ⋅ x.toTerm ⋅ y.toTerm) ⋅ (Arg.pval vz).toTerm) (rap.val.toTerm ⋅ yn2.toTerm) :=
        Reduces.next (Step.root x.toTerm y.toTerm vz.toTerm) (reduces_trans (reduces_left rap.red _) (reduces_right _ hred_yn2))
      have hph_rap : evalPH rap.val.toTerm = n1 := (evalPH_reduces rap.red).symm
      cases hn12_34 : isHN34PH (deltaPH n1 n2)
      · rw [hn12_34, if_false_eq_true] at hdpos hdle
        cases hpn_b : Nat.ble 1 (pairRank n1 n2)
        · rw [hpn_b, if_false_eq_true] at hdpos; exact False.elim (Nat.not_succ_le_zero 0 hdpos)
        · rw [hpn_b, if_true_eq_true] at hdle
          have hpn1 : 1 ≤ pairRank (evalPH rap.val.toTerm) (evalPH yn2.toTerm) := by
            rw [hph_rap, hph_yn2]; exact Nat.le_of_ble_eq_true hpn_b
          have hpn_rk : pairRank (evalPH rap.val.toTerm) (evalPH yn2.toTerm) ≤ rk := by
            rw [hph_rap, hph_yn2]; exact Nat.le_of_succ_le_succ hdle
          exact hasBot_back hred_all (ih_rk.1 rap.val yn2 hval_yn2 hpn1 hpn_rk)
      · have hv_prod : noVars (rap.val.toTerm ⋅ yn2.toTerm) = true := (Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm rap.val, hval_yn2.hv⟩
        have h34_prod : isHN34PH (evalPH (rap.val.toTerm ⋅ yn2.toTerm)) = true := by
          change isHN34PH (deltaPH (evalPH rap.val.toTerm) (evalPH yn2.toTerm)) = true
          rw [hph_rap, hph_yn2]; exact hn12_34
        exact hasBot_back hred_all (hasBot_from_hn34_ph hv_prod h34_prod)
    · exact hasBot_back hroot (hasBot_app_right_bot hvxz hvyz (hasBot_from_hn34_ph hvyz hn2_34))

private theorem solve_c3_step {rk x_sz : Nat} (ih_rk : RankSolvedUpTo rk)
    (same_pair : ∀ (u : PVal) (w : Arg), ValidArg w →
      1 ≤ pairRank (evalPH u.toTerm) (evalPH w.toTerm) →
      pairRank (evalPH u.toTerm) (evalPH w.toTerm) ≤ rk + 1 →
      u.size < x_sz → HasBot (u.toTerm ⋅ w.toTerm))
    (same_s1_raw : ∀ (u : PVal) (z w : Arg), ValidArg z → ValidArg w →
      z.pvalSize = 0 →
      1 ≤ tripleRank (evalPH u.toTerm) (evalPH z.toTerm) (evalPH w.toTerm) →
      tripleRank (evalPH u.toTerm) (evalPH z.toTerm) (evalPH w.toTerm) ≤ rk + 1 →
      u.size < x_sz → HasBot ((S ⋅ u.toTerm ⋅ z.toTerm) ⋅ w.toTerm))
    (x : PVal) (hx_sz : x.size = x_sz) (y z : Arg) (hy : ValidArg y) (hz : ValidArg z)
    (hcpos : 1 ≤ c3Rank (evalPH x.toTerm) (evalPH z.toTerm) (deltaPH (evalPH y.toTerm) (evalPH z.toTerm)))
    (hcle : c3Rank (evalPH x.toTerm) (evalPH z.toTerm) (deltaPH (evalPH y.toTerm) (evalPH z.toTerm)) ≤ rk + 1) :
    HasBot ((S ⋅ x.toTerm ⋅ y.toTerm) ⋅ z.toTerm) := by
  let n2 := deltaPH (evalPH y.toTerm) (evalPH z.toTerm)
  have hr_n2 : isReachPH n2 = true := isReachPH_deltaPH hy.reach hz.reach
  have hvyz : noVars (y.toTerm ⋅ z.toTerm) = true := (Bool.and_eq_true _ _).mpr ⟨hy.hv, hz.hv⟩
  have hvxz : noVars (x.toTerm ⋅ z.toTerm) = true := (Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm x, hz.hv⟩
  have hroot1 : Reduces ((S ⋅ x.toTerm ⋅ y.toTerm) ⋅ z.toTerm) ((x.toTerm ⋅ z.toTerm) ⋅ (y.toTerm ⋅ z.toTerm)) :=
    Reduces.next (Step.root x.toTerm y.toTerm z.toTerm) (Reduces.refl _)
  cases hn2_34 : isHN34PH n2
  · let ⟨yn2, hred_yn2, hph_yn2, hval_yn2⟩ := mkValidArg (y.toTerm ⋅ z.toTerm) hvyz hn2_34
    cases hx : x with
    | s =>
      exfalso; have hz0 := c3Rank_ph0 _ _ hz.reach hr_n2
      rw [hx] at hcpos; change 1 ≤ c3Rank ph0 (evalPH z.toTerm) n2 at hcpos
      rw [hz0] at hcpos; exact Nat.not_succ_le_zero 0 hcpos
    | zachos m n =>
      rw [hx] at hroot1 hvxz
      exact hasBot_back hroot1 (hasBot_app_left_bot hvxz hvyz (hasBot_zachos_app m n hz.hv))
    | s1 u =>
      have hu_lt : u.size < x_sz := by rw [← hx_sz, hx]; change u.size < u.size + 1; omega
      have hob3 := ob3_chk (evalPH u.toTerm) (evalPH z.toTerm) n2 (PVal.isAccPH_toTerm u) hz.reach hr_n2
      dsimp only [ob3_fn] at hob3
      have hcr0 : Nat.beq (c3Rank (deltaPH ph0 (evalPH u.toTerm)) (evalPH z.toTerm) n2) 0 = false := by
        rw [hx] at hcpos; change 1 ≤ c3Rank (deltaPH ph0 (evalPH u.toTerm)) (evalPH z.toTerm) n2 at hcpos
        cases hc : c3Rank (deltaPH ph0 (evalPH u.toTerm)) (evalPH z.toTerm) n2
        · rw [hc] at hcpos; cases hcpos
        · rfl
      have hcond3 : (Nat.beq (c3Rank (deltaPH ph0 (evalPH u.toTerm)) (evalPH z.toTerm) n2) 0 || isHN34PH (evalPH z.toTerm) || isHN34PH n2) = false := by
        rw [hcr0, hz.not_hn34, hn2_34]; rfl
      rw [hcond3, if_false_eq_true] at hob3
      have hred_mid : Reduces ((S ⋅ (PVal.s1 u).toTerm ⋅ y.toTerm) ⋅ z.toTerm) ((S ⋅ u.toTerm ⋅ z.toTerm) ⋅ yn2.toTerm) :=
        Reduces.next (Step.root (S ⋅ u.toTerm) y.toTerm z.toTerm) (reduces_right _ hred_yn2)
      cases hun2_34 : isHN34PH (deltaPH (evalPH u.toTerm) n2)
      · rw [hun2_34, if_false_eq_true] at hob3
        cases hbranch : (!isAccPH (deltaPH (evalPH u.toTerm) n2) && Nat.beq (kindPH (evalPH u.toTerm)) 2)
        · rw [hbranch, if_false_eq_true] at hob3
          rcases (Bool.or_eq_true _ _).mp hob3 with htop34 | htr_ok
          · have hv_mid : noVars ((S ⋅ u.toTerm ⋅ z.toTerm) ⋅ yn2.toTerm) = true :=
              (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨rfl, PVal.noVars_toTerm u⟩, hz.hv⟩, hval_yn2.hv⟩
            have h34_mid : isHN34PH (evalPH ((S ⋅ u.toTerm ⋅ z.toTerm) ⋅ yn2.toTerm)) = true := by
              change isHN34PH (deltaPH (deltaPH (deltaPH ph0 (evalPH u.toTerm)) (evalPH z.toTerm)) (evalPH yn2.toTerm)) = true
              rw [hph_yn2]; exact htop34
            exact hasBot_back hred_mid (hasBot_from_hn34_ph hv_mid h34_mid)
          · have htr1 := Nat.le_of_ble_eq_true (and_left htr_ok)
            have htr_cmp := and_right htr_ok
            have hph_n2 : n2 = evalPH yn2.toTerm := hph_yn2.symm
            rw [hx] at hcle
            change c3Rank (deltaPH ph0 (evalPH u.toTerm)) (evalPH z.toTerm) n2 ≤ rk + 1 at hcle
            rw [hph_n2] at htr1 htr_cmp hcle
            cases hz_acc : isAccPH (evalPH z.toTerm)
            · rw [hz_acc, if_false_eq_true] at htr_cmp
              have htr_le := Nat.le_trans (Nat.le_of_ble_eq_true htr_cmp) hcle
              exact hasBot_back hred_mid (same_s1_raw u z yn2 hz hval_yn2 (hz.not_acc_pvalSize_zero hz_acc) htr1 htr_le hu_lt)
            · rw [hz_acc, if_true_eq_true] at htr_cmp
              have htr_lt := Nat.le_of_ble_eq_true htr_cmp
              exact hasBot_back hred_mid (ih_rk.2 u z yn2 hz hval_yn2 htr1 (by omega))
        · rw [hbranch, if_true_eq_true] at hob3
          have hpr1 := Nat.le_of_ble_eq_true (and_left hob3)
          have hpr_le := Nat.le_of_ble_eq_true (and_right hob3)
          have hph_n2 : n2 = evalPH yn2.toTerm := hph_yn2.symm
          rw [hx] at hcle
          change c3Rank (deltaPH ph0 (evalPH u.toTerm)) (evalPH z.toTerm) n2 ≤ rk + 1 at hcle
          rw [hph_n2] at hpr1 hpr_le hcle
          have hbot_u := same_pair u yn2 hval_yn2 hpr1 (Nat.le_trans hpr_le hcle) hu_lt
          have hstep2 : Reduces ((S ⋅ u.toTerm ⋅ z.toTerm) ⋅ yn2.toTerm) ((u.toTerm ⋅ yn2.toTerm) ⋅ (z.toTerm ⋅ yn2.toTerm)) :=
            Reduces.next (Step.root u.toTerm z.toTerm yn2.toTerm) (Reduces.refl _)
          exact hasBot_back (reduces_trans hred_mid hstep2)
            (hasBot_app_left_bot ((Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm u, hval_yn2.hv⟩)
              ((Bool.and_eq_true _ _).mpr ⟨hz.hv, hval_yn2.hv⟩) hbot_u)
      · have hv_un2 : noVars (u.toTerm ⋅ yn2.toTerm) = true := (Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm u, hval_yn2.hv⟩
        have h34_un2 : isHN34PH (evalPH (u.toTerm ⋅ yn2.toTerm)) = true := by
          change isHN34PH (deltaPH (evalPH u.toTerm) (evalPH yn2.toTerm)) = true; rw [hph_yn2]; exact hun2_34
        have hstep2 : Reduces ((S ⋅ u.toTerm ⋅ z.toTerm) ⋅ yn2.toTerm) ((u.toTerm ⋅ yn2.toTerm) ⋅ (z.toTerm ⋅ yn2.toTerm)) :=
          Reduces.next (Step.root u.toTerm z.toTerm yn2.toTerm) (Reduces.refl _)
        exact hasBot_back (reduces_trans hred_mid hstep2)
          (hasBot_app_left_bot hv_un2 ((Bool.and_eq_true _ _).mpr ⟨hz.hv, hval_yn2.hv⟩) (hasBot_from_hn34_ph hv_un2 h34_un2))
    | s2 x1 x2 =>
      have hk2 := (kindPH_s2 _ _ (PVal.isAccPH_toTerm x1) (PVal.isAccPH_toTerm x2)).2
      have hob4 := ob4_chk (evalPH (PVal.s2 x1 x2).toTerm) (evalPH z.toTerm) n2 (PVal.isAccPH_toTerm (.s2 x1 x2)) hz.reach hr_n2
      dsimp only [ob4_fn] at hob4
      rw [hx] at hcpos hcle
      have hcr0 : Nat.beq (c3Rank (evalPH (PVal.s2 x1 x2).toTerm) (evalPH z.toTerm) n2) 0 = false := by
        change 1 ≤ c3Rank (evalPH (PVal.s2 x1 x2).toTerm) (evalPH z.toTerm) n2 at hcpos
        cases hc : c3Rank (evalPH (PVal.s2 x1 x2).toTerm) (evalPH z.toTerm) n2
        · rw [hc] at hcpos; cases hcpos
        · rfl
      have hk2_f : (!Nat.beq (kindPH (evalPH (PVal.s2 x1 x2).toTerm)) 2) = false := by
        change (!Nat.beq (kindPH (deltaPH (deltaPH ph0 (evalPH x1.toTerm)) (evalPH x2.toTerm))) 2) = false
        rw [hk2]; rfl
      have hcond4 : (Nat.beq (c3Rank (evalPH (PVal.s2 x1 x2).toTerm) (evalPH z.toTerm) n2) 0 || !Nat.beq (kindPH (evalPH (PVal.s2 x1 x2).toTerm)) 2 || isHN34PH (evalPH z.toTerm) || isHN34PH n2) = false := by
        rw [hcr0, hk2_f, hz.not_hn34, hn2_34]; rfl
      rw [hcond4, if_false_eq_true] at hob4
      have ⟨hpair_acc, hall_bits⟩ := (Bool.and_eq_true _ _).mp hob4
      have ⟨hz_acc, hxz_acc⟩ := (Bool.and_eq_true _ _).mp hpair_acc
      obtain ⟨vz, hvz_eq⟩ := hz.acc_is_pval hz_acc; subst hvz_eq
      have hfw_ne : deltaP (evalP (PVal.s2 x1 x2).toTerm) (evalP vz.toTerm) ≠ .p37 :=
        (isAccPH_evalPH_iff (t := (PVal.s2 x1 x2).toTerm ⋅ vz.toTerm) ((Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm (.s2 x1 x2), PVal.noVars_toTerm vz⟩)).mp hxz_acc
      let rap := pvalApply (.s2 x1 x2) vz hfw_ne
      have hred_all : Reduces ((S ⋅ (PVal.s2 x1 x2).toTerm ⋅ y.toTerm) ⋅ (Arg.pval vz).toTerm) (rap.val.toTerm ⋅ yn2.toTerm) :=
        Reduces.next (Step.root (PVal.s2 x1 x2).toTerm y.toTerm vz.toTerm) (reduces_trans (reduces_left rap.red _) (reduces_right _ hred_yn2))
      cases hrv : rap.val with
      | s => exfalso; have hph0 : evalPH rap.val.toTerm = ph0 := by rw [hrv]; rfl
             rw [← evalPH_reduces rap.red] at hph0
             change deltaPH (evalPH (PVal.s2 x1 x2).toTerm) (evalPH vz.toTerm) = ph0 at hph0
             exact deltaPH_ne_ph0 _ _ hph0
      | s1 w0 => obtain ⟨hbad, _⟩ := rap.s1_imp w0 hrv; cases hbad
      | zachos m n => rw [hrv] at hred_all; exact hasBot_back hred_all (hasBot_zachos_app m n hval_yn2.hv)
      | s2 a b =>
        have hbit := out2dAllPairs_sound hall_bits (rap.s2_mem a b hrv)
        rw [hrv] at hred_all
        rcases (Bool.or_eq_true _ _).mp hbit with h34_ab | htr_ab
        · have hv_ab : noVars ((S ⋅ a.toTerm ⋅ b.toTerm) ⋅ yn2.toTerm) = true := (Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm (.s2 a b), hval_yn2.hv⟩
          have h34_term : isHN34PH (evalPH ((S ⋅ a.toTerm ⋅ b.toTerm) ⋅ yn2.toTerm)) = true := by
            change isHN34PH (deltaPH (deltaPH (deltaPH ph0 (evalPH a.toTerm)) (evalPH b.toTerm)) (evalPH yn2.toTerm)) = true
            rw [hph_yn2]; exact h34_ab
          exact hasBot_back hred_all (hasBot_from_hn34_ph hv_ab h34_term)
        · have htr1 := Nat.le_of_ble_eq_true (and_left htr_ab)
          have htr_lt := Nat.le_of_ble_eq_true (and_right htr_ab)
          have hph_n2 : n2 = evalPH yn2.toTerm := hph_yn2.symm
          change c3Rank (evalPH (PVal.s2 x1 x2).toTerm) (evalPH (Arg.pval vz).toTerm) n2 ≤ rk + 1 at hcle
          rw [hph_n2] at htr1 htr_lt hcle
          have htr_le : tripleRank (evalPH a.toTerm) (evalPH (Arg.pval b).toTerm) (evalPH yn2.toTerm) ≤ rk := by
            change tripleRank (evalPH a.toTerm) (evalPH b.toTerm) (evalPH yn2.toTerm) ≤ rk; omega
          exact hasBot_back hred_all (ih_rk.2 a (.pval b) yn2 (validArg_pval b) hval_yn2 htr1 htr_le)
  · exact hasBot_back hroot1 (hasBot_app_right_bot hvxz hvyz (hasBot_from_hn34_ph hvyz hn2_34))

/-- **Single-Branch `rankSolved_step` (No Odd/Even Parity Split!)**:
    Uses the unified measure `2 * (x.size + y.pvalSize) + 1` at EVERY rank `rk + 1`. -/
theorem rankSolved_step {rk : Nat} (ih_rk : RankSolvedUpTo rk) : RankSolvedUpTo (rk + 1) := by
  have hM : ∀ (M : Nat),
      (∀ (f : PVal) (z : Arg), 2 * f.size ≤ M → ValidArg z →
        1 ≤ pairRank (evalPH f.toTerm) (evalPH z.toTerm) →
        pairRank (evalPH f.toTerm) (evalPH z.toTerm) ≤ rk + 1 →
        HasBot (f.toTerm ⋅ z.toTerm)) ∧
      (∀ (x : PVal) (y z : Arg), 2 * (x.size + y.pvalSize) + 1 ≤ M → ValidArg y → ValidArg z →
        1 ≤ tripleRank (evalPH x.toTerm) (evalPH y.toTerm) (evalPH z.toTerm) →
        tripleRank (evalPH x.toTerm) (evalPH y.toTerm) (evalPH z.toTerm) ≤ rk + 1 →
        HasBot ((S ⋅ x.toTerm ⋅ y.toTerm) ⋅ z.toTerm)) := by
    intro M; induction M with
    | zero =>
      refine ⟨fun f _ hle => False.elim (by have hf_pos := PVal.size_pos f; omega),
              fun _ _ _ hle => False.elim (by omega)⟩
    | succ M' ihM =>
      refine ⟨?_, ?_⟩
      · intro f z hsz hz hpos hle
        cases hf : f with
        | s =>
          have hob1 := and_left (ob1_chk ph0 (evalPH z.toTerm) (PVal.isAccPH_toTerm .s) hz.reach)
          rw [hf] at hpos; change 1 ≤ pairRank ph0 (evalPH z.toTerm) at hpos
          rw [Nat.ble_eq.mpr hpos, if_true_eq_true] at hob1
          have hk2 := Nat.eq_of_beq_eq_true (and_left hob1); cases hk2
        | s1 u =>
          have hk1 := (kindPH_s1 (evalPH u.toTerm) (PVal.isAccPH_toTerm u)).2
          have hob1 := and_left (ob1_chk (evalPH (PVal.s1 u).toTerm) (evalPH z.toTerm) (PVal.isAccPH_toTerm (.s1 u)) hz.reach)
          rw [hf] at hpos; rw [Nat.ble_eq.mpr hpos, if_true_eq_true] at hob1
          have hk2 : kindPH (deltaPH ph0 (evalPH u.toTerm)) = 2 := Nat.eq_of_beq_eq_true (and_left hob1)
          rw [hk1] at hk2; cases hk2
        | zachos m n => exact hasBot_zachos_app m n hz.hv
        | s2 a b =>
          rw [hf] at hpos hle hsz
          cases h34 : isHN34PH (deltaPH (evalPH (PVal.s2 a b).toTerm) (evalPH z.toTerm))
          · have hob2 := ob2_chk (evalPH a.toTerm) (evalPH b.toTerm) (evalPH z.toTerm) (PVal.isAccPH_toTerm a) (PVal.isAccPH_toTerm b) hz.reach
            dsimp only [ob2_fn] at hob2
            have hpr0 : Nat.beq (pairRank (evalPH (PVal.s2 a b).toTerm) (evalPH z.toTerm)) 0 = false := by
              cases hp : pairRank (evalPH (PVal.s2 a b).toTerm) (evalPH z.toTerm)
              · rw [hp] at hpos; cases hpos
              · rfl
            have hc2 : (Nat.beq (pairRank (evalPH (PVal.s2 a b).toTerm) (evalPH z.toTerm)) 0 ||
                isHN34PH (evalPH z.toTerm) || isHN34PH (deltaPH (evalPH (PVal.s2 a b).toTerm) (evalPH z.toTerm))) = false := by
              rw [hpr0, hz.not_hn34, h34]; rfl
            change (if (Nat.beq (pairRank (evalPH (PVal.s2 a b).toTerm) (evalPH z.toTerm)) 0 ||
                isHN34PH (evalPH z.toTerm) || isHN34PH (deltaPH (evalPH (PVal.s2 a b).toTerm) (evalPH z.toTerm))) = true then true else _) = true at hob2
            rw [hc2, if_false_eq_true] at hob2
            have htr1 := Nat.le_of_ble_eq_true (and_left hob2)
            have htr_le := Nat.le_of_ble_eq_true (and_right hob2)
            have hsub_M : 2 * (a.size + (Arg.pval b).pvalSize) + 1 ≤ M' := by
              change 2 * (a.size + b.size + 1) ≤ M' + 1 at hsz
              change 2 * (a.size + b.size) + 1 ≤ M'; omega
            exact ihM.2 a (.pval b) z hsub_M (validArg_pval b) hz htr1 (Nat.le_trans htr_le hle)
          · exact hasBot_from_hn34_ph ((Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm (.s2 a b), hz.hv⟩) h34
      · intro x y z hsz hy hz hpos hle
        have hvxz : noVars (x.toTerm ⋅ z.toTerm) = true := (Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm x, hz.hv⟩
        have hvyz : noVars (y.toTerm ⋅ z.toTerm) = true := (Bool.and_eq_true _ _).mpr ⟨hy.hv, hz.hv⟩
        have hroot : Reduces ((S ⋅ x.toTerm ⋅ y.toTerm) ⋅ z.toTerm) ((x.toTerm ⋅ z.toTerm) ⋅ (y.toTerm ⋅ z.toTerm)) :=
          Reduces.next (Step.root x.toTerm y.toTerm z.toTerm) (Reduces.refl _)
        rcases tripleRank_cases hpos hle with hn2 | hn1 | hL | hR | hD | hC
        · exact hasBot_back hroot (hasBot_app_right_bot hvxz hvyz (hasBot_from_hn34_ph hvyz hn2))
        · exact hasBot_back hroot (hasBot_app_left_bot hvxz hvyz (hasBot_from_hn34_ph hvxz hn1))
        · exact hasBot_back hroot (hasBot_app_left_bot hvxz hvyz (ihM.1 x z (by omega) hz hL.1 hL.2))
        · obtain ⟨vy, hvy_eq⟩ := hy.acc_is_pval hR.1; subst hvy_eq
          have hx_pos := PVal.size_pos x
          have hsub_M : 2 * vy.size ≤ M' := by change 2 * (x.size + vy.size) + 1 ≤ M' + 1 at hsz; omega
          exact hasBot_back hroot (hasBot_app_right_bot hvxz hvyz (ihM.1 vy z hsub_M hz hR.2.1 hR.2.2))
        · exact solve_directN1N2_step ih_rk x y z hy hz hD.1 hD.2
        · exact solve_c3_step ih_rk
            (fun u w hw hp1 hple hult => ihM.1 u w (by omega) hw hp1 hple)
            (fun u z' w' hz' hw' hpz0 ht1 htle hult => ihM.2 u z' w' (by rw [hpz0]; omega) hz' hw' ht1 htle)
            x rfl y z hy hz hC.1 hC.2
  exact ⟨fun f z => (hM (2 * f.size)).1 f z (Nat.le_refl _),
         fun x y z => (hM (2 * (x.size + y.pvalSize) + 1)).2 x y z (Nat.le_refl _)⟩

theorem rankSolved_all : ∀ k : Nat, RankSolvedUpTo k
  | 0 => rankSolved_zero
  | k + 1 => rankSolved_step (rankSolved_all k)

theorem pval_root_pair_hasBot (f z : PVal) (h37 : evalP (f.toTerm ⋅ z.toTerm) = .p37) :
    HasBot (f.toTerm ⋅ z.toTerm) := by
  have hnot_acc : (!isAccPH (deltaPH (evalPH f.toTerm) (evalPH z.toTerm))) = true := by
    cases hc : isAccPH (deltaPH (evalPH f.toTerm) (evalPH z.toTerm)) with
    | false => rfl
    | true =>
      exfalso; exact ((isAccPH_evalPH_iff (t := f.toTerm ⋅ z.toTerm)
        ((Bool.and_eq_true _ _).mpr ⟨PVal.noVars_toTerm f, PVal.noVars_toTerm z⟩)).mp hc) h37
  have hr := and_right (ob1_chk (evalPH f.toTerm) (evalPH z.toTerm) (PVal.isAccPH_toTerm f) (evalPH_isReach (PVal.noVars_toTerm z)))
  have hc : (isAccPH (evalPH f.toTerm) && isAccPH (evalPH z.toTerm) && !isAccPH (deltaPH (evalPH f.toTerm) (evalPH z.toTerm))) = true := by
    rw [PVal.isAccPH_toTerm f, PVal.isAccPH_toTerm z, hnot_acc]; rfl
  rw [hc, if_true_eq_true] at hr
  exact (rankSolved_all 10).1 f (.pval z) (validArg_pval z) (Nat.le_of_ble_eq_true (and_left hr)) (Nat.le_of_ble_eq_true (and_right hr))

theorem evalP_eq_p37_implies_hasBot : ∀ {t : Term}, noVars t = true → evalP t = .p37 → HasBot t
  | .s, _, h37 => by cases h37
  | .var _, hv, _ => by cases hv
  | .app a b, hv, h37 => by
    have ⟨hva, hvb⟩ := (Bool.and_eq_true _ _).mp hv
    cases ha37 : beqP (evalP a) .p37 with
    | true => exact hasBot_app_left_bot hva hvb (evalP_eq_p37_implies_hasBot hva (eq_of_beqP ha37))
    | false =>
      cases hb37 : beqP (evalP b) .p37 with
      | true => exact hasBot_app_right_bot hva hvb (evalP_eq_p37_implies_hasBot hvb (eq_of_beqP hb37))
      | false =>
        let ⟨va, hra⟩ := toPVal a hva (ne_of_beqP_false ha37)
        let ⟨vb, hrb⟩ := toPVal b hvb (ne_of_beqP_false hb37)
        have hprod37 : evalP (va.toTerm ⋅ vb.toTerm) = .p37 := by
          change deltaP (evalP va.toTerm) (evalP vb.toTerm) = .p37
          rw [← evalP_reduces hra, ← evalP_reduces hrb]; exact h37
        have hred : Reduces (a ⋅ b) (va.toTerm ⋅ vb.toTerm) :=
          reduces_trans (reduces_left hra b) (reduces_right va.toTerm hrb)
        exact hasBot_back hred (pval_root_pair_hasBot va vb hprod37)

/-- **Barendregt, Endrullis, Klop & Waldmann's Open Question 5 (Simplified Rank-10 Proof)**:
    A closed pure-`S` combinator `t` is Böhm-tree productive (`Productive t`) if and only if
    the 39-state finite `S`-algebra `A_P` accepts `t` (`evalP t ≠ .p37`). -/
theorem barendregt_open_question_5_simplified {t : Term} (hv : noVars t = true) :
    Productive t ↔ evalP t ≠ .p37 :=
  ⟨fun hprod h37 => hprod (evalP_eq_p37_implies_hasBot hv h37), evalP_ne_p37_implies_productive hv⟩

theorem productive_or_hasBot_closed_simplified {t : Term} (hv : noVars t = true) :
    Productive t ∨ HasBot t :=
  match hb : beqP (evalP t) .p37 with
  | true => Or.inr (evalP_eq_p37_implies_hasBot hv (eq_of_beqP hb))
  | false => Or.inl (evalP_ne_p37_implies_productive hv (ne_of_beqP_false hb))

/-! ## 5. Exact 113-State Myhill–Nerode Minimality Corollaries -/

private theorem obs3_eq_iff_same_semantics {u v : Term} (hvu : noVars u = true) (hvv : noVars v = true) :
    ((Productive u ↔ Productive v) ∧ (HasHNF u ↔ HasHNF v)) →
    obs3Idx (phIdx (evalPH u)) = obs3Idx (phIdx (evalPH v)) := by
  intro ⟨hP, hH⟩
  have hru := evalPH_isReach hvu; have hrv := evalPH_isReach hvv
  have hpu : Productive u ↔ isAccIdx (phIdx (evalPH u)) = true :=
    (barendregt_open_question_5_simplified hvu).trans (isAccPH_evalPH_iff hvu).symm
  have hpv : Productive v ↔ isAccIdx (phIdx (evalPH v)) = true :=
    (barendregt_open_question_5_simplified hvv).trans (isAccPH_evalPH_iff hvv).symm
  have hhu : ¬ HasHNF u ↔ isHN34Idx (phIdx (evalPH u)) = true := by
    rw [(barendregt_open_problem_10_simplified hvu).1, ← (reach_1d_props hru).2.2.2.1]
    unfold isHN34PH; change ¬ evalHN u ≠ .hn34 ↔ beq_StateHN (evalHN u) .hn34 = true
    cases hb : beq_StateHN (evalHN u) .hn34 with
    | true => exact ⟨fun _ => rfl, fun _ hne => hne (eq_of_beq_StateHN hb)⟩
    | false => exact ⟨fun hnn => False.elim (hnn (ne_of_beq_StateHN_false hb)), fun h => by cases h⟩
  have hhv : ¬ HasHNF v ↔ isHN34Idx (phIdx (evalPH v)) = true := by
    rw [(barendregt_open_problem_10_simplified hvv).1, ← (reach_1d_props hrv).2.2.2.1]
    unfold isHN34PH; change ¬ evalHN v ≠ .hn34 ↔ beq_StateHN (evalHN v) .hn34 = true
    cases hb : beq_StateHN (evalHN v) .hn34 with
    | true => exact ⟨fun _ => rfl, fun _ hne => hne (eq_of_beq_StateHN hb)⟩
    | false => exact ⟨fun hnn => False.elim (hnn (ne_of_beq_StateHN_false hb)), fun h => by cases h⟩
  unfold obs3Idx
  cases hu112 : Nat.beq (phIdx (evalPH u)) 112 with
  | true =>
    have hv112 : Nat.beq (phIdx (evalPH v)) 112 = true := hhv.mp (fun hh => (hhu.mpr hu112) (hH.mpr hh))
    rw [hv112]; rfl
  | false =>
    have hv112 : Nat.beq (phIdx (evalPH v)) 112 = false := by
      cases hc : Nat.beq (phIdx (evalPH v)) 112 with
      | false => rfl
      | true => exfalso; have hbad := hhu.mp (fun hh => (hhv.mpr hc) (hH.mp hh)); unfold isHN34Idx at hbad; rw [hu112] at hbad; cases hbad
    cases hua : isAccIdx (phIdx (evalPH u)) with
    | true =>
      have hva : isAccIdx (phIdx (evalPH v)) = true := hpv.mp (hP.mp (hpu.mpr hua))
      rw [hv112, hva]
    | false =>
      have hva : isAccIdx (phIdx (evalPH v)) = false := by
        cases hc : isAccIdx (phIdx (evalPH v)) with
        | false => rfl
        | true => exfalso; have hbad := hpu.mp (hP.mpr (hpv.mpr hc)); rw [hua] at hbad; cases hbad
      rw [hv112, hva]

private theorem nerode_sep_idx {i j : Nat} (hi : i < 113) (hj : j < 113) (hne : i ≠ j) :
    ∃ k, k < 17 ∧ obs3Idx (evalCtxOpsIdx (sepCtxOps k) i) ≠ obs3Idx (evalCtxOpsIdx (sepCtxOps k) j) := by
  if hlt : i < j then
    have h := checkNat1_sound 113 _ (nerode_sep_all hi) hj
    have hble : Nat.ble j i = false := by cases hc : Nat.ble j i with | false => rfl | true => have hji := Nat.le_of_ble_eq_true hc; exact False.elim (by omega)
    rw [hble, Bool.false_or] at h
    obtain ⟨k, hk17, hneq⟩ := existsNat_sound _ h
    exact ⟨k, hk17, fun heq => by rw [heq, Nat.beq_refl] at hneq; cases hneq⟩
  else
    have hgt : j < i := by omega
    have h := checkNat1_sound 113 _ (nerode_sep_all hj) hi
    have hble : Nat.ble i j = false := by cases hc : Nat.ble i j with | false => rfl | true => have hij := Nat.le_of_ble_eq_true hc; exact False.elim (by omega)
    rw [hble, Bool.false_or] at h
    obtain ⟨k, hk17, hneq⟩ := existsNat_sound _ h
    exact ⟨k, hk17, fun heq => by rw [heq.symm, Nat.beq_refl] at hneq; cases hneq⟩

/-- **Exact 113-State Myhill–Nerode Minimality of `PH` (`A_P × A_HN`)**:
    For ANY two closed pure-`S` combinators `t₁, t₂` with `evalPH t₁ ≠ evalPH t₂`, one of the
    17 explicit closed contexts `applySepCtx k` (`k < 17`) distinguishes `applySepCtx k t₁`
    from `applySepCtx k t₂` on `(Productive ·, HasHNF ·)`. -/
theorem ph_113_nerode_minimal {t1 t2 : Term} (hv1 : noVars t1 = true) (hv2 : noVars t2 = true)
    (hne : evalPH t1 ≠ evalPH t2) :
    ∃ k, k < 17 ∧ ¬ ((Productive (applySepCtx k t1) ↔ Productive (applySepCtx k t2)) ∧
                     (HasHNF (applySepCtx k t1) ↔ HasHNF (applySepCtx k t2))) := by
  have hr1 := evalPH_isReach hv1; have hr2 := evalPH_isReach hv2
  have hne_i : phIdx (evalPH t1) ≠ phIdx (evalPH t2) := fun heq => by
    have h := congrArg ofPhIdx heq
    rw [(ofPhIdx_phIdx hr1).1, (ofPhIdx_phIdx hr2).1] at h; exact hne h
  obtain ⟨k, hk17, hdiff⟩ := nerode_sep_idx (phIdx_lt_113 hr1) (phIdx_lt_113 hr2) hne_i
  have hall := checkNat1_sound 17 _ sepCtxOps_lt_chk hk17
  have ⟨hvk1, hik1⟩ := applyCtxOps_spec (sepCtxOps k) hall hv1
  have ⟨hvk2, hik2⟩ := applyCtxOps_spec (sepCtxOps k) hall hv2
  refine ⟨k, hk17, fun hsame => hdiff ?_⟩
  have heq_obs := obs3_eq_iff_same_semantics hvk1 hvk2 hsame
  unfold applySepCtx at heq_obs; rwa [hik1, hik2] at heq_obs

/-- **Universal 113-State Quotient Lower Bound**:
    Every `S`-algebra homomorphism `evalQ : Term → Q` on closed terms (`evalQ (a ⋅ b) = δQ (evalQ a) (evalQ b)`)
    through which `(Productive, HasHNF)` factors takes **113 pairwise distinct values** on `witTerm 0 .. witTerm 112`. -/
theorem ph_113_quotient_lower_bound {Q : Type} (evalQ : Term → Q) (δQ : Q → Q → Q)
    (hhom : ∀ a b : Term, evalQ (a ⋅ b) = δQ (evalQ a) (evalQ b))
    (hdecides : ∀ u v : Term, noVars u = true → noVars v = true → evalQ u = evalQ v →
      (Productive u ↔ Productive v) ∧ (HasHNF u ↔ HasHNF v)) :
    ∀ i j : Nat, i < 113 → j < 113 → i ≠ j → evalQ (witTerm i) ≠ evalQ (witTerm j) := by
  intro i j hi hj hne heqQ
  have ⟨hvi, hii⟩ := witTerm_spec hi
  have ⟨hvj, hij⟩ := witTerm_spec hj
  have hne_ph : evalPH (witTerm i) ≠ evalPH (witTerm j) := fun hph => hne (hii.symm.trans ((congrArg phIdx hph).trans hij))
  obtain ⟨k, hk17, hsep⟩ := ph_113_nerode_minimal hvi hvj hne_ph
  have hall := checkNat1_sound 17 _ sepCtxOps_lt_chk hk17
  have ⟨hvki, _⟩ := applyCtxOps_spec (sepCtxOps k) hall hvi
  have ⟨hvkj, _⟩ := applyCtxOps_spec (sepCtxOps k) hall hvj
  exact hsep (hdecides _ _ hvki hvkj (applyCtxOps_congr evalQ δQ hhom (sepCtxOps k) heqQ))

end SimplifiedQ10Q5

#print axioms SimplifiedQ10Q5.evalP_ne_p37_implies_productive
#print axioms SimplifiedQ10Q5.barendregt_open_question_5_simplified
#print axioms SimplifiedQ10Q5.productive_or_hasBot_closed_simplified
#print axioms SimplifiedQ10Q5.ph_113_nerode_minimal
#print axioms SimplifiedQ10Q5.ph_113_quotient_lower_bound

