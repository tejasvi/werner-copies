/- NPT.K4.ClsLen3 — every slice list of the shared family-40/04 class data has `24^4 = 331776` entries: each of
its 24 chunks has 13824 entries by the chunk witness checks (`witGoKS_sound`). -/
import NPT.K4.ClsSlices3
import NPT.K4.Classes.WitK3

open NPT.K4.Classes

namespace NPT.K4.D3T4979

theorem slen3_0 : cls3_0.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_0_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_0_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_0_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_0_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_0_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_0_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_0_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_0_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_0_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_0_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_0_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_0_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_0_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_0_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_0_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_0_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_0_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_0_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_0_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_0_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_0_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_0_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_0_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_0_23).2
  simp only [cls3_0, List.length_append]
  omega

theorem slen3_1 : cls3_1.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_1_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_1_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_1_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_1_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_1_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_1_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_1_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_1_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_1_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_1_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_1_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_1_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_1_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_1_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_1_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_1_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_1_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_1_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_1_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_1_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_1_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_1_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_1_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_1_23).2
  simp only [cls3_1, List.length_append]
  omega

theorem slen3_2 : cls3_2.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_2_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_2_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_2_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_2_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_2_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_2_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_2_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_2_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_2_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_2_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_2_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_2_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_2_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_2_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_2_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_2_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_2_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_2_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_2_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_2_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_2_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_2_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_2_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_2_23).2
  simp only [cls3_2, List.length_append]
  omega

theorem slen3_3 : cls3_3.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_3_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_3_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_3_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_3_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_3_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_3_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_3_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_3_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_3_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_3_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_3_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_3_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_3_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_3_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_3_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_3_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_3_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_3_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_3_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_3_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_3_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_3_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_3_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_3_23).2
  simp only [cls3_3, List.length_append]
  omega

theorem slen3_4 : cls3_4.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_4_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_4_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_4_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_4_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_4_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_4_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_4_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_4_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_4_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_4_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_4_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_4_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_4_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_4_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_4_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_4_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_4_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_4_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_4_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_4_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_4_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_4_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_4_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_4_23).2
  simp only [cls3_4, List.length_append]
  omega

theorem slen3_5 : cls3_5.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_5_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_5_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_5_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_5_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_5_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_5_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_5_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_5_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_5_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_5_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_5_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_5_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_5_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_5_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_5_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_5_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_5_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_5_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_5_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_5_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_5_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_5_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_5_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_5_23).2
  simp only [cls3_5, List.length_append]
  omega

theorem slen3_6 : cls3_6.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_6_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_6_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_6_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_6_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_6_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_6_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_6_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_6_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_6_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_6_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_6_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_6_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_6_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_6_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_6_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_6_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_6_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_6_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_6_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_6_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_6_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_6_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_6_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_6_23).2
  simp only [cls3_6, List.length_append]
  omega

theorem slen3_7 : cls3_7.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_7_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_7_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_7_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_7_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_7_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_7_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_7_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_7_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_7_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_7_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_7_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_7_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_7_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_7_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_7_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_7_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_7_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_7_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_7_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_7_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_7_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_7_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_7_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_7_23).2
  simp only [cls3_7, List.length_append]
  omega

theorem slen3_8 : cls3_8.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_8_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_8_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_8_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_8_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_8_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_8_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_8_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_8_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_8_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_8_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_8_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_8_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_8_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_8_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_8_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_8_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_8_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_8_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_8_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_8_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_8_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_8_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_8_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_8_23).2
  simp only [cls3_8, List.length_append]
  omega

theorem slen3_9 : cls3_9.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_9_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_9_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_9_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_9_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_9_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_9_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_9_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_9_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_9_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_9_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_9_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_9_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_9_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_9_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_9_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_9_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_9_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_9_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_9_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_9_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_9_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_9_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_9_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_9_23).2
  simp only [cls3_9, List.length_append]
  omega

theorem slen3_10 : cls3_10.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_10_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_10_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_10_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_10_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_10_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_10_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_10_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_10_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_10_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_10_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_10_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_10_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_10_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_10_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_10_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_10_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_10_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_10_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_10_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_10_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_10_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_10_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_10_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_10_23).2
  simp only [cls3_10, List.length_append]
  omega

theorem slen3_11 : cls3_11.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_11_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_11_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_11_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_11_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_11_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_11_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_11_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_11_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_11_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_11_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_11_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_11_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_11_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_11_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_11_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_11_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_11_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_11_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_11_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_11_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_11_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_11_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_11_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_11_23).2
  simp only [cls3_11, List.length_append]
  omega

theorem slen3_12 : cls3_12.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_12_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_12_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_12_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_12_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_12_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_12_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_12_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_12_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_12_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_12_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_12_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_12_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_12_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_12_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_12_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_12_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_12_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_12_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_12_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_12_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_12_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_12_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_12_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_12_23).2
  simp only [cls3_12, List.length_append]
  omega

theorem slen3_13 : cls3_13.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_13_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_13_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_13_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_13_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_13_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_13_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_13_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_13_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_13_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_13_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_13_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_13_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_13_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_13_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_13_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_13_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_13_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_13_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_13_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_13_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_13_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_13_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_13_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_13_23).2
  simp only [cls3_13, List.length_append]
  omega

theorem slen3_14 : cls3_14.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_14_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_14_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_14_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_14_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_14_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_14_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_14_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_14_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_14_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_14_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_14_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_14_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_14_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_14_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_14_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_14_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_14_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_14_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_14_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_14_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_14_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_14_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_14_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_14_23).2
  simp only [cls3_14, List.length_append]
  omega

theorem slen3_15 : cls3_15.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_15_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_15_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_15_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_15_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_15_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_15_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_15_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_15_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_15_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_15_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_15_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_15_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_15_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_15_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_15_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_15_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_15_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_15_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_15_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_15_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_15_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_15_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_15_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_15_23).2
  simp only [cls3_15, List.length_append]
  omega

theorem slen3_16 : cls3_16.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_16_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_16_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_16_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_16_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_16_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_16_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_16_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_16_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_16_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_16_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_16_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_16_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_16_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_16_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_16_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_16_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_16_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_16_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_16_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_16_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_16_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_16_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_16_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_16_23).2
  simp only [cls3_16, List.length_append]
  omega

theorem slen3_17 : cls3_17.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_17_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_17_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_17_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_17_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_17_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_17_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_17_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_17_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_17_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_17_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_17_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_17_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_17_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_17_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_17_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_17_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_17_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_17_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_17_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_17_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_17_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_17_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_17_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_17_23).2
  simp only [cls3_17, List.length_append]
  omega

theorem slen3_18 : cls3_18.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_18_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_18_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_18_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_18_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_18_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_18_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_18_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_18_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_18_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_18_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_18_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_18_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_18_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_18_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_18_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_18_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_18_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_18_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_18_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_18_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_18_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_18_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_18_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_18_23).2
  simp only [cls3_18, List.length_append]
  omega

theorem slen3_19 : cls3_19.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_19_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_19_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_19_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_19_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_19_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_19_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_19_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_19_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_19_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_19_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_19_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_19_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_19_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_19_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_19_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_19_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_19_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_19_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_19_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_19_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_19_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_19_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_19_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_19_23).2
  simp only [cls3_19, List.length_append]
  omega

theorem slen3_20 : cls3_20.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_20_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_20_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_20_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_20_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_20_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_20_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_20_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_20_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_20_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_20_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_20_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_20_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_20_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_20_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_20_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_20_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_20_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_20_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_20_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_20_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_20_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_20_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_20_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_20_23).2
  simp only [cls3_20, List.length_append]
  omega

theorem slen3_21 : cls3_21.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_21_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_21_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_21_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_21_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_21_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_21_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_21_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_21_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_21_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_21_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_21_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_21_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_21_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_21_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_21_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_21_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_21_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_21_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_21_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_21_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_21_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_21_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_21_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_21_23).2
  simp only [cls3_21, List.length_append]
  omega

theorem slen3_22 : cls3_22.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_22_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_22_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_22_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_22_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_22_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_22_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_22_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_22_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_22_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_22_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_22_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_22_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_22_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_22_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_22_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_22_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_22_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_22_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_22_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_22_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_22_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_22_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_22_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_22_23).2
  simp only [cls3_22, List.length_append]
  omega

theorem slen3_23 : cls3_23.length = 331776 := by
  have h0 := (witGoKS_sound _ _ _ _ witK3_23_0).2
  have h1 := (witGoKS_sound _ _ _ _ witK3_23_1).2
  have h2 := (witGoKS_sound _ _ _ _ witK3_23_2).2
  have h3 := (witGoKS_sound _ _ _ _ witK3_23_3).2
  have h4 := (witGoKS_sound _ _ _ _ witK3_23_4).2
  have h5 := (witGoKS_sound _ _ _ _ witK3_23_5).2
  have h6 := (witGoKS_sound _ _ _ _ witK3_23_6).2
  have h7 := (witGoKS_sound _ _ _ _ witK3_23_7).2
  have h8 := (witGoKS_sound _ _ _ _ witK3_23_8).2
  have h9 := (witGoKS_sound _ _ _ _ witK3_23_9).2
  have h10 := (witGoKS_sound _ _ _ _ witK3_23_10).2
  have h11 := (witGoKS_sound _ _ _ _ witK3_23_11).2
  have h12 := (witGoKS_sound _ _ _ _ witK3_23_12).2
  have h13 := (witGoKS_sound _ _ _ _ witK3_23_13).2
  have h14 := (witGoKS_sound _ _ _ _ witK3_23_14).2
  have h15 := (witGoKS_sound _ _ _ _ witK3_23_15).2
  have h16 := (witGoKS_sound _ _ _ _ witK3_23_16).2
  have h17 := (witGoKS_sound _ _ _ _ witK3_23_17).2
  have h18 := (witGoKS_sound _ _ _ _ witK3_23_18).2
  have h19 := (witGoKS_sound _ _ _ _ witK3_23_19).2
  have h20 := (witGoKS_sound _ _ _ _ witK3_23_20).2
  have h21 := (witGoKS_sound _ _ _ _ witK3_23_21).2
  have h22 := (witGoKS_sound _ _ _ _ witK3_23_22).2
  have h23 := (witGoKS_sound _ _ _ _ witK3_23_23).2
  simp only [cls3_23, List.length_append]
  omega

theorem slices3_len : ∀ l ∈ slices3, l.length = 331776 := by
  simp only [slices3, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  exact ⟨slen3_0, slen3_1, slen3_2, slen3_3, slen3_4, slen3_5, slen3_6, slen3_7, slen3_8, slen3_9, slen3_10, slen3_11, slen3_12, slen3_13, slen3_14, slen3_15, slen3_16, slen3_17, slen3_18, slen3_19, slen3_20, slen3_21, slen3_22, slen3_23⟩

end NPT.K4.D3T4979

#print axioms NPT.K4.D3T4979.slices3_len
