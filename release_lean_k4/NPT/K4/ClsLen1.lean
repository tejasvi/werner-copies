/- NPT.K4.ClsLen1 — every slice list of family 1 of K4@497 has `24^4 = 331776` entries: each of its 24 chunks has
13824 entries by the chunk witness checks (`witGoK5_sound`), so no list is walked again. -/
import NPT.K4.ClsSlices
import NPT.K4.Classes.WitK1

open NPT.K4.Classes

namespace NPT.K4.D3T497

theorem slen1_0 : cls1_0.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_0_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_0_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_0_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_0_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_0_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_0_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_0_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_0_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_0_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_0_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_0_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_0_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_0_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_0_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_0_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_0_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_0_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_0_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_0_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_0_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_0_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_0_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_0_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_0_23).2
  simp only [cls1_0, List.length_append]
  omega

theorem slen1_1 : cls1_1.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_1_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_1_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_1_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_1_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_1_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_1_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_1_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_1_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_1_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_1_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_1_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_1_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_1_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_1_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_1_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_1_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_1_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_1_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_1_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_1_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_1_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_1_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_1_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_1_23).2
  simp only [cls1_1, List.length_append]
  omega

theorem slen1_2 : cls1_2.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_2_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_2_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_2_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_2_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_2_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_2_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_2_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_2_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_2_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_2_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_2_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_2_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_2_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_2_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_2_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_2_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_2_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_2_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_2_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_2_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_2_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_2_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_2_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_2_23).2
  simp only [cls1_2, List.length_append]
  omega

theorem slen1_3 : cls1_3.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_3_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_3_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_3_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_3_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_3_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_3_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_3_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_3_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_3_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_3_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_3_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_3_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_3_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_3_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_3_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_3_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_3_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_3_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_3_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_3_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_3_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_3_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_3_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_3_23).2
  simp only [cls1_3, List.length_append]
  omega

theorem slen1_4 : cls1_4.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_4_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_4_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_4_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_4_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_4_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_4_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_4_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_4_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_4_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_4_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_4_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_4_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_4_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_4_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_4_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_4_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_4_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_4_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_4_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_4_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_4_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_4_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_4_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_4_23).2
  simp only [cls1_4, List.length_append]
  omega

theorem slen1_5 : cls1_5.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_5_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_5_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_5_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_5_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_5_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_5_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_5_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_5_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_5_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_5_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_5_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_5_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_5_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_5_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_5_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_5_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_5_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_5_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_5_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_5_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_5_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_5_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_5_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_5_23).2
  simp only [cls1_5, List.length_append]
  omega

theorem slen1_6 : cls1_6.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_6_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_6_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_6_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_6_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_6_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_6_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_6_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_6_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_6_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_6_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_6_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_6_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_6_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_6_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_6_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_6_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_6_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_6_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_6_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_6_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_6_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_6_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_6_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_6_23).2
  simp only [cls1_6, List.length_append]
  omega

theorem slen1_7 : cls1_7.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_7_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_7_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_7_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_7_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_7_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_7_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_7_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_7_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_7_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_7_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_7_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_7_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_7_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_7_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_7_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_7_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_7_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_7_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_7_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_7_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_7_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_7_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_7_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_7_23).2
  simp only [cls1_7, List.length_append]
  omega

theorem slen1_8 : cls1_8.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_8_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_8_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_8_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_8_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_8_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_8_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_8_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_8_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_8_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_8_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_8_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_8_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_8_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_8_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_8_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_8_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_8_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_8_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_8_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_8_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_8_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_8_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_8_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_8_23).2
  simp only [cls1_8, List.length_append]
  omega

theorem slen1_9 : cls1_9.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_9_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_9_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_9_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_9_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_9_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_9_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_9_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_9_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_9_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_9_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_9_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_9_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_9_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_9_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_9_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_9_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_9_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_9_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_9_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_9_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_9_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_9_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_9_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_9_23).2
  simp only [cls1_9, List.length_append]
  omega

theorem slen1_10 : cls1_10.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_10_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_10_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_10_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_10_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_10_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_10_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_10_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_10_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_10_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_10_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_10_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_10_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_10_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_10_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_10_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_10_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_10_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_10_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_10_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_10_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_10_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_10_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_10_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_10_23).2
  simp only [cls1_10, List.length_append]
  omega

theorem slen1_11 : cls1_11.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_11_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_11_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_11_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_11_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_11_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_11_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_11_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_11_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_11_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_11_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_11_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_11_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_11_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_11_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_11_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_11_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_11_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_11_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_11_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_11_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_11_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_11_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_11_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_11_23).2
  simp only [cls1_11, List.length_append]
  omega

theorem slen1_12 : cls1_12.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_12_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_12_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_12_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_12_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_12_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_12_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_12_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_12_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_12_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_12_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_12_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_12_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_12_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_12_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_12_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_12_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_12_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_12_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_12_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_12_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_12_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_12_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_12_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_12_23).2
  simp only [cls1_12, List.length_append]
  omega

theorem slen1_13 : cls1_13.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_13_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_13_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_13_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_13_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_13_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_13_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_13_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_13_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_13_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_13_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_13_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_13_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_13_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_13_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_13_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_13_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_13_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_13_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_13_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_13_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_13_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_13_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_13_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_13_23).2
  simp only [cls1_13, List.length_append]
  omega

theorem slen1_14 : cls1_14.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_14_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_14_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_14_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_14_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_14_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_14_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_14_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_14_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_14_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_14_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_14_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_14_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_14_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_14_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_14_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_14_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_14_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_14_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_14_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_14_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_14_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_14_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_14_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_14_23).2
  simp only [cls1_14, List.length_append]
  omega

theorem slen1_15 : cls1_15.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_15_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_15_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_15_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_15_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_15_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_15_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_15_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_15_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_15_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_15_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_15_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_15_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_15_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_15_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_15_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_15_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_15_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_15_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_15_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_15_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_15_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_15_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_15_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_15_23).2
  simp only [cls1_15, List.length_append]
  omega

theorem slen1_16 : cls1_16.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_16_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_16_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_16_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_16_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_16_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_16_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_16_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_16_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_16_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_16_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_16_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_16_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_16_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_16_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_16_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_16_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_16_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_16_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_16_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_16_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_16_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_16_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_16_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_16_23).2
  simp only [cls1_16, List.length_append]
  omega

theorem slen1_17 : cls1_17.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_17_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_17_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_17_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_17_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_17_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_17_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_17_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_17_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_17_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_17_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_17_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_17_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_17_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_17_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_17_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_17_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_17_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_17_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_17_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_17_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_17_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_17_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_17_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_17_23).2
  simp only [cls1_17, List.length_append]
  omega

theorem slen1_18 : cls1_18.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_18_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_18_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_18_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_18_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_18_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_18_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_18_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_18_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_18_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_18_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_18_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_18_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_18_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_18_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_18_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_18_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_18_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_18_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_18_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_18_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_18_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_18_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_18_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_18_23).2
  simp only [cls1_18, List.length_append]
  omega

theorem slen1_19 : cls1_19.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_19_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_19_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_19_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_19_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_19_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_19_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_19_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_19_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_19_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_19_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_19_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_19_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_19_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_19_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_19_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_19_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_19_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_19_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_19_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_19_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_19_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_19_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_19_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_19_23).2
  simp only [cls1_19, List.length_append]
  omega

theorem slen1_20 : cls1_20.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_20_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_20_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_20_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_20_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_20_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_20_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_20_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_20_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_20_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_20_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_20_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_20_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_20_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_20_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_20_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_20_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_20_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_20_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_20_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_20_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_20_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_20_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_20_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_20_23).2
  simp only [cls1_20, List.length_append]
  omega

theorem slen1_21 : cls1_21.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_21_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_21_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_21_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_21_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_21_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_21_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_21_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_21_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_21_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_21_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_21_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_21_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_21_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_21_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_21_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_21_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_21_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_21_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_21_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_21_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_21_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_21_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_21_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_21_23).2
  simp only [cls1_21, List.length_append]
  omega

theorem slen1_22 : cls1_22.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_22_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_22_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_22_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_22_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_22_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_22_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_22_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_22_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_22_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_22_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_22_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_22_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_22_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_22_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_22_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_22_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_22_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_22_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_22_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_22_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_22_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_22_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_22_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_22_23).2
  simp only [cls1_22, List.length_append]
  omega

theorem slen1_23 : cls1_23.length = 331776 := by
  have h0 := (witGoK5_sound 1 _ _ _ _ witK1_23_0).2
  have h1 := (witGoK5_sound 1 _ _ _ _ witK1_23_1).2
  have h2 := (witGoK5_sound 1 _ _ _ _ witK1_23_2).2
  have h3 := (witGoK5_sound 1 _ _ _ _ witK1_23_3).2
  have h4 := (witGoK5_sound 1 _ _ _ _ witK1_23_4).2
  have h5 := (witGoK5_sound 1 _ _ _ _ witK1_23_5).2
  have h6 := (witGoK5_sound 1 _ _ _ _ witK1_23_6).2
  have h7 := (witGoK5_sound 1 _ _ _ _ witK1_23_7).2
  have h8 := (witGoK5_sound 1 _ _ _ _ witK1_23_8).2
  have h9 := (witGoK5_sound 1 _ _ _ _ witK1_23_9).2
  have h10 := (witGoK5_sound 1 _ _ _ _ witK1_23_10).2
  have h11 := (witGoK5_sound 1 _ _ _ _ witK1_23_11).2
  have h12 := (witGoK5_sound 1 _ _ _ _ witK1_23_12).2
  have h13 := (witGoK5_sound 1 _ _ _ _ witK1_23_13).2
  have h14 := (witGoK5_sound 1 _ _ _ _ witK1_23_14).2
  have h15 := (witGoK5_sound 1 _ _ _ _ witK1_23_15).2
  have h16 := (witGoK5_sound 1 _ _ _ _ witK1_23_16).2
  have h17 := (witGoK5_sound 1 _ _ _ _ witK1_23_17).2
  have h18 := (witGoK5_sound 1 _ _ _ _ witK1_23_18).2
  have h19 := (witGoK5_sound 1 _ _ _ _ witK1_23_19).2
  have h20 := (witGoK5_sound 1 _ _ _ _ witK1_23_20).2
  have h21 := (witGoK5_sound 1 _ _ _ _ witK1_23_21).2
  have h22 := (witGoK5_sound 1 _ _ _ _ witK1_23_22).2
  have h23 := (witGoK5_sound 1 _ _ _ _ witK1_23_23).2
  simp only [cls1_23, List.length_append]
  omega

theorem slices1_len : ∀ l ∈ slices1, l.length = 331776 := by
  simp only [slices1, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  exact ⟨slen1_0, slen1_1, slen1_2, slen1_3, slen1_4, slen1_5, slen1_6, slen1_7, slen1_8, slen1_9, slen1_10, slen1_11, slen1_12, slen1_13, slen1_14, slen1_15, slen1_16, slen1_17, slen1_18, slen1_19, slen1_20, slen1_21, slen1_22, slen1_23⟩

end NPT.K4.D3T497

#print axioms NPT.K4.D3T497.slices1_len
