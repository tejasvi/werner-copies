/- NPT.K4.ClsLen2 — every slice list of family 2 of K4@497 has `24^4 = 331776` entries: each of its 24 chunks has
13824 entries by the chunk witness checks (`witGoK5_sound`), so no list is walked again. -/
import NPT.K4.ClsSlices
import NPT.K4.Classes.WitK2

open NPT.K4.Classes

namespace NPT.K4.D3T497

theorem slen2_0 : cls2_0.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_0_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_0_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_0_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_0_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_0_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_0_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_0_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_0_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_0_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_0_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_0_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_0_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_0_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_0_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_0_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_0_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_0_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_0_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_0_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_0_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_0_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_0_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_0_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_0_23).2
  simp only [cls2_0, List.length_append]
  omega

theorem slen2_1 : cls2_1.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_1_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_1_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_1_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_1_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_1_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_1_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_1_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_1_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_1_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_1_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_1_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_1_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_1_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_1_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_1_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_1_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_1_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_1_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_1_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_1_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_1_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_1_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_1_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_1_23).2
  simp only [cls2_1, List.length_append]
  omega

theorem slen2_2 : cls2_2.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_2_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_2_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_2_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_2_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_2_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_2_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_2_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_2_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_2_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_2_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_2_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_2_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_2_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_2_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_2_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_2_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_2_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_2_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_2_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_2_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_2_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_2_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_2_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_2_23).2
  simp only [cls2_2, List.length_append]
  omega

theorem slen2_3 : cls2_3.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_3_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_3_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_3_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_3_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_3_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_3_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_3_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_3_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_3_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_3_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_3_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_3_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_3_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_3_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_3_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_3_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_3_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_3_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_3_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_3_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_3_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_3_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_3_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_3_23).2
  simp only [cls2_3, List.length_append]
  omega

theorem slen2_4 : cls2_4.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_4_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_4_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_4_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_4_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_4_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_4_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_4_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_4_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_4_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_4_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_4_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_4_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_4_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_4_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_4_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_4_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_4_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_4_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_4_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_4_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_4_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_4_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_4_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_4_23).2
  simp only [cls2_4, List.length_append]
  omega

theorem slen2_5 : cls2_5.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_5_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_5_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_5_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_5_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_5_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_5_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_5_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_5_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_5_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_5_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_5_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_5_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_5_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_5_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_5_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_5_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_5_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_5_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_5_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_5_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_5_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_5_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_5_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_5_23).2
  simp only [cls2_5, List.length_append]
  omega

theorem slen2_6 : cls2_6.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_6_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_6_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_6_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_6_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_6_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_6_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_6_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_6_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_6_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_6_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_6_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_6_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_6_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_6_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_6_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_6_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_6_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_6_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_6_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_6_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_6_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_6_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_6_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_6_23).2
  simp only [cls2_6, List.length_append]
  omega

theorem slen2_7 : cls2_7.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_7_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_7_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_7_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_7_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_7_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_7_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_7_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_7_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_7_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_7_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_7_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_7_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_7_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_7_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_7_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_7_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_7_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_7_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_7_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_7_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_7_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_7_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_7_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_7_23).2
  simp only [cls2_7, List.length_append]
  omega

theorem slen2_8 : cls2_8.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_8_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_8_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_8_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_8_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_8_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_8_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_8_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_8_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_8_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_8_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_8_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_8_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_8_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_8_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_8_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_8_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_8_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_8_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_8_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_8_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_8_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_8_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_8_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_8_23).2
  simp only [cls2_8, List.length_append]
  omega

theorem slen2_9 : cls2_9.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_9_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_9_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_9_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_9_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_9_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_9_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_9_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_9_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_9_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_9_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_9_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_9_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_9_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_9_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_9_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_9_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_9_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_9_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_9_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_9_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_9_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_9_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_9_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_9_23).2
  simp only [cls2_9, List.length_append]
  omega

theorem slen2_10 : cls2_10.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_10_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_10_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_10_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_10_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_10_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_10_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_10_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_10_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_10_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_10_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_10_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_10_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_10_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_10_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_10_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_10_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_10_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_10_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_10_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_10_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_10_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_10_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_10_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_10_23).2
  simp only [cls2_10, List.length_append]
  omega

theorem slen2_11 : cls2_11.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_11_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_11_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_11_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_11_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_11_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_11_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_11_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_11_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_11_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_11_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_11_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_11_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_11_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_11_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_11_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_11_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_11_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_11_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_11_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_11_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_11_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_11_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_11_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_11_23).2
  simp only [cls2_11, List.length_append]
  omega

theorem slen2_12 : cls2_12.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_12_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_12_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_12_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_12_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_12_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_12_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_12_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_12_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_12_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_12_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_12_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_12_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_12_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_12_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_12_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_12_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_12_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_12_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_12_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_12_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_12_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_12_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_12_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_12_23).2
  simp only [cls2_12, List.length_append]
  omega

theorem slen2_13 : cls2_13.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_13_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_13_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_13_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_13_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_13_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_13_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_13_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_13_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_13_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_13_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_13_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_13_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_13_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_13_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_13_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_13_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_13_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_13_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_13_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_13_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_13_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_13_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_13_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_13_23).2
  simp only [cls2_13, List.length_append]
  omega

theorem slen2_14 : cls2_14.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_14_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_14_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_14_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_14_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_14_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_14_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_14_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_14_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_14_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_14_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_14_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_14_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_14_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_14_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_14_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_14_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_14_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_14_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_14_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_14_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_14_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_14_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_14_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_14_23).2
  simp only [cls2_14, List.length_append]
  omega

theorem slen2_15 : cls2_15.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_15_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_15_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_15_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_15_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_15_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_15_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_15_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_15_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_15_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_15_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_15_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_15_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_15_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_15_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_15_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_15_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_15_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_15_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_15_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_15_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_15_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_15_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_15_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_15_23).2
  simp only [cls2_15, List.length_append]
  omega

theorem slen2_16 : cls2_16.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_16_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_16_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_16_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_16_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_16_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_16_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_16_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_16_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_16_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_16_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_16_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_16_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_16_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_16_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_16_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_16_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_16_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_16_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_16_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_16_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_16_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_16_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_16_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_16_23).2
  simp only [cls2_16, List.length_append]
  omega

theorem slen2_17 : cls2_17.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_17_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_17_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_17_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_17_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_17_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_17_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_17_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_17_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_17_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_17_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_17_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_17_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_17_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_17_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_17_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_17_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_17_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_17_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_17_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_17_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_17_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_17_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_17_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_17_23).2
  simp only [cls2_17, List.length_append]
  omega

theorem slen2_18 : cls2_18.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_18_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_18_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_18_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_18_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_18_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_18_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_18_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_18_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_18_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_18_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_18_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_18_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_18_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_18_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_18_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_18_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_18_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_18_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_18_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_18_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_18_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_18_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_18_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_18_23).2
  simp only [cls2_18, List.length_append]
  omega

theorem slen2_19 : cls2_19.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_19_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_19_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_19_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_19_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_19_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_19_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_19_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_19_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_19_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_19_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_19_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_19_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_19_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_19_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_19_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_19_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_19_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_19_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_19_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_19_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_19_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_19_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_19_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_19_23).2
  simp only [cls2_19, List.length_append]
  omega

theorem slen2_20 : cls2_20.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_20_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_20_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_20_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_20_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_20_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_20_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_20_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_20_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_20_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_20_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_20_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_20_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_20_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_20_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_20_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_20_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_20_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_20_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_20_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_20_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_20_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_20_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_20_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_20_23).2
  simp only [cls2_20, List.length_append]
  omega

theorem slen2_21 : cls2_21.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_21_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_21_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_21_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_21_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_21_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_21_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_21_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_21_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_21_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_21_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_21_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_21_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_21_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_21_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_21_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_21_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_21_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_21_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_21_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_21_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_21_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_21_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_21_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_21_23).2
  simp only [cls2_21, List.length_append]
  omega

theorem slen2_22 : cls2_22.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_22_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_22_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_22_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_22_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_22_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_22_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_22_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_22_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_22_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_22_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_22_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_22_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_22_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_22_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_22_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_22_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_22_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_22_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_22_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_22_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_22_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_22_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_22_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_22_23).2
  simp only [cls2_22, List.length_append]
  omega

theorem slen2_23 : cls2_23.length = 331776 := by
  have h0 := (witGoK5_sound 2 _ _ _ _ witK2_23_0).2
  have h1 := (witGoK5_sound 2 _ _ _ _ witK2_23_1).2
  have h2 := (witGoK5_sound 2 _ _ _ _ witK2_23_2).2
  have h3 := (witGoK5_sound 2 _ _ _ _ witK2_23_3).2
  have h4 := (witGoK5_sound 2 _ _ _ _ witK2_23_4).2
  have h5 := (witGoK5_sound 2 _ _ _ _ witK2_23_5).2
  have h6 := (witGoK5_sound 2 _ _ _ _ witK2_23_6).2
  have h7 := (witGoK5_sound 2 _ _ _ _ witK2_23_7).2
  have h8 := (witGoK5_sound 2 _ _ _ _ witK2_23_8).2
  have h9 := (witGoK5_sound 2 _ _ _ _ witK2_23_9).2
  have h10 := (witGoK5_sound 2 _ _ _ _ witK2_23_10).2
  have h11 := (witGoK5_sound 2 _ _ _ _ witK2_23_11).2
  have h12 := (witGoK5_sound 2 _ _ _ _ witK2_23_12).2
  have h13 := (witGoK5_sound 2 _ _ _ _ witK2_23_13).2
  have h14 := (witGoK5_sound 2 _ _ _ _ witK2_23_14).2
  have h15 := (witGoK5_sound 2 _ _ _ _ witK2_23_15).2
  have h16 := (witGoK5_sound 2 _ _ _ _ witK2_23_16).2
  have h17 := (witGoK5_sound 2 _ _ _ _ witK2_23_17).2
  have h18 := (witGoK5_sound 2 _ _ _ _ witK2_23_18).2
  have h19 := (witGoK5_sound 2 _ _ _ _ witK2_23_19).2
  have h20 := (witGoK5_sound 2 _ _ _ _ witK2_23_20).2
  have h21 := (witGoK5_sound 2 _ _ _ _ witK2_23_21).2
  have h22 := (witGoK5_sound 2 _ _ _ _ witK2_23_22).2
  have h23 := (witGoK5_sound 2 _ _ _ _ witK2_23_23).2
  simp only [cls2_23, List.length_append]
  omega

theorem slices2_len : ∀ l ∈ slices2, l.length = 331776 := by
  simp only [slices2, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  exact ⟨slen2_0, slen2_1, slen2_2, slen2_3, slen2_4, slen2_5, slen2_6, slen2_7, slen2_8, slen2_9, slen2_10, slen2_11, slen2_12, slen2_13, slen2_14, slen2_15, slen2_16, slen2_17, slen2_18, slen2_19, slen2_20, slen2_21, slen2_22, slen2_23⟩

end NPT.K4.D3T497

#print axioms NPT.K4.D3T497.slices2_len
