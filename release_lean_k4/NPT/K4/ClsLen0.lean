/- NPT.K4.ClsLen0 — every slice list of family 0 of K4@497 has `24^4 = 331776` entries: each of its 24 chunks has
13824 entries by the chunk witness checks (`witGoK5_sound`), so no list is walked again. -/
import NPT.K4.ClsSlices
import NPT.K4.Classes.WitK0

open NPT.K4.Classes

namespace NPT.K4.D3T497

theorem slen0_0 : cls0_0.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_0_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_0_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_0_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_0_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_0_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_0_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_0_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_0_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_0_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_0_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_0_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_0_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_0_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_0_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_0_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_0_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_0_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_0_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_0_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_0_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_0_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_0_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_0_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_0_23).2
  simp only [cls0_0, List.length_append]
  omega

theorem slen0_1 : cls0_1.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_1_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_1_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_1_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_1_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_1_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_1_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_1_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_1_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_1_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_1_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_1_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_1_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_1_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_1_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_1_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_1_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_1_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_1_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_1_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_1_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_1_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_1_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_1_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_1_23).2
  simp only [cls0_1, List.length_append]
  omega

theorem slen0_2 : cls0_2.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_2_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_2_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_2_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_2_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_2_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_2_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_2_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_2_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_2_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_2_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_2_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_2_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_2_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_2_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_2_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_2_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_2_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_2_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_2_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_2_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_2_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_2_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_2_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_2_23).2
  simp only [cls0_2, List.length_append]
  omega

theorem slen0_3 : cls0_3.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_3_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_3_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_3_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_3_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_3_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_3_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_3_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_3_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_3_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_3_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_3_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_3_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_3_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_3_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_3_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_3_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_3_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_3_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_3_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_3_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_3_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_3_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_3_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_3_23).2
  simp only [cls0_3, List.length_append]
  omega

theorem slen0_4 : cls0_4.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_4_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_4_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_4_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_4_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_4_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_4_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_4_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_4_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_4_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_4_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_4_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_4_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_4_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_4_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_4_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_4_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_4_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_4_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_4_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_4_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_4_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_4_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_4_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_4_23).2
  simp only [cls0_4, List.length_append]
  omega

theorem slen0_5 : cls0_5.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_5_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_5_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_5_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_5_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_5_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_5_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_5_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_5_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_5_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_5_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_5_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_5_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_5_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_5_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_5_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_5_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_5_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_5_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_5_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_5_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_5_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_5_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_5_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_5_23).2
  simp only [cls0_5, List.length_append]
  omega

theorem slen0_6 : cls0_6.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_6_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_6_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_6_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_6_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_6_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_6_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_6_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_6_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_6_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_6_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_6_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_6_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_6_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_6_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_6_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_6_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_6_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_6_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_6_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_6_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_6_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_6_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_6_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_6_23).2
  simp only [cls0_6, List.length_append]
  omega

theorem slen0_7 : cls0_7.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_7_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_7_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_7_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_7_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_7_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_7_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_7_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_7_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_7_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_7_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_7_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_7_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_7_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_7_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_7_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_7_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_7_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_7_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_7_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_7_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_7_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_7_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_7_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_7_23).2
  simp only [cls0_7, List.length_append]
  omega

theorem slen0_8 : cls0_8.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_8_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_8_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_8_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_8_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_8_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_8_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_8_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_8_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_8_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_8_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_8_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_8_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_8_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_8_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_8_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_8_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_8_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_8_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_8_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_8_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_8_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_8_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_8_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_8_23).2
  simp only [cls0_8, List.length_append]
  omega

theorem slen0_9 : cls0_9.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_9_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_9_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_9_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_9_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_9_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_9_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_9_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_9_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_9_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_9_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_9_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_9_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_9_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_9_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_9_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_9_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_9_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_9_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_9_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_9_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_9_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_9_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_9_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_9_23).2
  simp only [cls0_9, List.length_append]
  omega

theorem slen0_10 : cls0_10.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_10_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_10_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_10_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_10_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_10_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_10_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_10_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_10_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_10_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_10_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_10_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_10_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_10_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_10_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_10_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_10_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_10_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_10_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_10_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_10_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_10_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_10_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_10_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_10_23).2
  simp only [cls0_10, List.length_append]
  omega

theorem slen0_11 : cls0_11.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_11_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_11_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_11_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_11_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_11_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_11_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_11_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_11_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_11_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_11_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_11_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_11_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_11_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_11_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_11_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_11_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_11_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_11_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_11_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_11_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_11_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_11_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_11_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_11_23).2
  simp only [cls0_11, List.length_append]
  omega

theorem slen0_12 : cls0_12.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_12_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_12_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_12_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_12_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_12_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_12_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_12_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_12_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_12_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_12_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_12_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_12_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_12_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_12_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_12_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_12_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_12_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_12_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_12_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_12_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_12_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_12_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_12_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_12_23).2
  simp only [cls0_12, List.length_append]
  omega

theorem slen0_13 : cls0_13.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_13_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_13_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_13_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_13_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_13_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_13_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_13_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_13_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_13_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_13_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_13_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_13_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_13_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_13_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_13_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_13_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_13_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_13_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_13_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_13_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_13_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_13_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_13_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_13_23).2
  simp only [cls0_13, List.length_append]
  omega

theorem slen0_14 : cls0_14.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_14_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_14_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_14_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_14_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_14_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_14_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_14_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_14_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_14_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_14_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_14_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_14_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_14_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_14_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_14_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_14_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_14_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_14_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_14_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_14_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_14_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_14_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_14_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_14_23).2
  simp only [cls0_14, List.length_append]
  omega

theorem slen0_15 : cls0_15.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_15_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_15_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_15_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_15_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_15_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_15_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_15_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_15_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_15_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_15_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_15_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_15_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_15_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_15_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_15_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_15_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_15_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_15_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_15_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_15_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_15_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_15_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_15_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_15_23).2
  simp only [cls0_15, List.length_append]
  omega

theorem slen0_16 : cls0_16.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_16_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_16_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_16_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_16_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_16_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_16_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_16_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_16_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_16_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_16_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_16_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_16_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_16_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_16_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_16_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_16_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_16_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_16_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_16_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_16_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_16_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_16_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_16_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_16_23).2
  simp only [cls0_16, List.length_append]
  omega

theorem slen0_17 : cls0_17.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_17_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_17_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_17_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_17_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_17_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_17_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_17_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_17_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_17_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_17_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_17_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_17_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_17_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_17_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_17_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_17_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_17_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_17_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_17_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_17_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_17_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_17_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_17_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_17_23).2
  simp only [cls0_17, List.length_append]
  omega

theorem slen0_18 : cls0_18.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_18_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_18_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_18_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_18_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_18_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_18_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_18_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_18_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_18_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_18_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_18_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_18_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_18_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_18_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_18_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_18_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_18_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_18_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_18_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_18_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_18_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_18_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_18_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_18_23).2
  simp only [cls0_18, List.length_append]
  omega

theorem slen0_19 : cls0_19.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_19_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_19_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_19_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_19_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_19_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_19_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_19_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_19_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_19_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_19_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_19_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_19_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_19_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_19_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_19_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_19_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_19_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_19_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_19_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_19_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_19_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_19_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_19_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_19_23).2
  simp only [cls0_19, List.length_append]
  omega

theorem slen0_20 : cls0_20.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_20_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_20_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_20_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_20_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_20_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_20_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_20_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_20_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_20_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_20_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_20_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_20_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_20_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_20_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_20_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_20_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_20_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_20_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_20_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_20_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_20_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_20_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_20_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_20_23).2
  simp only [cls0_20, List.length_append]
  omega

theorem slen0_21 : cls0_21.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_21_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_21_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_21_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_21_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_21_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_21_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_21_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_21_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_21_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_21_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_21_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_21_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_21_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_21_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_21_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_21_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_21_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_21_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_21_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_21_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_21_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_21_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_21_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_21_23).2
  simp only [cls0_21, List.length_append]
  omega

theorem slen0_22 : cls0_22.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_22_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_22_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_22_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_22_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_22_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_22_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_22_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_22_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_22_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_22_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_22_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_22_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_22_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_22_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_22_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_22_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_22_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_22_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_22_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_22_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_22_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_22_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_22_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_22_23).2
  simp only [cls0_22, List.length_append]
  omega

theorem slen0_23 : cls0_23.length = 331776 := by
  have h0 := (witGoK5_sound 0 _ _ _ _ witK0_23_0).2
  have h1 := (witGoK5_sound 0 _ _ _ _ witK0_23_1).2
  have h2 := (witGoK5_sound 0 _ _ _ _ witK0_23_2).2
  have h3 := (witGoK5_sound 0 _ _ _ _ witK0_23_3).2
  have h4 := (witGoK5_sound 0 _ _ _ _ witK0_23_4).2
  have h5 := (witGoK5_sound 0 _ _ _ _ witK0_23_5).2
  have h6 := (witGoK5_sound 0 _ _ _ _ witK0_23_6).2
  have h7 := (witGoK5_sound 0 _ _ _ _ witK0_23_7).2
  have h8 := (witGoK5_sound 0 _ _ _ _ witK0_23_8).2
  have h9 := (witGoK5_sound 0 _ _ _ _ witK0_23_9).2
  have h10 := (witGoK5_sound 0 _ _ _ _ witK0_23_10).2
  have h11 := (witGoK5_sound 0 _ _ _ _ witK0_23_11).2
  have h12 := (witGoK5_sound 0 _ _ _ _ witK0_23_12).2
  have h13 := (witGoK5_sound 0 _ _ _ _ witK0_23_13).2
  have h14 := (witGoK5_sound 0 _ _ _ _ witK0_23_14).2
  have h15 := (witGoK5_sound 0 _ _ _ _ witK0_23_15).2
  have h16 := (witGoK5_sound 0 _ _ _ _ witK0_23_16).2
  have h17 := (witGoK5_sound 0 _ _ _ _ witK0_23_17).2
  have h18 := (witGoK5_sound 0 _ _ _ _ witK0_23_18).2
  have h19 := (witGoK5_sound 0 _ _ _ _ witK0_23_19).2
  have h20 := (witGoK5_sound 0 _ _ _ _ witK0_23_20).2
  have h21 := (witGoK5_sound 0 _ _ _ _ witK0_23_21).2
  have h22 := (witGoK5_sound 0 _ _ _ _ witK0_23_22).2
  have h23 := (witGoK5_sound 0 _ _ _ _ witK0_23_23).2
  simp only [cls0_23, List.length_append]
  omega

theorem slices0_len : ∀ l ∈ slices0, l.length = 331776 := by
  simp only [slices0, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  exact ⟨slen0_0, slen0_1, slen0_2, slen0_3, slen0_4, slen0_5, slen0_6, slen0_7, slen0_8, slen0_9, slen0_10, slen0_11, slen0_12, slen0_13, slen0_14, slen0_15, slen0_16, slen0_17, slen0_18, slen0_19, slen0_20, slen0_21, slen0_22, slen0_23⟩

end NPT.K4.D3T497

#print axioms NPT.K4.D3T497.slices0_len
