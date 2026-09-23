theory Inverse_Schrodinger_Lp_Qstar_Centered_Three_Term_Source_Input_Lp
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Complex_Lp_Coarse_Triangle"
begin

section \<open>The centered three-term derivative source in the HLS input space\<close>

context aim_planar_riesz_hls
begin

theorem slp_qstar_centered_three_term_source_input_complex_Lp:
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
    and delta_positive: "0 < delta"
    and radius_lower: "delta \<le> R"
    and amplitude_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
    and amplitude_derivative_lp:
      "aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f)"
    and amplitude_radius: "\<And>y. f y \<noteq> 0 \<Longrightarrow> norm y \<le> R"
  shows source_lp:
      "aim_complex_lp_on_plane a
        (\<lambda>y.
          slp_qstar_far_amplitude_derivative_source delta 0 f y -
          slp_qstar_centered_cutoff_partial_source delta f y -
          slp_qstar_centered_square_denominator_source delta f y)"
    and source_norm_bound:
      "aim_complex_lp_norm a
          (\<lambda>y.
            slp_qstar_far_amplitude_derivative_source delta 0 f y -
            slp_qstar_centered_cutoff_partial_source delta f y -
            slp_qstar_centered_square_denominator_source delta f y)
        \<le> 4 *
          (4 *
            ((2 / delta) *
                aim_complex_lp_norm a
                  (slp_classical_wirtinger_partial f) +
              (slp_global_cutoff_L / delta) *
                ((integral\<^sup>L lborel
                    (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
                  aim_complex_lp_norm (aim_hls_target_exponent a) f)) +
            (1 / delta) *
              slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f)"
proof -
  let ?A = "slp_qstar_far_amplitude_derivative_source delta 0 f"
  let ?C = "slp_qstar_centered_cutoff_partial_source delta f"
  let ?S = "slp_qstar_centered_square_denominator_source delta f"
  have exponent_one_le: "1 \<le> a"
    using exponent_lower by linarith
  have exponent_positive: "0 < a"
    using exponent_lower by linarith
  note amplitude_data =
    slp_qstar_far_amplitude_derivative_source_complex_Lp[
      OF exponent_positive delta_positive amplitude_derivative_lp,
      where c=0]
  note cutoff_data =
    slp_qstar_centered_cutoff_partial_source_input_complex_Lp[
      OF exponent_lower exponent_upper delta_positive amplitude_lp]
  note square_data =
    slp_qstar_centered_square_denominator_source_input_complex_Lp[
      OF exponent_lower exponent_upper delta_positive radius_lower
        amplitude_lp amplitude_radius]
  note first_difference = slp_complex_lp_diff_norm_coarse_triangle[
      OF exponent_one_le amplitude_data(1) cutoff_data(1)]
  note full_difference = slp_complex_lp_diff_norm_coarse_triangle[
      OF exponent_one_le first_difference(1) square_data(1)]
  show "aim_complex_lp_on_plane a
      (\<lambda>y. ?A y - ?C y - ?S y)"
    by (rule full_difference(1))
  have first_component_sum_bound:
      "aim_complex_lp_norm a ?A + aim_complex_lp_norm a ?C
        \<le> (2 / delta) *
              aim_complex_lp_norm a
                (slp_classical_wirtinger_partial f) +
            (slp_global_cutoff_L / delta) *
              ((integral\<^sup>L lborel
                  (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
                aim_complex_lp_norm (aim_hls_target_exponent a) f)"
    by (rule add_mono[OF amplitude_data(2) cutoff_data(2)])
  have first_norm_bound:
      "aim_complex_lp_norm a (\<lambda>y. ?A y - ?C y)
        \<le> 4 *
          ((2 / delta) *
              aim_complex_lp_norm a
                (slp_classical_wirtinger_partial f) +
            (slp_global_cutoff_L / delta) *
              ((integral\<^sup>L lborel
                  (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
                aim_complex_lp_norm (aim_hls_target_exponent a) f))"
  proof (rule order_trans[OF first_difference(2)])
    show "4 * (aim_complex_lp_norm a ?A + aim_complex_lp_norm a ?C)
        \<le> 4 *
          ((2 / delta) *
              aim_complex_lp_norm a
                (slp_classical_wirtinger_partial f) +
            (slp_global_cutoff_L / delta) *
              ((integral\<^sup>L lborel
                  (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
                aim_complex_lp_norm (aim_hls_target_exponent a) f))"
      by (rule mult_left_mono[OF first_component_sum_bound]) simp
  qed
  have full_component_sum_bound:
      "aim_complex_lp_norm a (\<lambda>y. ?A y - ?C y) +
          aim_complex_lp_norm a ?S
        \<le> 4 *
            ((2 / delta) *
                aim_complex_lp_norm a
                  (slp_classical_wirtinger_partial f) +
              (slp_global_cutoff_L / delta) *
                ((integral\<^sup>L lborel
                    (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
                  aim_complex_lp_norm (aim_hls_target_exponent a) f)) +
          (1 / delta) *
            slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
            aim_complex_lp_norm (aim_hls_target_exponent a) f"
    by (rule add_mono[OF first_norm_bound square_data(2)])
  show "aim_complex_lp_norm a (\<lambda>y. ?A y - ?C y - ?S y)
      \<le> 4 *
        (4 *
          ((2 / delta) *
              aim_complex_lp_norm a
                (slp_classical_wirtinger_partial f) +
            (slp_global_cutoff_L / delta) *
              ((integral\<^sup>L lborel
                  (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
                aim_complex_lp_norm (aim_hls_target_exponent a) f)) +
          (1 / delta) *
            slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
            aim_complex_lp_norm (aim_hls_target_exponent a) f)"
  proof (rule order_trans[OF full_difference(2)])
    show "4 *
        (aim_complex_lp_norm a (\<lambda>y. ?A y - ?C y) +
          aim_complex_lp_norm a ?S)
        \<le> 4 *
          (4 *
            ((2 / delta) *
                aim_complex_lp_norm a
                  (slp_classical_wirtinger_partial f) +
              (slp_global_cutoff_L / delta) *
                ((integral\<^sup>L lborel
                    (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
                  aim_complex_lp_norm (aim_hls_target_exponent a) f)) +
            (1 / delta) *
              slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f)"
      by (rule mult_left_mono[OF full_component_sum_bound]) simp
  qed
qed

end

end
