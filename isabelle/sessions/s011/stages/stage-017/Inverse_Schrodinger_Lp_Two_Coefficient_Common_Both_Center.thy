theory Inverse_Schrodinger_Lp_Two_Coefficient_Common_Both_Center
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Alessandrini_Born"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Two_Coefficient_Common_Left_Center"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Two_Coefficient_Common_Right_Center"
begin

hide_const (open) Commutative_Ring.norm

section \<open>One center carrier for both CGO orientations\<close>

context slp_cgo_full_weak_solution_context
begin

theorem slp_two_coefficient_common_both_center_fixed_point:
  fixes p epsilon A R A0 B0 B1 :: real
    and Omega X :: "slp_point set"
    and cutoff coefficient coefficient_tilde :: slp_scalar_field
  assumes riesz_hls: "aim_planar_riesz_hls_claim"
    and cauchy_test_left_inverse:
      "aim_planar_cauchy_test_left_inverse_claim"
    and evans_density: "evans_compact_support_w1p_zero_density_claim"
    and exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and loss_positive: "0 < epsilon"
    and loss_upper: "epsilon < 1 - 1 / p"
    and radius_nonnegative: "0 \<le> A"
    and radius_lower: "1 \<le> R"
    and set_radius:
      "\<And>y :: slp_point. y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm y \<le> A"
    and center_geometry:
      "\<And>c y :: slp_point. c \<in> Omega \<Longrightarrow> y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (y - c) \<le> R"
    and X_open: "open X"
    and X_bounded: "bounded X"
    and cutoff_test: "slp_test_function_on X cutoff"
    and cutoff_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (cutoff x) \<le> A0"
    and cutoff_derivative_zero_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative cutoff 0 x) \<le> B0"
    and cutoff_derivative_one_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative cutoff 1 x) \<le> B1"
    and A0_nonnegative: "0 \<le> A0"
    and B0_nonnegative: "0 \<le> B0"
    and B1_nonnegative: "0 \<le> B1"
    and coefficient_lp: "aim_complex_lp_on_plane p coefficient"
    and coefficient_support: "{x. coefficient x \<noteq> 0} \<subseteq> X"
    and coefficient_tilde_lp:
      "aim_complex_lp_on_plane p coefficient_tilde"
    and coefficient_tilde_support:
      "{x. coefficient_tilde x \<noteq> 0} \<subseteq> X"
    and domain: "slp_bounded_smooth_domain Omega"
  shows
    "\<exists>T Z. 2 \<le> T
      \<and> Z \<in> sets (lborel :: slp_point measure)
      \<and> Z \<noteq> {}
      \<and> Z \<subseteq> Omega
      \<and> (AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longleftrightarrow> c \<in> Z)
      \<and> (\<forall>c \<in> Z.
        slp_left_neumann_center_fixed_point_data
          X T c cutoff coefficient
        \<and> slp_left_neumann_center_fixed_point_data
          X T c cutoff coefficient_tilde
        \<and> slp_right_neumann_center_fixed_point_data
          X T c cutoff coefficient
        \<and> slp_right_neumann_center_fixed_point_data
          X T c cutoff coefficient_tilde)"
proof -
  obtain T_left Z_left where T_left_lower: "2 \<le> T_left"
    and Z_left_measurable:
      "Z_left \<in> sets (lborel :: slp_point measure)"
    and Z_left_nonempty: "Z_left \<noteq> {}"
    and Z_left_subset: "Z_left \<subseteq> Omega"
    and Z_left_AE:
      "AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longleftrightarrow> c \<in> Z_left"
    and left_data:
      "\<forall>c \<in> Z_left.
        slp_left_neumann_center_fixed_point_data
          X T_left c cutoff coefficient
        \<and> slp_left_neumann_center_fixed_point_data
          X T_left c cutoff coefficient_tilde"
    using slp_two_coefficient_common_left_center_fixed_point[
      OF riesz_hls cauchy_test_left_inverse evans_density
        exponent_lower exponent_upper loss_positive loss_upper
        radius_nonnegative radius_lower set_radius center_geometry
        X_open X_bounded cutoff_test cutoff_bound
        cutoff_derivative_zero_bound cutoff_derivative_one_bound
        A0_nonnegative B0_nonnegative B1_nonnegative
        coefficient_lp coefficient_support coefficient_tilde_lp
        coefficient_tilde_support domain]
    by blast
  obtain T_right Z_right where T_right_lower: "2 \<le> T_right"
    and Z_right_measurable:
      "Z_right \<in> sets (lborel :: slp_point measure)"
    and Z_right_nonempty: "Z_right \<noteq> {}"
    and Z_right_subset: "Z_right \<subseteq> Omega"
    and Z_right_AE:
      "AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longleftrightarrow> c \<in> Z_right"
    and right_data:
      "\<forall>c \<in> Z_right.
        slp_right_neumann_center_fixed_point_data
          X T_right c cutoff coefficient
        \<and> slp_right_neumann_center_fixed_point_data
          X T_right c cutoff coefficient_tilde"
    using slp_two_coefficient_common_right_center_fixed_point[
      OF riesz_hls cauchy_test_left_inverse evans_density
        exponent_lower exponent_upper loss_positive loss_upper
        radius_nonnegative radius_lower set_radius center_geometry
        X_open X_bounded cutoff_test cutoff_bound
        cutoff_derivative_zero_bound cutoff_derivative_one_bound
        A0_nonnegative B0_nonnegative B1_nonnegative
        coefficient_lp coefficient_support coefficient_tilde_lp
        coefficient_tilde_support domain]
    by blast

  let ?T = "max T_left T_right"
  have T_lower: "2 \<le> ?T"
    using T_left_lower by simp
  have left_data_max:
      "\<forall>c \<in> Z_left.
        slp_left_neumann_center_fixed_point_data
          X ?T c cutoff coefficient
        \<and> slp_left_neumann_center_fixed_point_data
          X ?T c cutoff coefficient_tilde"
  proof (intro ballI conjI)
    fix c
    assume c_in: "c \<in> Z_left"
    note old = left_data[rule_format, OF c_in]
    show "slp_left_neumann_center_fixed_point_data
        X ?T c cutoff coefficient"
      by (rule slp_left_neumann_center_fixed_point_data_mono[
            OF conjunct1[OF old]]) simp
    show "slp_left_neumann_center_fixed_point_data
        X ?T c cutoff coefficient_tilde"
      by (rule slp_left_neumann_center_fixed_point_data_mono[
            OF conjunct2[OF old]]) simp
  qed
  have right_data_max:
      "\<forall>c \<in> Z_right.
        slp_right_neumann_center_fixed_point_data
          X ?T c cutoff coefficient
        \<and> slp_right_neumann_center_fixed_point_data
          X ?T c cutoff coefficient_tilde"
  proof (intro ballI conjI)
    fix c
    assume c_in: "c \<in> Z_right"
    note old = right_data[rule_format, OF c_in]
    show "slp_right_neumann_center_fixed_point_data
        X ?T c cutoff coefficient"
      by (rule slp_right_neumann_center_fixed_point_data_mono[
            OF conjunct1[OF old]]) simp
    show "slp_right_neumann_center_fixed_point_data
        X ?T c cutoff coefficient_tilde"
      by (rule slp_right_neumann_center_fixed_point_data_mono[
            OF conjunct2[OF old]]) simp
  qed

  have left_AE:
      "AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longrightarrow>
          (slp_left_neumann_center_fixed_point_data
            X ?T c cutoff coefficient
          \<and> slp_left_neumann_center_fixed_point_data
            X ?T c cutoff coefficient_tilde)"
    using Z_left_AE
  proof eventually_elim
    fix c
    assume carrier: "c \<in> Omega \<longleftrightarrow> c \<in> Z_left"
    show "c \<in> Omega \<longrightarrow>
        (slp_left_neumann_center_fixed_point_data
          X ?T c cutoff coefficient
        \<and> slp_left_neumann_center_fixed_point_data
          X ?T c cutoff coefficient_tilde)"
    proof
      assume "c \<in> Omega"
      then have "c \<in> Z_left" using carrier by blast
      then show "slp_left_neumann_center_fixed_point_data
          X ?T c cutoff coefficient
        \<and> slp_left_neumann_center_fixed_point_data
          X ?T c cutoff coefficient_tilde"
        using left_data_max by blast
    qed
  qed
  have right_AE:
      "AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longrightarrow>
          (slp_right_neumann_center_fixed_point_data
            X ?T c cutoff coefficient
          \<and> slp_right_neumann_center_fixed_point_data
            X ?T c cutoff coefficient_tilde)"
    using Z_right_AE
  proof eventually_elim
    fix c
    assume carrier: "c \<in> Omega \<longleftrightarrow> c \<in> Z_right"
    show "c \<in> Omega \<longrightarrow>
        (slp_right_neumann_center_fixed_point_data
          X ?T c cutoff coefficient
        \<and> slp_right_neumann_center_fixed_point_data
          X ?T c cutoff coefficient_tilde)"
    proof
      assume "c \<in> Omega"
      then have "c \<in> Z_right" using carrier by blast
      then show "slp_right_neumann_center_fixed_point_data
          X ?T c cutoff coefficient
        \<and> slp_right_neumann_center_fixed_point_data
          X ?T c cutoff coefficient_tilde"
        using right_data_max by blast
    qed
  qed

  obtain Z where Z_measurable:
      "Z \<in> sets (lborel :: slp_point measure)"
    and Z_nonempty: "Z \<noteq> {}"
    and Z_subset: "Z \<subseteq> Omega"
    and Z_AE:
      "AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longleftrightarrow> c \<in> Z"
    and both_data:
      "\<forall>c \<in> Z.
        (slp_left_neumann_center_fixed_point_data
          X ?T c cutoff coefficient
        \<and> slp_left_neumann_center_fixed_point_data
          X ?T c cutoff coefficient_tilde)
        \<and>
        (slp_right_neumann_center_fixed_point_data
          X ?T c cutoff coefficient
        \<and> slp_right_neumann_center_fixed_point_data
          X ?T c cutoff coefficient_tilde)"
    using slp_bounded_smooth_domain_common_carrier[
      OF domain left_AE right_AE] by blast
  show ?thesis
    using T_lower Z_measurable Z_nonempty Z_subset Z_AE both_data by blast
qed

end

end
