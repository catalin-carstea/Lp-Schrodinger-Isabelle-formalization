theory Inverse_Schrodinger_Lp_Two_Coefficient_Common_Left_Center
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Smooth_Domain_Common_Carrier"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Common left fixed-point data for two coefficients\<close>

definition slp_left_neumann_center_fixed_point_data ::
    "slp_point set \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow> bool"
  where
  "slp_left_neumann_center_fixed_point_data X T c cutoff coefficient \<longleftrightarrow>
    slp_cauchy_integrable_at SLP_Dbar_Inverse coefficient c
    \<and> (\<forall>tau. T \<le> tau \<longrightarrow>
      (\<exists>K::real. slp_ae_bounded_measurable lborel K
        (slp_left_neumann_series_sum X tau c cutoff coefficient))
      \<and> (AE z in lborel.
        slp_left_neumann_series_sum X tau c cutoff coefficient z =
          slp_restrict_field X
            (slp_left_neumann_base tau c cutoff coefficient
              SLP_Dbar_Inverse) z +
          slp_restrict_field X
            (slp_left_neumann_step tau c cutoff coefficient
              (slp_left_neumann_series_sum X tau c cutoff coefficient)) z)
      \<and> (\<forall>candidate K.
        slp_ae_bounded_measurable lborel K candidate
        \<and> (AE z in lborel.
          candidate z =
            slp_restrict_field X
              (slp_left_neumann_base tau c cutoff coefficient
                SLP_Dbar_Inverse) z +
            slp_restrict_field X
              (slp_left_neumann_step tau c cutoff coefficient candidate) z)
        \<longrightarrow>
        (AE z in lborel.
          candidate z =
            slp_left_neumann_series_sum X tau c cutoff coefficient z)))"

theorem slp_left_neumann_center_fixed_point_data_mono:
  assumes data:
    "slp_left_neumann_center_fixed_point_data X T c cutoff coefficient"
    and threshold: "T \<le> T'"
  shows
    "slp_left_neumann_center_fixed_point_data X T' c cutoff coefficient"
proof -
  note unfolded_data =
    data[unfolded slp_left_neumann_center_fixed_point_data_def]
  note integrable = conjunct1[OF unfolded_data]
  note universal = conjunct2[OF unfolded_data]
  show ?thesis
    unfolding slp_left_neumann_center_fixed_point_data_def
    apply (intro conjI)
    subgoal by (rule integrable)
    apply (intro allI impI)
    subgoal premises tau_large for tau
      by (rule universal[rule_format])
        (rule order_trans[OF threshold tau_large])
    done
qed

context slp_cauchy_local_w1s
begin

theorem slp_two_coefficient_common_left_center_fixed_point:
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
          X T c cutoff coefficient_tilde)"
proof -
  obtain T1 :: real where T1_lower: "2 \<le> T1"
    and coefficient_AE:
      "AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longrightarrow>
        slp_left_neumann_center_fixed_point_data
          X T1 c cutoff coefficient"
    using slp_left_neumann_series_ae_center_fixed_point_unique[
      OF riesz_hls cauchy_test_left_inverse evans_density
        exponent_lower exponent_upper loss_positive loss_upper
        radius_nonnegative radius_lower set_radius center_geometry
        X_open X_bounded cutoff_test cutoff_bound
        cutoff_derivative_zero_bound cutoff_derivative_one_bound
        A0_nonnegative B0_nonnegative B1_nonnegative
        coefficient_lp coefficient_support]
    unfolding slp_left_neumann_center_fixed_point_data_def
    by blast

  obtain T2 :: real where T2_lower: "2 \<le> T2"
    and coefficient_tilde_AE:
      "AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longrightarrow>
        slp_left_neumann_center_fixed_point_data
          X T2 c cutoff coefficient_tilde"
    using slp_left_neumann_series_ae_center_fixed_point_unique[
      OF riesz_hls cauchy_test_left_inverse evans_density
        exponent_lower exponent_upper loss_positive loss_upper
        radius_nonnegative radius_lower set_radius center_geometry
        X_open X_bounded cutoff_test cutoff_bound
        cutoff_derivative_zero_bound cutoff_derivative_one_bound
        A0_nonnegative B0_nonnegative B1_nonnegative
        coefficient_tilde_lp coefficient_tilde_support]
    unfolding slp_left_neumann_center_fixed_point_data_def
    by blast

  let ?T = "max T1 T2"
  have T_lower: "2 \<le> ?T"
    using T1_lower by simp

  have coefficient_AE_max:
      "AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longrightarrow>
        slp_left_neumann_center_fixed_point_data
          X ?T c cutoff coefficient"
    using coefficient_AE
  proof eventually_elim
    fix c :: slp_point
    assume data:
      "c \<in> Omega \<longrightarrow>
        slp_left_neumann_center_fixed_point_data
          X T1 c cutoff coefficient"
    show
      "c \<in> Omega \<longrightarrow>
        slp_left_neumann_center_fixed_point_data
          X ?T c cutoff coefficient"
    proof
      assume c_in: "c \<in> Omega"
      have old_data:
          "slp_left_neumann_center_fixed_point_data
            X T1 c cutoff coefficient"
        using data c_in by blast
      show
        "slp_left_neumann_center_fixed_point_data
          X ?T c cutoff coefficient"
        by (rule slp_left_neumann_center_fixed_point_data_mono[OF old_data]) simp
    qed
  qed

  have coefficient_tilde_AE_max:
      "AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longrightarrow>
        slp_left_neumann_center_fixed_point_data
          X ?T c cutoff coefficient_tilde"
    using coefficient_tilde_AE
  proof eventually_elim
    fix c :: slp_point
    assume data:
      "c \<in> Omega \<longrightarrow>
        slp_left_neumann_center_fixed_point_data
          X T2 c cutoff coefficient_tilde"
    show
      "c \<in> Omega \<longrightarrow>
        slp_left_neumann_center_fixed_point_data
          X ?T c cutoff coefficient_tilde"
    proof
      assume c_in: "c \<in> Omega"
      have old_data:
          "slp_left_neumann_center_fixed_point_data
            X T2 c cutoff coefficient_tilde"
        using data c_in by blast
      show
        "slp_left_neumann_center_fixed_point_data
          X ?T c cutoff coefficient_tilde"
        by (rule slp_left_neumann_center_fixed_point_data_mono[OF old_data]) simp
    qed
  qed

  obtain Z where Z_measurable:
      "Z \<in> sets (lborel :: slp_point measure)"
    and Z_nonempty: "Z \<noteq> {}"
    and Z_subset: "Z \<subseteq> Omega"
    and Z_AE:
      "AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longleftrightarrow> c \<in> Z"
    and Z_data:
      "\<forall>c \<in> Z.
        slp_left_neumann_center_fixed_point_data
          X ?T c cutoff coefficient
        \<and> slp_left_neumann_center_fixed_point_data
          X ?T c cutoff coefficient_tilde"
    using slp_bounded_smooth_domain_common_carrier[
      where P = "\<lambda>c. slp_left_neumann_center_fixed_point_data
        X ?T c cutoff coefficient"
        and Q = "\<lambda>c. slp_left_neumann_center_fixed_point_data
          X ?T c cutoff coefficient_tilde",
      OF domain coefficient_AE_max coefficient_tilde_AE_max]
    by blast

  show ?thesis
    by (rule exI[of _ ?T], rule exI[of _ Z])
      (use T_lower Z_measurable Z_nonempty Z_subset Z_AE Z_data in blast)
qed

end

end
