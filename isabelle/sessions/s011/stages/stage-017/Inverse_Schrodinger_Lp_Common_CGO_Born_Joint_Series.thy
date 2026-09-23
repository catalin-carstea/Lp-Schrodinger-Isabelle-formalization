theory Inverse_Schrodinger_Lp_Common_CGO_Born_Joint_Series
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_Common_CGO_Alessandrini_Born_Family"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Two_Coefficient_Common_Left_Joint_Series"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Two_Coefficient_Common_Right_Joint_Series"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Joint Neumann representatives on the Born-family carrier\<close>

context slp_cgo_full_weak_solution_context
begin

theorem slp_common_cgo_born_joint_series:
  fixes p epsilon A R A0 B0 B1 :: real
    and Omega X :: "slp_point set"
    and cutoff coefficient coefficient_tilde V V_tilde :: slp_scalar_field
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
    and Omega_subset: "Omega \<subseteq> X"
    and cutoff_test: "slp_test_function_on X cutoff"
    and cutoff_one: "\<And>z. z \<in> Omega \<Longrightarrow> cutoff z = 1"
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
    and coefficient_normalization: "coefficient = (\<lambda>z. V z / 4)"
    and coefficient_tilde_normalization:
      "coefficient_tilde = (\<lambda>z. V_tilde z / 4)"
    and domain: "slp_bounded_smooth_domain Omega"
    and orthogonality:
      "slp_alessandrini_orthogonality Omega V V_tilde"
  shows
    "\<exists>T Z C CV C_tilde CV_tilde.
      2 \<le> T
      \<and> Z \<in> sets (lborel :: slp_point measure)
      \<and> Z \<noteq> {}
      \<and> Z \<subseteq> Omega
      \<and> (AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longleftrightarrow> c \<in> Z)
      \<and> slp_left_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient C CV T
      \<and> slp_right_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient_tilde C_tilde CV_tilde T
      \<and> (\<forall>tau c z. T \<le> tau \<and> c \<in> Z \<longrightarrow>
        slp_left_neumann_joint_series_on
          Z X tau cutoff coefficient (c, z) =
            slp_left_neumann_series_sum X tau c cutoff coefficient z
        \<and> slp_right_neumann_joint_series_on
          Z X tau cutoff coefficient_tilde (c, z) =
            slp_right_neumann_series_sum
              X tau c cutoff coefficient_tilde z)
      \<and> (\<forall>tau c. T \<le> tau \<longrightarrow> c \<in> Z \<longrightarrow>
        set_integrable lborel Omega
          (\<lambda>x. (V x - V_tilde x) *
            (slp_center_kernel tau c x +
              slp_left_neumann_series_sum
                X tau c cutoff coefficient x +
              slp_right_neumann_series_sum
                X tau c cutoff coefficient_tilde x +
              slp_center_kernel (- tau) c x *
                slp_left_neumann_series_sum
                  X tau c cutoff coefficient x *
                slp_right_neumann_series_sum
                  X tau c cutoff coefficient_tilde x))
        \<and>
        set_lebesgue_integral lborel Omega
          (\<lambda>x. (V x - V_tilde x) *
            (slp_center_kernel tau c x +
              slp_left_neumann_series_sum
                X tau c cutoff coefficient x +
              slp_right_neumann_series_sum
                X tau c cutoff coefficient_tilde x +
              slp_center_kernel (- tau) c x *
                slp_left_neumann_series_sum
                  X tau c cutoff coefficient x *
                slp_right_neumann_series_sum
                  X tau c cutoff coefficient_tilde x)) = 0)"
proof -
  obtain T0 Z where T0_lower: "2 \<le> T0"
    and Z_measurable: "Z \<in> sets (lborel :: slp_point measure)"
    and Z_nonempty: "Z \<noteq> {}"
    and Z_subset: "Z \<subseteq> Omega"
    and Z_AE:
      "AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longleftrightarrow> c \<in> Z"
    and born0:
      "\<forall>tau c. T0 \<le> tau \<longrightarrow> c \<in> Z \<longrightarrow>
        set_integrable lborel Omega
          (\<lambda>x. (V x - V_tilde x) *
            (slp_center_kernel tau c x +
              slp_left_neumann_series_sum
                X tau c cutoff coefficient x +
              slp_right_neumann_series_sum
                X tau c cutoff coefficient_tilde x +
              slp_center_kernel (- tau) c x *
                slp_left_neumann_series_sum
                  X tau c cutoff coefficient x *
                slp_right_neumann_series_sum
                  X tau c cutoff coefficient_tilde x))
        \<and>
        set_lebesgue_integral lborel Omega
          (\<lambda>x. (V x - V_tilde x) *
            (slp_center_kernel tau c x +
              slp_left_neumann_series_sum
                X tau c cutoff coefficient x +
              slp_right_neumann_series_sum
                X tau c cutoff coefficient_tilde x +
              slp_center_kernel (- tau) c x *
                slp_left_neumann_series_sum
                  X tau c cutoff coefficient x *
                slp_right_neumann_series_sum
                  X tau c cutoff coefficient_tilde x)) = 0"
    using slp_common_literal_cgo_alessandrini_born_family[
      OF riesz_hls cauchy_test_left_inverse evans_density
        exponent_lower exponent_upper loss_positive loss_upper
        radius_nonnegative radius_lower set_radius center_geometry
        X_open X_bounded Omega_subset cutoff_test cutoff_one cutoff_bound
        cutoff_derivative_zero_bound cutoff_derivative_one_bound
        A0_nonnegative B0_nonnegative B1_nonnegative coefficient_lp
        coefficient_support coefficient_tilde_lp coefficient_tilde_support
        coefficient_normalization coefficient_tilde_normalization domain
        orthogonality]
    by blast

  have Z_geometry:
      "\<And>c y :: slp_point. c \<in> Z \<Longrightarrow> y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (y - c) \<le> R"
  proof -
    fix c y :: slp_point
    assume c_in: "c \<in> Z" and y_in: "y \<in> X"
    have "c \<in> Omega" using Z_subset c_in by blast
    then show "Real_Vector_Spaces.norm (y - c) \<le> R"
      by (rule center_geometry[OF _ y_in])
  qed

  have left_exists:
      "\<exists>C CV T. slp_left_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient C CV T"
    unfolding slp_left_neumann_joint_geometric_data_def
    by (rule slp_left_neumann_joint_geometric_series[
      OF riesz_hls cauchy_test_left_inverse evans_density
        exponent_lower exponent_upper loss_positive loss_upper
        radius_nonnegative radius_lower set_radius X_open X_bounded
        cutoff_test cutoff_bound cutoff_derivative_zero_bound
        cutoff_derivative_one_bound A0_nonnegative B0_nonnegative
        B1_nonnegative coefficient_lp coefficient_support Z_measurable
        Z_nonempty Z_geometry])
  then obtain C CV T_left where left_data:
      "slp_left_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient C CV T_left"
    by blast
  have right_exists:
      "\<exists>C_tilde CV_tilde T. slp_right_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient_tilde C_tilde CV_tilde T"
    unfolding slp_right_neumann_joint_geometric_data_def
    by (rule slp_right_neumann_joint_geometric_series[
      OF riesz_hls cauchy_test_left_inverse evans_density
        exponent_lower exponent_upper loss_positive loss_upper
        radius_nonnegative radius_lower set_radius X_open X_bounded
        cutoff_test cutoff_bound cutoff_derivative_zero_bound
        cutoff_derivative_one_bound A0_nonnegative B0_nonnegative
        B1_nonnegative coefficient_tilde_lp coefficient_tilde_support
        Z_measurable Z_nonempty Z_geometry])
  then obtain C_tilde CV_tilde T_right where right_data:
      "slp_right_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient_tilde C_tilde CV_tilde T_right"
    by blast

  let ?T = "max T0 (max T_left T_right)"
  have T_lower: "2 \<le> ?T" using T0_lower by simp
  have left_data_max:
      "slp_left_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient C CV ?T"
    by (rule slp_left_neumann_joint_geometric_data_mono[OF left_data]) simp
  have right_data_max:
      "slp_right_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient_tilde C_tilde CV_tilde ?T"
    by (rule slp_right_neumann_joint_geometric_data_mono[OF right_data]) simp
  have fibers:
      "\<forall>tau c z. ?T \<le> tau \<and> c \<in> Z \<longrightarrow>
        slp_left_neumann_joint_series_on
          Z X tau cutoff coefficient (c, z) =
            slp_left_neumann_series_sum X tau c cutoff coefficient z
        \<and> slp_right_neumann_joint_series_on
          Z X tau cutoff coefficient_tilde (c, z) =
            slp_right_neumann_series_sum
              X tau c cutoff coefficient_tilde z"
    by (intro allI impI)
      (simp add: slp_left_neumann_joint_series_on_fiber
        slp_right_neumann_joint_series_on_fiber)
  have born_max:
      "\<forall>tau c. ?T \<le> tau \<longrightarrow> c \<in> Z \<longrightarrow>
        set_integrable lborel Omega
          (\<lambda>x. (V x - V_tilde x) *
            (slp_center_kernel tau c x +
              slp_left_neumann_series_sum
                X tau c cutoff coefficient x +
              slp_right_neumann_series_sum
                X tau c cutoff coefficient_tilde x +
              slp_center_kernel (- tau) c x *
                slp_left_neumann_series_sum
                  X tau c cutoff coefficient x *
                slp_right_neumann_series_sum
                  X tau c cutoff coefficient_tilde x))
        \<and>
        set_lebesgue_integral lborel Omega
          (\<lambda>x. (V x - V_tilde x) *
            (slp_center_kernel tau c x +
              slp_left_neumann_series_sum
                X tau c cutoff coefficient x +
              slp_right_neumann_series_sum
                X tau c cutoff coefficient_tilde x +
              slp_center_kernel (- tau) c x *
                slp_left_neumann_series_sum
                  X tau c cutoff coefficient x *
                slp_right_neumann_series_sum
                  X tau c cutoff coefficient_tilde x)) = 0"
  proof (intro allI impI)
    fix tau c
    assume tau_large: "?T \<le> tau" and c_in: "c \<in> Z"
    have "T0 \<le> tau" using tau_large by simp
    then show
      "set_integrable lborel Omega
          (\<lambda>x. (V x - V_tilde x) *
            (slp_center_kernel tau c x +
              slp_left_neumann_series_sum
                X tau c cutoff coefficient x +
              slp_right_neumann_series_sum
                X tau c cutoff coefficient_tilde x +
              slp_center_kernel (- tau) c x *
                slp_left_neumann_series_sum
                  X tau c cutoff coefficient x *
                slp_right_neumann_series_sum
                  X tau c cutoff coefficient_tilde x))
        \<and>
        set_lebesgue_integral lborel Omega
          (\<lambda>x. (V x - V_tilde x) *
            (slp_center_kernel tau c x +
              slp_left_neumann_series_sum
                X tau c cutoff coefficient x +
              slp_right_neumann_series_sum
                X tau c cutoff coefficient_tilde x +
              slp_center_kernel (- tau) c x *
                slp_left_neumann_series_sum
                  X tau c cutoff coefficient x *
                slp_right_neumann_series_sum
                  X tau c cutoff coefficient_tilde x)) = 0"
      using born0 c_in by blast
  qed
  show ?thesis
    by (rule exI[of _ ?T], rule exI[of _ Z], rule exI[of _ C],
        rule exI[of _ CV], rule exI[of _ C_tilde],
        rule exI[of _ CV_tilde])
      (use T_lower Z_measurable Z_nonempty Z_subset Z_AE left_data_max
        right_data_max fibers born_max in blast)
qed

end

end
