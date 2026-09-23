theory Inverse_Schrodinger_Lp_Two_Coefficient_Common_Left_Joint_Series
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Two_Coefficient_Common_Left_Center"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Common-carrier joint left series for two coefficients\<close>

definition slp_left_neumann_joint_geometric_data ::
    "real \<Rightarrow> real \<Rightarrow> slp_point set \<Rightarrow> slp_point set \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
      real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool"
  where
  "slp_left_neumann_joint_geometric_data
      p epsilon X centers cutoff coefficient C CV T \<longleftrightarrow>
    0 < C \<and> 0 < CV \<and> 2 \<le> T \<and>
    (\<forall>tau. T \<le> tau \<longrightarrow>
      (let rho = CV * tau powr (-(1 - 1 / p) + epsilon);
           majorant = (\<lambda>c.
             if c \<in> centers
             then C * tau powr (-(1 - 1 / p) + epsilon) *
               (aim_complex_lp_norm p coefficient +
                 Real_Vector_Spaces.norm (slp_dbar_inverse coefficient c))
             else 0);
           U = (\<lambda>j c z.
             if c \<in> centers
             then slp_restrict_field X
               (slp_neumann_iterate
                 (slp_left_neumann_step tau c cutoff coefficient)
                 (slp_left_neumann_base tau c cutoff coefficient
                   SLP_Dbar_Inverse) j) z
             else 0)
       in rho \<le> 1 / 2
        \<and> (AE pair in lborel \<Otimes>\<^sub>M lborel. \<forall>j.
          Real_Vector_Spaces.norm (U j (fst pair) (snd pair)) \<le>
            majorant (fst pair) * rho ^ j)
        \<and> (\<lambda>pair :: slp_point \<times> slp_point.
          \<Sum>j. U j (fst pair) (snd pair))
            \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)
        \<and> (AE pair in lborel \<Otimes>\<^sub>M lborel.
          summable (\<lambda>j.
            Real_Vector_Spaces.norm (U j (fst pair) (snd pair))))
        \<and> (AE pair in lborel \<Otimes>\<^sub>M lborel.
          summable (\<lambda>j. U j (fst pair) (snd pair)))
        \<and> (AE pair in lborel \<Otimes>\<^sub>M lborel.
          Real_Vector_Spaces.norm
            (\<Sum>j. U j (fst pair) (snd pair)) \<le>
            majorant (fst pair) / (1 - rho))))"

theorem slp_left_neumann_joint_geometric_data_mono:
  assumes data:
    "slp_left_neumann_joint_geometric_data
      p epsilon X centers cutoff coefficient C CV T"
    and threshold: "T \<le> T'"
  shows
    "slp_left_neumann_joint_geometric_data
      p epsilon X centers cutoff coefficient C CV T'"
proof -
  note old_data =
    data[unfolded slp_left_neumann_joint_geometric_data_def]
  note C_positive = conjunct1[OF old_data]
  note after_C = conjunct2[OF old_data]
  note CV_positive = conjunct1[OF after_C]
  note after_CV = conjunct2[OF after_C]
  note T_lower = conjunct1[OF after_CV]
  note universal = conjunct2[OF after_CV]
  have T'_lower: "2 \<le> T'"
    by (rule order_trans[OF T_lower threshold])
  show ?thesis
    unfolding slp_left_neumann_joint_geometric_data_def
    apply (intro conjI)
    subgoal by (rule C_positive)
    subgoal by (rule CV_positive)
    subgoal by (rule T'_lower)
    apply (intro allI impI)
    subgoal premises tau_large for tau
      by (rule universal[rule_format])
        (rule order_trans[OF threshold tau_large])
    done
qed

context slp_cauchy_local_w1s
begin

theorem slp_two_coefficient_common_left_joint_series:
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
    "\<exists>T Z C CV C_tilde CV_tilde.
      2 \<le> T
      \<and> Z \<in> sets (lborel :: slp_point measure)
      \<and> Z \<noteq> {}
      \<and> Z \<subseteq> Omega
      \<and> (AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longleftrightarrow> c \<in> Z)
      \<and> (\<forall>c \<in> Z.
        slp_left_neumann_center_fixed_point_data
          X T c cutoff coefficient
        \<and> slp_left_neumann_center_fixed_point_data
          X T c cutoff coefficient_tilde)
      \<and> slp_left_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient C CV T
      \<and> slp_left_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient_tilde C_tilde CV_tilde T
      \<and> (\<forall>tau c z. T \<le> tau \<and> c \<in> Z \<longrightarrow>
        slp_left_neumann_joint_series_on
          Z X tau cutoff coefficient (c, z) =
            slp_left_neumann_series_sum X tau c cutoff coefficient z
        \<and> slp_left_neumann_joint_series_on
          Z X tau cutoff coefficient_tilde (c, z) =
            slp_left_neumann_series_sum X tau c cutoff coefficient_tilde z)"
proof -
  obtain T0 Z where T0_lower: "2 \<le> T0"
    and Z_measurable: "Z \<in> sets (lborel :: slp_point measure)"
    and Z_nonempty: "Z \<noteq> {}"
    and Z_subset: "Z \<subseteq> Omega"
    and Z_AE:
      "AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longleftrightarrow> c \<in> Z"
    and center_data:
      "\<forall>c \<in> Z.
        slp_left_neumann_center_fixed_point_data
          X T0 c cutoff coefficient
        \<and> slp_left_neumann_center_fixed_point_data
          X T0 c cutoff coefficient_tilde"
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

  have Z_geometry:
      "\<And>c y :: slp_point. c \<in> Z \<Longrightarrow> y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (y - c) \<le> R"
  proof -
    fix c y :: slp_point
    assume c_in: "c \<in> Z"
      and y_in: "y \<in> X"
    have c_in_Omega: "c \<in> Omega"
      using Z_subset c_in by blast
    show "Real_Vector_Spaces.norm (y - c) \<le> R"
      by (rule center_geometry[OF c_in_Omega y_in])
  qed

  have joint_exists:
      "\<exists>C CV T1. slp_left_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient C CV T1"
    unfolding slp_left_neumann_joint_geometric_data_def
    by (rule slp_left_neumann_joint_geometric_series[
      OF riesz_hls cauchy_test_left_inverse evans_density
        exponent_lower exponent_upper loss_positive loss_upper
        radius_nonnegative radius_lower set_radius X_open X_bounded
        cutoff_test cutoff_bound cutoff_derivative_zero_bound
        cutoff_derivative_one_bound A0_nonnegative B0_nonnegative
        B1_nonnegative coefficient_lp coefficient_support
        Z_measurable Z_nonempty Z_geometry])
  then obtain C CV T1 where joint_data:
      "slp_left_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient C CV T1"
    by blast

  have joint_tilde_exists:
      "\<exists>C_tilde CV_tilde T2. slp_left_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient_tilde C_tilde CV_tilde T2"
    unfolding slp_left_neumann_joint_geometric_data_def
    by (rule slp_left_neumann_joint_geometric_series[
      OF riesz_hls cauchy_test_left_inverse evans_density
        exponent_lower exponent_upper loss_positive loss_upper
        radius_nonnegative radius_lower set_radius X_open X_bounded
        cutoff_test cutoff_bound cutoff_derivative_zero_bound
        cutoff_derivative_one_bound A0_nonnegative B0_nonnegative
        B1_nonnegative coefficient_tilde_lp coefficient_tilde_support
        Z_measurable Z_nonempty Z_geometry])
  then obtain C_tilde CV_tilde T2 where joint_tilde_data:
      "slp_left_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient_tilde C_tilde CV_tilde T2"
    by blast

  let ?T = "max T0 (max T1 T2)"
  have T_lower: "2 \<le> ?T"
    using T0_lower by simp
  have T0_le: "T0 \<le> ?T"
    by simp
  have T1_le: "T1 \<le> ?T"
    by simp
  have T2_le: "T2 \<le> ?T"
    by simp

  have center_data_max:
      "\<forall>c \<in> Z.
        slp_left_neumann_center_fixed_point_data
          X ?T c cutoff coefficient
        \<and> slp_left_neumann_center_fixed_point_data
          X ?T c cutoff coefficient_tilde"
  proof (intro ballI conjI)
    fix c
    assume c_in: "c \<in> Z"
    show
      "slp_left_neumann_center_fixed_point_data
        X ?T c cutoff coefficient"
      by (rule slp_left_neumann_center_fixed_point_data_mono[
            OF conjunct1[OF center_data[rule_format, OF c_in]] T0_le])
    show
      "slp_left_neumann_center_fixed_point_data
        X ?T c cutoff coefficient_tilde"
      by (rule slp_left_neumann_center_fixed_point_data_mono[
            OF conjunct2[OF center_data[rule_format, OF c_in]] T0_le])
  qed

  have joint_data_max:
      "slp_left_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient C CV ?T"
    by (rule slp_left_neumann_joint_geometric_data_mono[
          OF joint_data T1_le])
  have joint_tilde_data_max:
      "slp_left_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient_tilde C_tilde CV_tilde ?T"
    by (rule slp_left_neumann_joint_geometric_data_mono[
          OF joint_tilde_data T2_le])

  have fiber_identities:
      "\<forall>tau c z. ?T \<le> tau \<and> c \<in> Z \<longrightarrow>
        slp_left_neumann_joint_series_on
          Z X tau cutoff coefficient (c, z) =
            slp_left_neumann_series_sum X tau c cutoff coefficient z
        \<and> slp_left_neumann_joint_series_on
          Z X tau cutoff coefficient_tilde (c, z) =
            slp_left_neumann_series_sum X tau c cutoff coefficient_tilde z"
    by (intro allI impI)
      (simp add: slp_left_neumann_joint_series_on_fiber)

  show ?thesis
    by (rule exI[of _ ?T], rule exI[of _ Z],
        rule exI[of _ C], rule exI[of _ CV],
        rule exI[of _ C_tilde], rule exI[of _ CV_tilde])
      (use T_lower Z_measurable Z_nonempty Z_subset Z_AE center_data_max
        joint_data_max joint_tilde_data_max fiber_identities in blast)
qed

end

end
