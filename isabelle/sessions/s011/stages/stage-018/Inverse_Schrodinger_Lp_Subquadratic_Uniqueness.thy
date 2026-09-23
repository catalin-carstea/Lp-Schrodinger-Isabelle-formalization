theory Inverse_Schrodinger_Lp_Subquadratic_Uniqueness
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_018.Inverse_Schrodinger_Lp_Zero_Extension_Invariance"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Auxiliary data from the physical bounded domain\<close>

theorem slp_subquadratic_auxiliary_cutoff_exists:
  assumes Omega_bounded: "bounded Omega"
  shows "\<exists>A R X cutoff A0 B0 B1.
    0 \<le> A \<and> 1 \<le> R \<and>
    (\<forall>y::slp_point. y \<in> X \<longrightarrow>
      Real_Vector_Spaces.norm y \<le> A) \<and>
    (\<forall>c y::slp_point. c \<in> Omega \<longrightarrow> y \<in> X \<longrightarrow>
      Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
    open X \<and> bounded X \<and> Omega \<subseteq> X \<and>
    slp_test_function_on X cutoff \<and>
    (\<forall>z. z \<in> Omega \<longrightarrow> cutoff z = 1) \<and>
    (\<forall>x. x \<in> X \<longrightarrow>
      Real_Vector_Spaces.norm (cutoff x) \<le> A0) \<and>
    (\<forall>x. x \<in> X \<longrightarrow>
      Real_Vector_Spaces.norm
        (slp_complex_partial_derivative cutoff 0 x) \<le> B0) \<and>
    (\<forall>x. x \<in> X \<longrightarrow>
      Real_Vector_Spaces.norm
        (slp_complex_partial_derivative cutoff 1 x) \<le> B1) \<and>
    0 \<le> A0 \<and> 0 \<le> B0 \<and> 0 \<le> B1"
proof -
  obtain delta :: real where delta_positive: "0 < delta"
    and Omega_ball: "Omega \<subseteq> ball 0 delta"
    using bounded_subset_ballD[OF Omega_bounded, of "0::slp_point"] by blast
  let ?X = "ball (0::slp_point) (3 * delta)"
  let ?real_cutoff =
    "slp_global_cutoff.slp_scaled_cutoff delta (0::slp_point)"
  let ?cutoff = "\<lambda>z. of_real (?real_cutoff z) :: complex"
  have real_cutoff_smooth: "smooth_on UNIV ?real_cutoff"
    by (rule slp_global_scaled_cutoff_smooth)
  have cutoff_smooth: "smooth_on UNIV ?cutoff"
    unfolding of_real_def
    by (rule smooth_on_scaleR[OF real_cutoff_smooth smooth_on_const open_UNIV])
  have cutoff_nonzero_subset:
      "{x. ?cutoff x \<noteq> 0} \<subseteq> ball 0 (2 * delta)"
  proof
    fix x
    assume cutoff_nonzero: "x \<in> {x. ?cutoff x \<noteq> 0}"
    have radius_strict:
        "Real_Vector_Spaces.norm (x - (0::slp_point)) < 2 * delta"
    proof (rule ccontr)
      assume "\<not> Real_Vector_Spaces.norm (x - (0::slp_point)) <
        2 * delta"
      then have outer:
          "2 * delta \<le>
            Real_Vector_Spaces.norm (x - (0::slp_point))"
        by simp
      have "?real_cutoff x = 0"
        by (rule slp_global_cutoff.slp_scaled_cutoff_outer[
          OF delta_positive outer])
      then show False using cutoff_nonzero by simp
    qed
    show "x \<in> ball 0 (2 * delta)"
      using radius_strict by simp
  qed
  have cutoff_closure_cball:
      "closure {x. ?cutoff x \<noteq> 0} \<subseteq> cball 0 (2 * delta)"
    by (rule closure_minimal) (use cutoff_nonzero_subset in auto)
  have cball_subset_X: "cball 0 (2 * delta) \<subseteq> ?X"
  proof
    fix x :: slp_point
    assume x_in: "x \<in> cball 0 (2 * delta)"
    have x_bound: "Real_Vector_Spaces.norm x \<le> 2 * delta"
      using x_in by simp
    have "Real_Vector_Spaces.norm x < 3 * delta"
      using delta_positive x_bound by linarith
    then show "x \<in> ?X" by simp
  qed
  have cutoff_closure_X: "closure {x. ?cutoff x \<noteq> 0} \<subseteq> ?X"
    using cutoff_closure_cball cball_subset_X by blast
  have cutoff_compact: "compact (closure {x. ?cutoff x \<noteq> 0})"
    by (rule compact_if_closed_subset_of_compact[
      OF closed_closure compact_cball cutoff_closure_cball])
  have cutoff_test: "slp_test_function_on ?X ?cutoff"
    unfolding slp_test_function_on_def
    by (rule conjI[OF cutoff_smooth
          conjI[OF cutoff_compact cutoff_closure_X]])
  have derivative_zero_smooth:
      "smooth_on UNIV (slp_complex_partial_derivative ?cutoff 0)"
    by (rule slp_complex_partial_derivative_smooth[OF cutoff_smooth])
  have derivative_one_smooth:
      "smooth_on UNIV (slp_complex_partial_derivative ?cutoff 1)"
    by (rule slp_complex_partial_derivative_smooth[OF cutoff_smooth])
  have derivative_zero_continuous:
      "continuous_on (cball 0 (3 * delta))
        (slp_complex_partial_derivative ?cutoff 0)"
    by (rule continuous_on_subset[
      OF smooth_on_imp_continuous_on[OF derivative_zero_smooth]]) simp
  have derivative_one_continuous:
      "continuous_on (cball 0 (3 * delta))
        (slp_complex_partial_derivative ?cutoff 1)"
    by (rule continuous_on_subset[
      OF smooth_on_imp_continuous_on[OF derivative_one_smooth]]) simp
  obtain B0 where B0_nonnegative: "0 \<le> B0"
    and B0_bound:
      "\<And>x. x \<in> cball 0 (3 * delta) \<Longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative ?cutoff 0 x) \<le> B0"
    using continuous_on_compact_bound[
      OF compact_cball derivative_zero_continuous] by blast
  obtain B1 where B1_nonnegative: "0 \<le> B1"
    and B1_bound:
      "\<And>x. x \<in> cball 0 (3 * delta) \<Longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative ?cutoff 1 x) \<le> B1"
    using continuous_on_compact_bound[
      OF compact_cball derivative_one_continuous] by blast
  have Omega_subset_X: "Omega \<subseteq> ?X"
  proof
    fix x
    assume x_in: "x \<in> Omega"
    have x_small: "Real_Vector_Spaces.norm x < delta"
      using Omega_ball x_in by auto
    have "Real_Vector_Spaces.norm x < 3 * delta"
      using delta_positive x_small by linarith
    then show "x \<in> ?X" by simp
  qed
  have set_radius:
      "\<And>y::slp_point. y \<in> ?X \<Longrightarrow>
        Real_Vector_Spaces.norm y \<le> 3 * delta"
    by simp
  have center_geometry:
      "\<And>c y::slp_point. c \<in> Omega \<Longrightarrow> y \<in> ?X \<Longrightarrow>
        Real_Vector_Spaces.norm (y - c) \<le> max 1 (4 * delta)"
  proof -
    fix c y :: slp_point
    assume c_in: "c \<in> Omega" and y_in: "y \<in> ?X"
    have c_bound: "Real_Vector_Spaces.norm c < delta"
      using Omega_ball c_in by auto
    have y_bound: "Real_Vector_Spaces.norm y < 3 * delta"
      using y_in by simp
    have triangle:
        "Real_Vector_Spaces.norm (y - c) \<le>
          Real_Vector_Spaces.norm y + Real_Vector_Spaces.norm c"
      by (rule norm_triangle_ineq4)
    have "Real_Vector_Spaces.norm (y - c) \<le> 4 * delta"
      using triangle y_bound c_bound by linarith
    then show "Real_Vector_Spaces.norm (y - c) \<le> max 1 (4 * delta)"
      by simp
  qed
  have cutoff_one: "\<And>z. z \<in> Omega \<Longrightarrow> ?cutoff z = 1"
  proof -
    fix z
    assume z_in: "z \<in> Omega"
    have z_bound: "Real_Vector_Spaces.norm (z - (0::slp_point)) \<le> delta"
      using Omega_ball z_in by auto
    have "?real_cutoff z = 1"
      by (rule slp_global_cutoff.slp_scaled_cutoff_inner[
        OF delta_positive z_bound])
    then show "?cutoff z = 1" by simp
  qed
  have cutoff_bound:
      "\<And>x. x \<in> ?X \<Longrightarrow>
        Real_Vector_Spaces.norm (?cutoff x) \<le> 1"
  proof -
    fix x
    assume "x \<in> ?X"
    have "Real_Vector_Spaces.norm (?real_cutoff x) \<le> 1"
      by (rule slp_global_cutoff.slp_scaled_cutoff_norm)
    then show "Real_Vector_Spaces.norm (?cutoff x) \<le> 1" by simp
  qed
  have derivative_zero_bound:
      "\<And>x. x \<in> ?X \<Longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative ?cutoff 0 x) \<le> B0"
    by (rule B0_bound) auto
  have derivative_one_bound:
      "\<And>x. x \<in> ?X \<Longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative ?cutoff 1 x) \<le> B1"
    by (rule B1_bound) auto
  have chosen_radius_nonnegative: "0 \<le> 3 * delta"
    using delta_positive by linarith
  have chosen_radius_lower: "1 \<le> max 1 (4 * delta)"
    by simp
  have set_radius_all:
      "\<forall>y::slp_point. y \<in> ?X \<longrightarrow>
        Real_Vector_Spaces.norm y \<le> 3 * delta"
    using set_radius by blast
  have center_geometry_all:
      "\<forall>c y::slp_point. c \<in> Omega \<longrightarrow> y \<in> ?X \<longrightarrow>
        Real_Vector_Spaces.norm (y - c) \<le> max 1 (4 * delta)"
    using center_geometry by blast
  have cutoff_one_all: "\<forall>z. z \<in> Omega \<longrightarrow> ?cutoff z = 1"
    using cutoff_one by blast
  have cutoff_bound_all:
      "\<forall>x. x \<in> ?X \<longrightarrow>
        Real_Vector_Spaces.norm (?cutoff x) \<le> 1"
    using cutoff_bound by blast
  have derivative_zero_bound_all:
      "\<forall>x. x \<in> ?X \<longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative ?cutoff 0 x) \<le> B0"
    using derivative_zero_bound by blast
  have derivative_one_bound_all:
      "\<forall>x. x \<in> ?X \<longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative ?cutoff 1 x) \<le> B1"
    using derivative_one_bound by blast
  have auxiliary_interface:
      "0 \<le> 3 * delta \<and> 1 \<le> max 1 (4 * delta) \<and>
      (\<forall>y::slp_point. y \<in> ?X \<longrightarrow>
        Real_Vector_Spaces.norm y \<le> 3 * delta) \<and>
      (\<forall>c y::slp_point. c \<in> Omega \<longrightarrow> y \<in> ?X \<longrightarrow>
        Real_Vector_Spaces.norm (y - c) \<le> max 1 (4 * delta)) \<and>
      open ?X \<and> bounded ?X \<and> Omega \<subseteq> ?X \<and>
      slp_test_function_on ?X ?cutoff \<and>
      (\<forall>z. z \<in> Omega \<longrightarrow> ?cutoff z = 1) \<and>
      (\<forall>x. x \<in> ?X \<longrightarrow>
        Real_Vector_Spaces.norm (?cutoff x) \<le> 1) \<and>
      (\<forall>x. x \<in> ?X \<longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative ?cutoff 0 x) \<le> B0) \<and>
      (\<forall>x. x \<in> ?X \<longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative ?cutoff 1 x) \<le> B1) \<and>
      0 \<le> (1::real) \<and> 0 \<le> B0 \<and> 0 \<le> B1"
    using chosen_radius_nonnegative chosen_radius_lower set_radius_all
      center_geometry_all Omega_subset_X cutoff_test cutoff_one_all
      cutoff_bound_all derivative_zero_bound_all derivative_one_bound_all
      B0_nonnegative B1_nonnegative
    by simp
  show ?thesis
    by (intro exI[where x="3 * delta"]
        exI[where x="max 1 (4 * delta)"] exI[where x="?X"]
        exI[where x="?cutoff"] exI[where x=1]
        exI[where x=B0] exI[where x=B1])
      (rule auxiliary_interface)
qed

theorem slp_zero_extended_div_four_coefficient_data:
  assumes exponent_positive: "0 < p"
    and potential_lp: "slp_complex_lp_on p Omega V"
  shows "aim_complex_lp_on_plane p
      (\<lambda>z. slp_restrict_field Omega V z / 4) \<and>
    {x. slp_restrict_field Omega V x / 4 \<noteq> 0} \<subseteq> Omega"
proof -
  have restricted_lp:
      "aim_complex_lp_on_plane p (slp_restrict_field Omega V)"
    using potential_lp unfolding slp_complex_lp_on_def .
  have scaled_lp:
      "aim_complex_lp_on_plane p
        (\<lambda>z. (1 / 4 :: complex) * slp_restrict_field Omega V z)"
    by (rule slp_complex_lp_bounded_multiplier(1)[where C="1/4",
          OF exponent_positive _ _ _ restricted_lp])
      simp_all
  have coefficient_eq:
      "(\<lambda>z. slp_restrict_field Omega V z / 4) =
        (\<lambda>z. (1 / 4 :: complex) * slp_restrict_field Omega V z)"
    by (rule ext) (simp add: divide_simps)
  have coefficient_lp:
      "aim_complex_lp_on_plane p
        (\<lambda>z. slp_restrict_field Omega V z / 4)"
    using scaled_lp unfolding coefficient_eq .
  have coefficient_support:
      "{x. slp_restrict_field Omega V x / 4 \<noteq> 0} \<subseteq> Omega"
  proof
    fix x
    assume coefficient_nonzero:
      "x \<in> {x. slp_restrict_field Omega V x / 4 \<noteq> 0}"
    show "x \<in> Omega"
    proof (rule ccontr)
      assume "x \<notin> Omega"
      then show False
        using coefficient_nonzero by (simp add: slp_restrict_field_def)
    qed
  qed
  show ?thesis using coefficient_lp coefficient_support by blast
qed

section \<open>Closed subquadratic conditional theorem\<close>

context slp_cgo_full_weak_solution_context
begin

theorem slp_alessandrini_subquadratic_uniqueness:
  fixes p :: real and Omega :: "slp_point set"
    and V V_tilde :: slp_scalar_field
  assumes stationary:
      "hormander_quadratic_stationary_phase_decay_claim TYPE(2)"
    and density: "evans_compact_smooth_l1_density_claim TYPE(2)"
    and fourier_plancherel:
      "hormander_euclidean_l2_fourier_plancherel_claim"
    and riesz_hls: "aim_planar_riesz_hls_claim"
    and cauchy_test_left_inverse:
      "aim_planar_cauchy_test_left_inverse_claim"
    and evans_density: "evans_compact_support_w1p_zero_density_claim"
    and compact_smooth_density:
      "evans_compact_smooth_lp_density_claim TYPE(2)"
    and exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and domain: "slp_bounded_smooth_domain Omega"
    and V_lp: "slp_complex_lp_on p Omega V"
    and V_tilde_lp: "slp_complex_lp_on p Omega V_tilde"
    and orthogonality:
      "slp_alessandrini_orthogonality Omega V V_tilde"
  shows "slp_potential_ae_equal Omega V V_tilde"
proof -
  let ?V0 = "slp_restrict_field Omega V"
  let ?Vt0 = "slp_restrict_field Omega V_tilde"
  let ?q = "\<lambda>z. ?V0 z / 4"
  let ?qt = "\<lambda>z. ?Vt0 z / 4"
  have exponent_positive: "0 < p"
    using exponent_lower by linarith
  have one_div_less_one: "1 / p < 1"
    using exponent_lower exponent_positive
    by (simp add: divide_less_eq)
  let ?epsilon = "(1 - 1 / p) / 2"
  have loss_numerator_positive: "0 < 1 - 1 / p"
    using one_div_less_one by linarith
  have loss_positive: "0 < ?epsilon"
    using loss_numerator_positive by simp
  have loss_upper: "?epsilon < 1 - 1 / p"
    using loss_numerator_positive by simp
  have Omega_bounded: "bounded Omega"
    using domain unfolding slp_bounded_smooth_domain_def by blast
  obtain A R X cutoff A0 B0 B1 where radius_nonnegative: "0 \<le> A"
    and radius_lower: "1 \<le> R"
    and set_radius:
      "\<And>y::slp_point. y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm y \<le> A"
    and center_geometry:
      "\<And>c y::slp_point. c \<in> Omega \<Longrightarrow> y \<in> X \<Longrightarrow>
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
    using slp_subquadratic_auxiliary_cutoff_exists[OF Omega_bounded] by blast
  have q_data:
      "aim_complex_lp_on_plane p ?q \<and> {x. ?q x \<noteq> 0} \<subseteq> Omega"
    by (rule slp_zero_extended_div_four_coefficient_data[
      OF exponent_positive V_lp])
  have qt_data:
      "aim_complex_lp_on_plane p ?qt \<and> {x. ?qt x \<noteq> 0} \<subseteq> Omega"
    by (rule slp_zero_extended_div_four_coefficient_data[
      OF exponent_positive V_tilde_lp])
  have restricted_orthogonality:
      "slp_alessandrini_orthogonality Omega ?V0 ?Vt0"
    by (rule slp_alessandrini_orthogonality_restrict_potentials[
      OF orthogonality])
  have restricted_equal:
      "slp_potential_ae_equal Omega ?V0 ?Vt0"
    by (rule slp_common_cgo_subquadratic_potential_ae_equal[
      OF stationary density fourier_plancherel riesz_hls
        cauchy_test_left_inverse evans_density compact_smooth_density
        exponent_lower exponent_upper loss_positive loss_upper
        radius_nonnegative radius_lower set_radius center_geometry X_open
        X_bounded Omega_subset cutoff_test cutoff_one cutoff_bound
        cutoff_derivative_zero_bound cutoff_derivative_one_bound
        A0_nonnegative B0_nonnegative B1_nonnegative q_data[THEN conjunct1]
        q_data[THEN conjunct2] qt_data[THEN conjunct1]
        qt_data[THEN conjunct2] refl refl domain restricted_orthogonality])
  have Omega_measurable: "Omega \<in> sets lborel"
    using slp_bounded_smooth_domain_lborel_carrier[OF domain] by blast
  show ?thesis
    using restricted_equal
    by (simp only: slp_potential_ae_equal_restrict_potentials_iff[
      OF Omega_measurable])
qed

end

end
