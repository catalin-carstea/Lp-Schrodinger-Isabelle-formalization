theory Inverse_Schrodinger_Lp_Two_Cauchy_Test_Cutoff
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_Two_Cauchy_Local_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Measurable_Below_Two"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Local_Lp_Two"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_One_Sided_Smooth_Error_Limits"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Fixed-support test cutoffs in the two-Cauchy estimate\<close>

lemma slp_bounded_set_pair_distance_radius:
  fixes Y :: "slp_point set"
  assumes bounded: "bounded Y"
  obtains R :: real where "0 < R"
    "\<And>x y. x \<in> Y \<Longrightarrow> y \<in> Y \<Longrightarrow> norm (x - y) \<le> R"
proof -
  obtain B :: real where positive: "0 < B"
    and bound: "\<And>x. x \<in> Y \<Longrightarrow> norm x \<le> B"
    using bounded unfolding bounded_pos by blast
  have radius_positive: "0 < 2 * B" using positive by simp
  have distance: "norm (x - y) \<le> 2 * B"
    if x_in: "x \<in> Y" and y_in: "y \<in> Y" for x y
    by (rule norm_triangle_le_diff)
      (use bound[OF x_in] bound[OF y_in] in linarith)
  show thesis by (rule that[OF radius_positive distance])
qed

context aim_planar_hls_cauchy
begin

lemma slp_cauchy_transform_measurable_above_two_bounded_support:
  fixes f :: slp_scalar_field
  assumes exponent_lower: "2 < r"
    and function_lp: "aim_complex_lp_on_plane r f"
    and support_bounded: "bounded {x. f x \<noteq> 0}"
  shows "slp_cauchy_transform orientation f \<in> borel_measurable lborel"
proof -
  have small_positive: "0 < (3 / 2::real)" by simp
  have order: "(3 / 2::real) \<le> r" using exponent_lower by linarith
  have small_lp: "aim_complex_lp_on_plane (3 / 2) f"
    by (rule aim_complex_lp_on_plane_mono_exponent_bounded_support[
          OF small_positive order support_bounded function_lp])
  show ?thesis
    by (rule slp_cauchy_transform_measurable_below_two[
          where p="3/2", OF _ _ small_lp]) simp_all
qed

theorem slp_two_oscillatory_cauchy_test_cutoff_bound:
  fixes cutoff :: slp_scalar_field and Y :: "slp_point set"
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
    and target_bounded: "bounded Y"
    and cutoff_test: "slp_test_function_on Y cutoff"
  shows "\<exists>C::real. 0 < C \<and>
    (\<forall>tau1 tau2 c1 c2 f outer inner.
      aim_complex_lp_on_plane a f \<longrightarrow>
      slp_cauchy_transform outer
        (slp_oscillatory_modulation tau1 c1
          (\<lambda>y. cutoff y * slp_cauchy_transform inner
            (slp_oscillatory_modulation tau2 c2 f) y))
        \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y.
        slp_cauchy_integrable_at outer
          (slp_oscillatory_modulation tau1 c1
            (\<lambda>y. cutoff y * slp_cauchy_transform inner
              (slp_oscillatory_modulation tau2 c2 f) y)) z \<and>
        norm (slp_cauchy_transform outer
          (slp_oscillatory_modulation tau1 c1
            (\<lambda>y. cutoff y * slp_cauchy_transform inner
              (slp_oscillatory_modulation tau2 c2 f) y)) z) \<le>
          C * aim_complex_lp_norm a f))"
proof -
  have cutoff_plane: "slp_test_function_on UNIV cutoff"
    using cutoff_test unfolding slp_test_function_on_def by auto
  have cutoff_integrable: "integrable lborel cutoff"
    by (rule slp_test_function_integrable_bounded(1)[OF cutoff_plane])
  have cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    by (rule borel_measurable_integrable[OF cutoff_integrable])
  have cutoff_range_bounded: "bounded (range cutoff)"
    by (rule slp_test_function_integrable_bounded(2)[OF cutoff_plane])
  obtain M :: real where M_positive: "0 < M"
    and M_bound: "\<And>y. norm (cutoff y) \<le> M"
    using cutoff_range_bounded unfolding bounded_pos by blast
  have M_nonnegative: "0 \<le> M" using M_positive by linarith
  have cutoff_support: "{y. cutoff y \<noteq> 0} \<subseteq> Y"
    using cutoff_test closure_subset[of "{y. cutoff y \<noteq> 0}"]
    unfolding slp_test_function_on_def by blast
  obtain R :: real where R_positive: "0 < R"
    and R_bound:
      "\<And>x y. x \<in> Y \<Longrightarrow> y \<in> Y \<Longrightarrow> norm (x - y) \<le> R"
    by (rule slp_bounded_set_pair_distance_radius[OF target_bounded]) blast
  have radius: "norm (z - y) \<le> R"
    if "z \<in> Y" "cutoff y \<noteq> 0" for z y
    using R_bound cutoff_support that by blast
  obtain C :: real where C_data:
      "0 < C \<and>
        (\<forall>tau1 tau2 c1 c2 f outer inner.
          aim_complex_lp_on_plane a f \<longrightarrow>
          (\<forall>z\<in>Y.
            slp_cauchy_integrable_at outer
              (slp_oscillatory_modulation tau1 c1
                (\<lambda>y. cutoff y * slp_cauchy_transform inner
                  (slp_oscillatory_modulation tau2 c2 f) y)) z \<and>
            norm (slp_cauchy_transform outer
              (slp_oscillatory_modulation tau1 c1
                (\<lambda>y. cutoff y * slp_cauchy_transform inner
                  (slp_oscillatory_modulation tau2 c2 f) y)) z) \<le>
              C * aim_complex_lp_norm a f))"
    using slp_two_oscillatory_cauchy_cutoff_local_bound[OF exponent_lower
        exponent_upper R_positive cutoff_measurable M_bound M_nonnegative
        radius] ..
  have C_positive: "0 < C" by (rule conjunct1[OF C_data])
  note C_all = C_data[THEN conjunct2]
  have all:
      "\<forall>tau1 tau2 c1 c2 f outer inner.
        aim_complex_lp_on_plane a f \<longrightarrow>
        slp_cauchy_transform outer
          (slp_oscillatory_modulation tau1 c1
            (\<lambda>y. cutoff y * slp_cauchy_transform inner
              (slp_oscillatory_modulation tau2 c2 f) y))
          \<in> borel_measurable lborel \<and>
        (\<forall>z\<in>Y.
          slp_cauchy_integrable_at outer
            (slp_oscillatory_modulation tau1 c1
              (\<lambda>y. cutoff y * slp_cauchy_transform inner
                (slp_oscillatory_modulation tau2 c2 f) y)) z \<and>
          norm (slp_cauchy_transform outer
            (slp_oscillatory_modulation tau1 c1
              (\<lambda>y. cutoff y * slp_cauchy_transform inner
                (slp_oscillatory_modulation tau2 c2 f) y)) z) \<le>
            C * aim_complex_lp_norm a f)"
  proof (intro allI impI)
    fix tau1 tau2 c1 c2 f outer inner
    assume f_lp: "aim_complex_lp_on_plane a f"
    let ?q = "aim_hls_target_exponent a"
    let ?u = "slp_cauchy_transform inner
      (slp_oscillatory_modulation tau2 c2 f)"
    let ?v = "\<lambda>y. cutoff y * ?u y"
    let ?w = "slp_oscillatory_modulation tau1 c1 ?v"
    have q_above_two: "2 < ?q"
      by (rule slp_qstar_exponent_relations(1)[OF exponent_lower exponent_upper])
    have q_positive: "0 < ?q" using q_above_two by linarith
    have u_lp: "aim_complex_lp_on_plane ?q ?u"
    proof -
      obtain H :: real where H_data:
          "0 < H \<and>
            (\<forall>a tau c f orientation.
              1 < a \<and> a < 2 \<and> aim_complex_lp_on_plane a f \<longrightarrow>
              aim_complex_lp_on_plane (aim_hls_target_exponent a)
                (slp_cauchy_transform orientation
                  (slp_oscillatory_modulation tau c f)) \<and>
              aim_complex_lp_norm (aim_hls_target_exponent a)
                (slp_cauchy_transform orientation
                  (slp_oscillatory_modulation tau c f)) \<le>
                H / ((a - 1) * (2 - a)) * aim_complex_lp_norm a f)"
        using slp_oscillatory_cauchy_hls_all_orientations ..
      have hypotheses: "1 < a \<and> a < 2 \<and> aim_complex_lp_on_plane a f"
        by (intro conjI exponent_lower exponent_upper f_lp)
      have hls_instance_data:
          "aim_complex_lp_on_plane ?q ?u \<and>
            aim_complex_lp_norm ?q ?u \<le>
              H / ((a - 1) * (2 - a)) * aim_complex_lp_norm a f"
        by (rule H_data[THEN conjunct2, rule_format, OF hypotheses])
      show ?thesis by (rule conjunct1[OF hls_instance_data])
    qed
    have v_lp: "aim_complex_lp_on_plane ?q ?v"
      by (rule slp_complex_lp_bounded_multiplier(1)[OF q_positive
            cutoff_measurable M_bound M_nonnegative u_lp])
    have w_lp: "aim_complex_lp_on_plane ?q ?w"
      using v_lp by simp
    have w_support: "bounded {y. ?w y \<noteq> 0}"
    proof (rule bounded_subset[OF target_bounded])
      show "{y. ?w y \<noteq> 0} \<subseteq> Y"
        using cutoff_support unfolding slp_oscillatory_modulation_def by auto
    qed
    have measurable:
        "slp_cauchy_transform outer ?w \<in> borel_measurable lborel"
      by (rule slp_cauchy_transform_measurable_above_two_bounded_support[
            OF q_above_two w_lp w_support])
    have bounded:
        "\<forall>z\<in>Y. slp_cauchy_integrable_at outer ?w z \<and>
          norm (slp_cauchy_transform outer ?w z) \<le>
            C * aim_complex_lp_norm a f"
      by (intro ballI) (erule C_all[rule_format, OF f_lp])
    show "slp_cauchy_transform outer ?w \<in> borel_measurable lborel \<and>
        (\<forall>z\<in>Y. slp_cauchy_integrable_at outer ?w z \<and>
          norm (slp_cauchy_transform outer ?w z) \<le>
            C * aim_complex_lp_norm a f)"
      using measurable bounded by blast
  qed
  show ?thesis by (rule exI[of _ C], rule conjI[OF C_positive all])
qed

end

end
