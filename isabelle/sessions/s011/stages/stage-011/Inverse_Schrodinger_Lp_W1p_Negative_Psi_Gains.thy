theory Inverse_Schrodinger_Lp_W1p_Negative_Psi_Gains
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Zero_Quarter_Turn"
begin

section \<open>Measurable-input covariance of the literal oscillatory integral\<close>

theorem slp_dbar_psi_inverse_quarter_turn_measurable:
  assumes f_measurable: "f \<in> borel_measurable lborel"
  shows "slp_dbar_psi_inverse tau (slp_quarter_turn c)
      (\<lambda>x. f (- slp_quarter_turn x)) (slp_quarter_turn z) =
    - \<i> * slp_dbar_psi_inverse (- tau) c f z"
proof -
  let ?g = "\<lambda>x. f (- slp_quarter_turn x)"
  let ?left_source =
    "slp_oscillatory_modulation (- tau) (slp_quarter_turn c) ?g"
  let ?right_source = "slp_oscillatory_modulation tau c f"
  let ?left_integrand =
    "slp_cauchy_integrand SLP_Dbar_Inverse ?left_source (slp_quarter_turn z)"
  let ?right_integrand =
    "slp_cauchy_integrand SLP_Dbar_Inverse ?right_source z"
  have Q_measurable:
      "slp_quarter_turn \<in> measurable (lborel :: slp_point measure) borel"
    using slp_quarter_turn_measurable
    by (simp only: measurable_cong_sets[OF sets_lborel refl])
  have R_measurable:
      "(\<lambda>x. - slp_quarter_turn x) \<in>
        measurable (lborel :: slp_point measure) borel"
    using Q_measurable by measurable
  have f_borel: "f \<in> borel_measurable (borel :: slp_point measure)"
    using f_measurable
    by (simp only: measurable_cong_sets[OF sets_lborel refl])
  have g_measurable: "?g \<in> borel_measurable lborel"
    using measurable_comp[OF R_measurable f_borel]
    by (simp only: comp_def)
  have left_source_measurable: "?left_source \<in> borel_measurable lborel"
    by (rule slp_oscillatory_modulation_measurable[OF g_measurable])
  have left_integrand_measurable: "?left_integrand \<in> borel_measurable lborel"
    by (rule slp_cauchy_integrand_borel_measurable[OF left_source_measurable])
  have left_integrand_borel:
      "?left_integrand \<in> borel_measurable (borel :: slp_point measure)"
    using left_integrand_measurable
    by (simp only: measurable_cong_sets[OF sets_lborel refl])
  have transported_integral:
      "integral\<^sup>L lborel ?left_integrand =
        integral\<^sup>L lborel (\<lambda>y. ?left_integrand (slp_quarter_turn y))"
    using integral_distr[OF Q_measurable left_integrand_borel]
    by (simp only: slp_quarter_turn_distr_lborel)
  have rotated_integrand:
      "(\<lambda>y. ?left_integrand (slp_quarter_turn y)) =
        (\<lambda>y. - \<i> * ?right_integrand y)"
  proof (rule ext)
    fix y :: slp_point
    show "?left_integrand (slp_quarter_turn y) = - \<i> * ?right_integrand y"
      unfolding slp_cauchy_integrand_def slp_oscillatory_modulation_def
      by (simp add: slp_center_kernel_quarter_turn
          slp_dbar_cauchy_kernel_quarter_turn algebra_simps)
  qed
  have scalar_integral:
      "integral\<^sup>L lborel (\<lambda>y. - \<i> * ?right_integrand y) =
        - \<i> * integral\<^sup>L lborel ?right_integrand"
    by (simp only: Bochner_Integration.integral_mult_right_zero)
  have integral_covariance:
      "integral\<^sup>L lborel ?left_integrand =
        - \<i> * integral\<^sup>L lborel ?right_integrand"
    using transported_integral
    by (simp only: rotated_integrand scalar_integral)
  show ?thesis
    unfolding slp_dbar_psi_inverse_eq slp_cauchy_transform_def
    using integral_covariance by (simp add: algebra_simps)
qed

context slp_qstar_centered_smooth_far_hls_context
begin

section \<open>The dbar estimate at negative parameter\<close>

theorem slp_w1p_zero_pair_negative_dbar_psi_gain:
  assumes a_lower: "1 < a" and a_upper: "a < 2"
    and X_bounded: "bounded X"
  shows "\<exists>C::real. 0 < C \<and>
    (\<forall>tau c f Df.
      2 \<le> tau \<and> slp_w1p_zero_pair_on a X f Df \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_dbar_psi_inverse (- tau) c (slp_restrict_field X f)) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
        (slp_dbar_psi_inverse (- tau) c (slp_restrict_field X f))
        \<le> C * inverse (sqrt tau) * slp_w1p_norm_on a X f Df)"
proof -
  let ?Q = slp_quarter_turn
  let ?Y = "image ?Q X"
  have Q_bounded: "bounded_linear ?Q"
    by (simp only: linear_conv_bounded_linear[symmetric] slp_quarter_turn_linear)
  have Y_bounded: "bounded ?Y"
    by (rule bounded_linear_image[OF X_bounded Q_bounded])
  have a_one_le: "1 \<le> a" using a_lower by linarith
  obtain C::real where C_positive: "0 < C"
    and rotated_gain:
      "\<And>tau c f Df. 2 \<le> tau \<Longrightarrow>
        slp_w1p_zero_pair_on a ?Y f Df \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_dbar_psi_inverse tau c (slp_restrict_field ?Y f)) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_dbar_psi_inverse tau c (slp_restrict_field ?Y f))
          \<le> C * inverse (sqrt tau) * slp_w1p_norm_on a ?Y f Df"
    using slp_w1p_zero_pair_dbar_psi_gain[OF a_lower a_upper Y_bounded]
    by blast
  have R_membership: "- ?Q x \<in> X \<longleftrightarrow> x \<in> ?Y" for x
  proof
    assume source: "- ?Q x \<in> X"
    have "?Q (- ?Q x) \<in> ?Y" by (rule imageI[OF source])
    thus "x \<in> ?Y" by simp
  next
    assume "x \<in> ?Y"
    then obtain y where "y \<in> X" "x = ?Q y" by blast
    thus "- ?Q x \<in> X" by simp
  qed
  have negative_gain:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_dbar_psi_inverse (- tau) c (slp_restrict_field X f)) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_dbar_psi_inverse (- tau) c (slp_restrict_field X f))
          \<le> C * inverse (sqrt tau) * slp_w1p_norm_on a X f Df"
    if tau_lower: "2 \<le> tau"
      and zero_pair: "slp_w1p_zero_pair_on a X f Df"
    for tau c f Df
  proof -
    let ?Rf = "\<lambda>x. f (- ?Q x)"
    let ?RDf = "(\<lambda>x. \<chi> i. if i = 0 then - Df (- ?Q x) $ 1
      else Df (- ?Q x) $ 0) :: slp_gradient_field"
    note rotation = slp_w1p_zero_pair_inverse_quarter_turn[OF a_one_le zero_pair]
    have rotated_pair: "slp_w1p_zero_pair_on a ?Y ?Rf ?RDf"
      by (rule conjunct1[OF rotation])
    note positive_data = rotated_gain[OF tau_lower rotated_pair, of "?Q c"]
    let ?D = "slp_dbar_psi_inverse tau (?Q c) (slp_restrict_field ?Y ?Rf)"
    let ?N = "slp_dbar_psi_inverse (- tau) c (slp_restrict_field X f)"
    have base_pair: "slp_w1p_pair_on a X f Df"
      using zero_pair unfolding slp_w1p_zero_pair_on_def by blast
    have f_lp: "aim_complex_lp_on_plane a (slp_restrict_field X f)"
      using slp_w1p_pair_onD(2)[OF base_pair]
      unfolding slp_complex_lp_on_def .
    have f_measurable: "slp_restrict_field X f \<in> borel_measurable lborel"
      using f_lp unfolding aim_complex_lp_on_plane_def by blast
    have rotated_input:
        "slp_restrict_field ?Y ?Rf = (\<lambda>x. slp_restrict_field X f (- ?Q x))"
      by (rule ext) (simp add: slp_restrict_field_def R_membership)
    have covariance: "?D (?Q z) = - \<i> * ?N z" for z
      using slp_dbar_psi_inverse_quarter_turn_measurable[
        OF f_measurable, where tau=tau and c=c and z=z]
      by (simp only: rotated_input)
    have output_identity: "?N = (\<lambda>z. \<i> * ?D (?Q z))"
      by (rule ext) (simp add: covariance algebra_simps)
    note output_rotation =
      slp_aim_complex_lp_on_plane_quarter_turn[OF conjunct1[OF positive_data]]
    have scaled_lp:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (\<lambda>z. \<i> * ?D (?Q z))"
      by (rule aim_complex_lp_on_plane_cmult_unit)
        (simp_all add: conjunct1[OF output_rotation])
    have target_lp: "aim_complex_lp_on_plane (aim_hls_target_exponent a) ?N"
      using scaled_lp by (simp only: output_identity)
    have unit_norm:
        "aim_complex_lp_norm (aim_hls_target_exponent a) (\<lambda>z. \<i> * ?D (?Q z)) =
          aim_complex_lp_norm (aim_hls_target_exponent a) (\<lambda>z. ?D (?Q z))"
      by (simp add: aim_complex_lp_norm_def norm_mult)
    have target_norm:
        "aim_complex_lp_norm (aim_hls_target_exponent a) ?N =
          aim_complex_lp_norm (aim_hls_target_exponent a) ?D"
      using conjunct2[OF output_rotation] by (simp only: output_identity unit_norm)
    have target_bound:
        "aim_complex_lp_norm (aim_hls_target_exponent a) ?N
          \<le> C * inverse (sqrt tau) * slp_w1p_norm_on a X f Df"
      using conjunct2[OF positive_data]
      by (simp only: target_norm conjunct2[OF rotation])
    show ?thesis by (rule conjI[OF target_lp target_bound])
  qed
  show ?thesis
    by (rule exI[of _ C], rule conjI[OF C_positive])
      (use negative_gain in blast)
qed

section \<open>The partial estimate at negative parameter\<close>

theorem slp_w1p_zero_pair_negative_partial_psi_gain:
  assumes a_lower: "1 < a" and a_upper: "a < 2"
    and X_bounded: "bounded X"
  shows "\<exists>C::real. 0 < C \<and>
    (\<forall>tau c f Df.
      2 \<le> tau \<and> slp_w1p_zero_pair_on a X f Df \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_partial_psi_inverse (- tau) c (slp_restrict_field X f)) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
        (slp_partial_psi_inverse (- tau) c (slp_restrict_field X f))
        \<le> C * inverse (sqrt tau) * slp_w1p_norm_on a X f Df)"
proof -
  obtain C::real where C_positive: "0 < C"
    and dbar_gain:
      "\<And>tau c f Df. 2 \<le> tau \<Longrightarrow>
        slp_w1p_zero_pair_on a X f Df \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_dbar_psi_inverse (- tau) c (slp_restrict_field X f)) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_dbar_psi_inverse (- tau) c (slp_restrict_field X f))
          \<le> C * inverse (sqrt tau) * slp_w1p_norm_on a X f Df"
    using slp_w1p_zero_pair_negative_dbar_psi_gain[OF a_lower a_upper X_bounded]
    by blast
  have partial_gain:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_partial_psi_inverse (- tau) c (slp_restrict_field X f)) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_partial_psi_inverse (- tau) c (slp_restrict_field X f))
          \<le> C * inverse (sqrt tau) * slp_w1p_norm_on a X f Df"
    if tau_lower: "2 \<le> tau"
      and zero_pair: "slp_w1p_zero_pair_on a X f Df"
    for tau c f Df
  proof -
    let ?cf = "\<lambda>x. cnj (f x)"
    let ?cDf = "slp_conjugate_gradient Df"
    note conjugate_data = slp_w1p_zero_pair_on_cnj[OF zero_pair]
    have conjugate_pair: "slp_w1p_zero_pair_on a X ?cf ?cDf"
      by (rule conjunct1[OF conjugate_data])
    have conjugate_norm:
        "slp_w1p_norm_on a X ?cf ?cDf = slp_w1p_norm_on a X f Df"
      by (rule conjunct2[OF conjugate_data])
    note dbar_data = dbar_gain[OF tau_lower conjugate_pair, of c]
    have input_conjugate:
        "(\<lambda>x. cnj (slp_restrict_field X ?cf x)) = slp_restrict_field X f"
      by (rule ext) (simp add: slp_restrict_field_def)
    let ?D = "slp_dbar_psi_inverse (- tau) c (slp_restrict_field X ?cf)"
    let ?P = "slp_partial_psi_inverse (- tau) c (slp_restrict_field X f)"
    have output_conjugate: "(\<lambda>x. cnj (?D x)) = ?P"
      by (rule ext)
        (simp only: slp_dbar_psi_inverse_conjugate input_conjugate)
    have output_lp: "aim_complex_lp_on_plane (aim_hls_target_exponent a) ?P"
      using conjunct1[OF dbar_data]
      by (simp only: output_conjugate[symmetric] aim_complex_lp_on_plane_cnj_iff)
    have output_bound:
        "aim_complex_lp_norm (aim_hls_target_exponent a) ?P
          \<le> C * inverse (sqrt tau) * slp_w1p_norm_on a X f Df"
      using conjunct2[OF dbar_data]
      by (simp only: output_conjugate[symmetric] aim_complex_lp_norm_cnj conjugate_norm)
    show ?thesis by (rule conjI[OF output_lp output_bound])
  qed
  show ?thesis
    by (rule exI[of _ C], rule conjI[OF C_positive])
      (use partial_gain in blast)
qed

end

end
