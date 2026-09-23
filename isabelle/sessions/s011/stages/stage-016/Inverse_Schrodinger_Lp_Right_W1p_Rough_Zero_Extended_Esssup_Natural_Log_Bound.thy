theory Inverse_Schrodinger_Lp_Right_W1p_Rough_Zero_Extended_Esssup_Natural_Log_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_W1p_Rough_Zero_Extended_Esssup_Natural_Log_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Negative_Psi_Gains"
begin

section \<open>Negative-parameter dbar rough endpoint\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem
  slp_w1p_zero_pair_negative_dbar_psi_inverse_rough_zero_extended_esssup_natural_log_bound:
  fixes b A R tau :: real
    and X :: "slp_point set"
    and u :: slp_scalar_field
    and Du :: slp_gradient_field
    and c :: slp_point
  assumes tau_lower: "2 \<le> tau"
    and exponent_above_two: "2 < b"
    and radius_nonnegative: "0 \<le> A"
    and radius_lower: "1 \<le> R"
    and set_radius:
      "\<And>y :: slp_point. y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm y \<le> A"
    and relative_radius:
      "\<And>y :: slp_point. y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (y - c) \<le> R"
    and X_measurable: "X \<in> sets lborel"
    and zero_pair: "slp_w1p_zero_pair_on b X u Du"
  defines "q \<equiv> slp_holder_conjugate b"
  shows zero_extended_modulus_measurable:
      "(\<lambda>z :: slp_point.
        ereal (Real_Vector_Spaces.norm
          (slp_restrict_field X
            (slp_dbar_psi_inverse (- tau) c
              (slp_restrict_field X u)) z)))
        \<in> borel_measurable (lborel :: slp_point measure)"
    and zero_extended_esssup_bound:
      "(let
          P = Real_Vector_Spaces.norm
            (inverse (of_real pi :: complex));
          K = P *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x)
                powr q)) powr (1 / q);
          W = slp_w1p_norm_on b X u Du;
          M = K * (192 * W);
          I = integral\<^sup>L lborel (slp_localized_cauchy_kernel 1);
          J = integral\<^sup>L lborel (slp_squared_radial_annulus 1 2);
          C = 6 * I + 2 * unit_ball_vol 2;
          N0 = P * M * C;
          B0 = 2 * M;
          DB0 = K * (2 * (4 * W));
          CB0 = ((P * slp_global_cutoff_L) * M) * C;
          C0 = N0 + (B0 + (DB0 + (CB0 + P * M * I)));
          C1 = P * M * J
        in
          esssup (lborel :: slp_point measure)
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_dbar_psi_inverse (- tau) c
                    (slp_restrict_field X u)) z)))
          \<le>
          ereal
            (inverse (sqrt tau) * ln (2 + tau) *
              (C0 / ln 2 + C1 * ((2 + log 2 R) / ln 2))))"
proof -
  let ?Q = slp_quarter_turn
  let ?Y = "image ?Q X"
  let ?Ru = "\<lambda>x. u (- ?Q x)"
  let ?RDu =
    "(\<lambda>x. \<chi> i. if i = 0 then - Du (- ?Q x) $ 1
      else Du (- ?Q x) $ 0) :: slp_gradient_field"
  let ?cRu = "\<lambda>x. cnj (?Ru x)"
  let ?cRDu = "slp_conjugate_gradient ?RDu"
  let ?f = "slp_restrict_field X u"
  let ?g = "slp_oscillatory_modulation tau c ?f"
  let ?Pout =
    "slp_partial_psi_inverse tau (?Q c)
      (slp_restrict_field ?Y ?cRu)"
  let ?Dout =
    "slp_dbar_psi_inverse tau (?Q c)
      (slp_restrict_field ?Y ?Ru)"
  let ?Nout = "slp_dbar_psi_inverse (- tau) c ?f"
  let ?hY = "slp_restrict_field ?Y ?Pout"
  let ?hX = "slp_restrict_field X ?Nout"

  have exponent_one_le: "1 \<le> b"
    using exponent_above_two by linarith
  have X_bounded: "bounded X"
    unfolding bounded_iff
  proof (rule exI[of _ A], intro ballI)
    fix y :: slp_point
    assume "y \<in> X"
    then show "Real_Vector_Spaces.norm y \<le> A"
      by (rule set_radius)
  qed
  have Q_bounded: "bounded_linear ?Q"
    by (simp only: linear_conv_bounded_linear[symmetric]
          slp_quarter_turn_linear)
  have Y_bounded: "bounded ?Y"
    by (rule bounded_linear_image[OF X_bounded Q_bounded])
  have Q_membership: "?Q z \<in> ?Y \<longleftrightarrow> z \<in> X" for z
  proof
    assume "?Q z \<in> ?Y"
    then obtain x where x_in: "x \<in> X" and Q_eq: "?Q z = ?Q x"
      by blast
    have twice_eq: "?Q (?Q z) = ?Q (?Q x)"
      by (rule arg_cong[OF Q_eq])
    have "z = x"
      using twice_eq by simp
    then show "z \<in> X"
      using x_in by simp
  next
    assume "z \<in> X"
    then show "?Q z \<in> ?Y"
      by (rule imageI)
  qed
  have inverse_membership: "- ?Q y \<in> X \<longleftrightarrow> y \<in> ?Y" for y
  proof
    assume source: "- ?Q y \<in> X"
    have "?Q (- ?Q y) \<in> ?Y"
      by (rule imageI[OF source])
    then show "y \<in> ?Y"
      by simp
  next
    assume "y \<in> ?Y"
    then obtain x where x_in: "x \<in> X" and y_eq: "y = ?Q x"
      by blast
    show "- ?Q y \<in> X"
      using x_in y_eq by simp
  qed
  have R_measurable:
      "(\<lambda>y. - ?Q y) \<in>
        measurable (lborel :: slp_point measure) borel"
  proof -
    have Q_measurable:
        "?Q \<in> measurable (lborel :: slp_point measure) borel"
      using slp_quarter_turn_measurable
      by (simp only: measurable_cong_sets[OF sets_lborel refl])
    show ?thesis
      using Q_measurable by measurable
  qed
  have Y_measurable: "?Y \<in> sets lborel"
  proof -
    have X_borel: "X \<in> sets borel"
      using X_measurable by simp
    have preimage:
        "(\<lambda>y. - ?Q y) -` X \<inter> space lborel \<in> sets lborel"
      by (rule measurable_sets[OF R_measurable X_borel])
    have Y_eq:
        "?Y = (\<lambda>y. - ?Q y) -` X \<inter> space lborel"
    proof
      show "?Y \<subseteq> (\<lambda>y. - ?Q y) -` X \<inter> space lborel"
        using inverse_membership by auto
      show "(\<lambda>y. - ?Q y) -` X \<inter> space lborel \<subseteq> ?Y"
        using inverse_membership by auto
    qed
    show ?thesis
      using preimage unfolding Y_eq .
  qed
  have Y_set_radius:
      "\<And>y :: slp_point. y \<in> ?Y \<Longrightarrow>
        Real_Vector_Spaces.norm y \<le> A"
  proof -
    fix y :: slp_point
    assume "y \<in> ?Y"
    then obtain x where x_in: "x \<in> X" and y_eq: "y = ?Q x"
      by blast
    show "Real_Vector_Spaces.norm y \<le> A"
      using set_radius[OF x_in] unfolding y_eq by simp
  qed
  have Y_relative_radius:
      "\<And>y :: slp_point. y \<in> ?Y \<Longrightarrow>
        Real_Vector_Spaces.norm (y - ?Q c) \<le> R"
  proof -
    fix y :: slp_point
    assume "y \<in> ?Y"
    then obtain x where x_in: "x \<in> X" and y_eq: "y = ?Q x"
      by blast
    have "y - ?Q c = ?Q (x - c)"
      unfolding y_eq by (simp only: linear_diff[OF slp_quarter_turn_linear])
    then show "Real_Vector_Spaces.norm (y - ?Q c) \<le> R"
      using relative_radius[OF x_in] by simp
  qed

  note rotation = slp_w1p_zero_pair_inverse_quarter_turn[
    OF exponent_one_le zero_pair]
  have rotated_pair: "slp_w1p_zero_pair_on b ?Y ?Ru ?RDu"
    by (rule conjunct1[OF rotation])
  have rotated_norm:
      "slp_w1p_norm_on b ?Y ?Ru ?RDu = slp_w1p_norm_on b X u Du"
    by (rule conjunct2[OF rotation])
  note conjugation = slp_w1p_zero_pair_on_cnj[OF rotated_pair]
  have conjugate_pair: "slp_w1p_zero_pair_on b ?Y ?cRu ?cRDu"
    by (rule conjunct1[OF conjugation])
  have conjugate_norm:
      "slp_w1p_norm_on b ?Y ?cRu ?cRDu =
        slp_w1p_norm_on b X u Du"
    using conjunct2[OF conjugation] rotated_norm by simp

  note positive =
    slp_w1p_zero_pair_partial_psi_inverse_rough_zero_extended_esssup_natural_log_bound[
      where b = b and A = A and R = R and tau = tau and X = ?Y and u = ?cRu
        and Du = ?cRDu and c = "?Q c",
      OF tau_lower exponent_above_two radius_nonnegative radius_lower
        Y_set_radius Y_relative_radius Y_measurable conjugate_pair,
      folded q_def]

  let ?P =
    "Real_Vector_Spaces.norm (inverse (of_real pi :: complex))"
  let ?K =
    "?P *
      (integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
        powr (1 / q)"
  let ?W = "slp_w1p_norm_on b X u Du"
  let ?M = "?K * (192 * ?W)"
  let ?I = "integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
  let ?J = "integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
  let ?C = "6 * ?I + 2 * unit_ball_vol 2"
  let ?N0 = "?P * ?M * ?C"
  let ?B0 = "2 * ?M"
  let ?DB0 = "?K * (2 * (4 * ?W))"
  let ?CB0 = "((?P * slp_global_cutoff_L) * ?M) * ?C"
  let ?C0 = "?N0 + (?B0 + (?DB0 + (?CB0 + ?P * ?M * ?I)))"
  let ?C1 = "?P * ?M * ?J"
  let ?B =
    "inverse (sqrt tau) * ln (2 + tau) *
      (?C0 / ln 2 + ?C1 * ((2 + log 2 R) / ln 2))"

  have hY_measurable:
      "(\<lambda>y :: slp_point.
        ereal (Real_Vector_Spaces.norm (?hY y)))
        \<in> borel_measurable (lborel :: slp_point measure)"
    by (rule positive(1))
  have hY_esssup:
      "esssup (lborel :: slp_point measure)
          (\<lambda>y :: slp_point.
            ereal (Real_Vector_Spaces.norm (?hY y)))
        \<le> ereal ?B"
    using positive(2)
    unfolding Let_def
    by (simp only: conjugate_norm)
  have hY_AE:
      "AE y in lborel.
        ereal (Real_Vector_Spaces.norm (?hY y)) \<le> ereal ?B"
  proof -
    have below:
        "AE y in lborel.
          ereal (Real_Vector_Spaces.norm (?hY y)) \<le>
            esssup (lborel :: slp_point measure)
              (\<lambda>w :: slp_point.
                ereal (Real_Vector_Spaces.norm (?hY w)))"
      by (rule esssup_AE)
    show ?thesis
      using below
    proof eventually_elim
      fix y :: slp_point
      assume at_y:
        "ereal (Real_Vector_Spaces.norm (?hY y)) \<le>
          esssup (lborel :: slp_point measure)
            (\<lambda>w :: slp_point.
              ereal (Real_Vector_Spaces.norm (?hY w)))"
      show "ereal (Real_Vector_Spaces.norm (?hY y)) \<le> ereal ?B"
        by (rule order_trans[OF at_y hY_esssup])
    qed
  qed

  have base_pair: "slp_w1p_pair_on b X u Du"
    using zero_pair unfolding slp_w1p_zero_pair_on_def by blast
  have f_lp: "aim_complex_lp_on_plane b ?f"
    using slp_w1p_pair_onD(2)[OF base_pair]
    unfolding slp_complex_lp_on_def .
  have f_measurable: "?f \<in> borel_measurable lborel"
    using f_lp unfolding aim_complex_lp_on_plane_def by blast
  have rotated_input:
      "slp_restrict_field ?Y ?Ru = (\<lambda>x. ?f (- ?Q x))"
    by (rule ext) (simp add: slp_restrict_field_def inverse_membership)
  have conjugate_input:
      "(\<lambda>x. cnj (slp_restrict_field ?Y ?cRu x)) =
        slp_restrict_field ?Y ?Ru"
    by (rule ext) (simp add: slp_restrict_field_def)
  have output_conjugate: "cnj (?Pout y) = ?Dout y" for y
    by (simp only: slp_partial_psi_inverse_conjugate conjugate_input)
  have covariance: "?Dout (?Q z) = - \<i> * ?Nout z" for z
    using slp_dbar_psi_inverse_quarter_turn_measurable[
      OF f_measurable, where tau=tau and c=c and z=z]
    by (simp only: rotated_input)
  have output_norm:
      "Real_Vector_Spaces.norm (?Pout (?Q z)) =
        Real_Vector_Spaces.norm (?Nout z)" for z
  proof -
    have "Real_Vector_Spaces.norm (?Pout (?Q z)) =
        Real_Vector_Spaces.norm (cnj (?Pout (?Q z)))"
      by (simp only: complex_mod_cnj)
    also have "... = Real_Vector_Spaces.norm (?Dout (?Q z))"
      by (simp only: output_conjugate)
    also have "... = Real_Vector_Spaces.norm (- \<i> * ?Nout z)"
      by (simp only: covariance)
    also have "... = Real_Vector_Spaces.norm (?Nout z)"
      by (simp add: norm_mult)
    finally show ?thesis .
  qed
  have restricted_norm:
      "Real_Vector_Spaces.norm (?hY (?Q z)) =
        Real_Vector_Spaces.norm (?hX z)" for z
    by (cases "z \<in> X")
      (simp_all add: slp_restrict_field_def Q_membership output_norm)

  have Q_measurable:
      "?Q \<in> measurable (lborel :: slp_point measure) borel"
    using slp_quarter_turn_measurable
    by (simp only: measurable_cong_sets[OF sets_lborel refl])
  let ?Pred =
    "\<lambda>y :: slp_point.
      ereal (Real_Vector_Spaces.norm (?hY y)) \<le> ereal ?B"
  have Pred_measurable: "Measurable.pred lborel ?Pred"
    by (rule pred_le_const[OF hY_measurable]) simp
  have Pred_borel_measurable: "Measurable.pred borel ?Pred"
  proof -
    have sets_eq:
        "sets (lborel :: slp_point measure) = sets borel"
      by (rule sets_lborel)
    have spaces_eq:
        "space (lborel :: slp_point measure) = space borel"
      by (rule sets_eq_imp_space_eq[OF sets_eq])
    show ?thesis
      using Pred_measurable
      unfolding Measurable.pred_def
      by (simp only: sets_eq spaces_eq)
  qed
  have Pred_borel_set: "{y \<in> space borel. ?Pred y} \<in> sets borel"
    using Pred_borel_measurable
    unfolding Measurable.pred_def .
  have Pred_distr: "AE y in distr lborel borel ?Q. ?Pred y"
    using hY_AE by (simp only: slp_quarter_turn_distr_lborel)
  have pulled_AE: "AE z in lborel. ?Pred (?Q z)"
    using AE_distr_iff[OF Q_measurable Pred_borel_set] Pred_distr by blast
  have hX_AE:
      "AE z in lborel.
        ereal (Real_Vector_Spaces.norm (?hX z)) \<le> ereal ?B"
    using pulled_AE by (simp only: restricted_norm)

  have g_lp: "aim_complex_lp_on_plane b ?g"
    using f_lp by simp
  have f_support_subset: "{x. ?f x \<noteq> 0} \<subseteq> X"
    unfolding slp_restrict_field_def by auto
  have f_support_bounded: "bounded {x. ?f x \<noteq> 0}"
    by (rule bounded_subset[OF X_bounded f_support_subset])
  have g_support_bounded: "bounded {x. ?g x \<noteq> 0}"
    using f_support_bounded by simp
  have transform_measurable:
      "slp_cauchy_transform SLP_Dbar_Inverse ?g
        \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_above_two_bounded_support[
      OF exponent_above_two g_lp g_support_bounded])
  have Nout_measurable: "?Nout \<in> borel_measurable lborel"
    using transform_measurable
    unfolding slp_dbar_psi_inverse_def by simp
  have hX_measurable: "?hX \<in> borel_measurable lborel"
    by (rule slp_restrict_field_measurable[
      OF X_measurable Nout_measurable])
  have hX_modulus_measurable:
      "(\<lambda>z :: slp_point.
        ereal (Real_Vector_Spaces.norm (?hX z)))
        \<in> borel_measurable (lborel :: slp_point measure)"
    using hX_measurable by measurable

  show zero_extended_modulus_measurable:
      "(\<lambda>z :: slp_point.
        ereal (Real_Vector_Spaces.norm
          (slp_restrict_field X
            (slp_dbar_psi_inverse (- tau) c
              (slp_restrict_field X u)) z)))
        \<in> borel_measurable (lborel :: slp_point measure)"
    by (rule hX_modulus_measurable)

  show zero_extended_esssup_bound:
      "(let
          P = Real_Vector_Spaces.norm
            (inverse (of_real pi :: complex));
          K = P *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x)
                powr q)) powr (1 / q);
          W = slp_w1p_norm_on b X u Du;
          M = K * (192 * W);
          I = integral\<^sup>L lborel (slp_localized_cauchy_kernel 1);
          J = integral\<^sup>L lborel (slp_squared_radial_annulus 1 2);
          C = 6 * I + 2 * unit_ball_vol 2;
          N0 = P * M * C;
          B0 = 2 * M;
          DB0 = K * (2 * (4 * W));
          CB0 = ((P * slp_global_cutoff_L) * M) * C;
          C0 = N0 + (B0 + (DB0 + (CB0 + P * M * I)));
          C1 = P * M * J
        in
          esssup (lborel :: slp_point measure)
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_dbar_psi_inverse (- tau) c
                    (slp_restrict_field X u)) z)))
          \<le>
          ereal
            (inverse (sqrt tau) * ln (2 + tau) *
              (C0 / ln 2 + C1 * ((2 + log 2 R) / ln 2))))"
    unfolding Let_def
    by (rule esssup_I[OF hX_modulus_measurable hX_AE])
qed

end

end
