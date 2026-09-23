theory Inverse_Schrodinger_Lp_Positive_Convolution_Mixed_Pointwise
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Output_Density_All_Order_Unit_Terminal_Companion_Lp"
begin

section \<open>Pointwise mixed-exponent convolution envelope\<close>

lemma slp_lborel_integrable_reflect_translate:
  fixes f :: "slp_point \<Rightarrow> real"
  assumes f_measurable: "f \<in> borel_measurable lborel"
    and f_integrable: "integrable lborel f"
  shows reflected_integrable: "integrable lborel (\<lambda>x. f (origin - x))"
    and reflected_integral:
      "integral\<^sup>L lborel (\<lambda>x. f (origin - x)) =
        integral\<^sup>L lborel f"
proof -
  let ?T = "\<lambda>x :: slp_point. origin + (-1 :: real) *\<^sub>R x"
  have T_eq: "?T = (-) origin"
    by (rule ext) simp
  have T_measurable: "?T \<in> measurable lborel borel"
    by measurable
  have distr_eq:
      "distr lborel borel ?T = (lborel :: slp_point measure)"
  proof -
    have density_identity:
        "(lborel :: slp_point measure) =
          density (distr lborel borel ?T)
            (\<lambda>_. abs (-1 :: real) ^ DIM(slp_point))"
      by (rule lborel_affine) simp
    have density_one:
        "density (distr lborel borel ?T) (\<lambda>_. 1) =
          distr lborel borel ?T"
      by (rule density_1)
    show ?thesis
      using density_identity density_one by simp
  qed
  have f_borel_measurable: "f \<in> borel_measurable borel"
    using f_measurable by simp
  have integrable_equivalence:
      "integrable (distr lborel borel ?T) f =
        integrable lborel (f \<circ> ?T)"
    using integrable_distr_eq[OF T_measurable f_borel_measurable]
    by (simp add: comp_def)
  show "integrable lborel (\<lambda>x. f (origin - x))"
    using f_integrable integrable_equivalence distr_eq T_eq
    by (simp add: comp_def)
  have integral_transport:
      "integral\<^sup>L (distr lborel borel ?T) f =
        integral\<^sup>L lborel (f \<circ> ?T)"
    using integral_distr[OF T_measurable f_borel_measurable]
    by (simp add: comp_def)
  show "integral\<^sup>L lborel (\<lambda>x. f (origin - x)) =
      integral\<^sup>L lborel f"
    using integral_transport distr_eq T_eq by (simp add: comp_def)
qed

lemma slp_positive_convolution_mixed_pointwise_square_bound:
  fixes a b q r :: real
    and f g :: "slp_point \<Rightarrow> real"
  assumes a_lower: "1 < a"
    and a_upper: "a < 2"
    and b_lower: "1 < b"
    and b_upper: "b < 2"
    and q_lower: "1 < q"
    and r_lower: "1 < r"
    and split_conjugate: "1 / q + 1 / r = 1"
    and q_scale: "(2 - a) * q = a"
    and r_scale: "(2 - b) * r = b"
    and f_measurable[measurable]: "f \<in> borel_measurable lborel"
    and g_measurable[measurable]: "g \<in> borel_measurable lborel"
    and f_nonnegative: "\<And>x. 0 \<le> f x"
    and g_nonnegative: "\<And>x. 0 \<le> g x"
    and f_power_integrable:
      "integrable lborel (\<lambda>x. f x powr a)"
    and g_power_integrable:
      "integrable lborel (\<lambda>x. g x powr b)"
  shows
    "(\<integral>\<^sup>+ root. ennreal (f root * g (output - root))
        \<partial>lborel) ^ 2 \<le>
      (\<integral>\<^sup>+ root.
        ennreal (f root powr a * g (output - root) powr b)
        \<partial>lborel) *
      ennreal
        (integral\<^sup>L lborel (\<lambda>x. f x powr a) / q +
          integral\<^sup>L lborel (\<lambda>x. g x powr b) / r)"
proof -
  let ?A = "\<lambda>root.
    ennreal (f root powr (a / 2) * g (output - root) powr (b / 2))"
  let ?B = "\<lambda>root.
    ennreal (f root powr ((2 - a) / 2) *
      g (output - root) powr ((2 - b) / 2))"
  let ?U = "\<lambda>root.
    ennreal (f root powr a * g (output - root) powr b)"
  let ?V = "\<lambda>root.
    ennreal (f root powr (2 - a) * g (output - root) powr (2 - b))"
  let ?majorant = "\<lambda>root.
    f root powr a / q + g (output - root) powr b / r"
  have A_measurable: "?A \<in> borel_measurable lborel"
    by measurable
  have B_measurable: "?B \<in> borel_measurable lborel"
    by measurable
  have U_measurable: "?U \<in> borel_measurable lborel"
    by measurable
  have V_measurable: "?V \<in> borel_measurable lborel"
    by measurable
  have split_product:
      "?A root * ?B root = ennreal (f root * g (output - root))"
    for root
  proof -
    have f_split: "a / 2 + (2 - a) / 2 = 1"
      by (simp add: add_divide_distrib [symmetric])
    have g_split: "b / 2 + (2 - b) / 2 = 1"
      by (simp add: add_divide_distrib [symmetric])
    have real_split:
        "(f root powr (a / 2) * g (output - root) powr (b / 2)) *
          (f root powr ((2 - a) / 2) *
            g (output - root) powr ((2 - b) / 2)) =
          f root * g (output - root)"
      using f_nonnegative[of root] g_nonnegative[of "output - root"]
      by (simp add: algebra_simps powr_add [symmetric] f_split g_split)
    have A_nonnegative:
        "0 \<le> f root powr (a / 2) *
          g (output - root) powr (b / 2)"
      by simp
    have B_nonnegative:
        "0 \<le> f root powr ((2 - a) / 2) *
          g (output - root) powr ((2 - b) / 2)"
      by simp
    have combined:
        "?A root * ?B root =
          ennreal
            ((f root powr (a / 2) *
                g (output - root) powr (b / 2)) *
              (f root powr ((2 - a) / 2) *
                g (output - root) powr ((2 - b) / 2)))"
      by (rule ennreal_mult [symmetric])
        (use A_nonnegative B_nonnegative in simp_all)
    show ?thesis
      using combined real_split by simp
  qed
  have A_square: "?A root ^ 2 = ?U root" for root
  proof -
    have f_half:
        "(f root powr (a / 2)) ^ 2 = f root powr a"
      by (simp add: power2_eq_square powr_add [symmetric])
    have g_half:
        "(g (output - root) powr (b / 2)) ^ 2 =
          g (output - root) powr b"
      by (simp add: power2_eq_square powr_add [symmetric])
    have real_square:
        "(f root powr (a / 2) * g (output - root) powr (b / 2)) ^ 2 =
          f root powr a * g (output - root) powr b"
      by (simp add: power_mult_distrib f_half g_half)
    have base_nonnegative:
        "0 \<le> f root powr (a / 2) * g (output - root) powr (b / 2)"
      by simp
    have converted:
        "?A root ^ 2 =
          ennreal
            ((f root powr (a / 2) *
              g (output - root) powr (b / 2)) ^ 2)"
      by (rule ennreal_power[OF base_nonnegative])
    show ?thesis
      using converted real_square by simp
  qed
  have B_square: "?B root ^ 2 = ?V root" for root
  proof -
    have f_half:
        "(f root powr ((2 - a) / 2)) ^ 2 = f root powr (2 - a)"
      by (simp add: power2_eq_square powr_add [symmetric])
    have g_half:
        "(g (output - root) powr ((2 - b) / 2)) ^ 2 =
          g (output - root) powr (2 - b)"
      by (simp add: power2_eq_square powr_add [symmetric])
    have real_square:
        "(f root powr ((2 - a) / 2) *
            g (output - root) powr ((2 - b) / 2)) ^ 2 =
          f root powr (2 - a) * g (output - root) powr (2 - b)"
      by (simp add: power_mult_distrib f_half g_half)
    have base_nonnegative:
        "0 \<le> f root powr ((2 - a) / 2) *
          g (output - root) powr ((2 - b) / 2)"
      by simp
    have converted:
        "?B root ^ 2 =
          ennreal
            ((f root powr ((2 - a) / 2) *
              g (output - root) powr ((2 - b) / 2)) ^ 2)"
      by (rule ennreal_power[OF base_nonnegative])
    show ?thesis
      using converted real_square by simp
  qed
  have cauchy:
      "(\<integral>\<^sup>+ root. ennreal (f root * g (output - root))
          \<partial>lborel) ^ 2 \<le>
        (\<integral>\<^sup>+ root. ?U root \<partial>lborel) *
        (\<integral>\<^sup>+ root. ?V root \<partial>lborel)"
  proof -
    have raw:
        "(\<integral>\<^sup>+ root. ?A root * ?B root \<partial>lborel) ^ 2 \<le>
          (\<integral>\<^sup>+ root. ?A root ^ 2 \<partial>lborel) *
          (\<integral>\<^sup>+ root. ?B root ^ 2 \<partial>lborel)"
      by (rule Cauchy_Schwarz_nn_integral[OF A_measurable B_measurable])
    show ?thesis
      using raw by (simp only: split_product A_square B_square)
  qed
  have q_positive: "0 < q" and r_positive: "0 < r"
    using q_lower r_lower by linarith+
  have q_nonzero: "q \<noteq> 0" and r_nonzero: "r \<noteq> 0"
    using q_positive r_positive by simp_all
  have g_reflected_integrable:
      "integrable lborel (\<lambda>root. g (output - root) powr b)"
    by (rule slp_lborel_integrable_reflect_translate(1)[OF _
          g_power_integrable]) measurable
  have g_reflected_integral:
      "integral\<^sup>L lborel (\<lambda>root. g (output - root) powr b) =
        integral\<^sup>L lborel (\<lambda>x. g x powr b)"
    by (rule slp_lborel_integrable_reflect_translate(2)[OF _
          g_power_integrable]) measurable
  have majorant_integrable: "integrable lborel ?majorant"
    using f_power_integrable g_reflected_integrable q_nonzero r_nonzero by simp
  have majorant_nonnegative: "0 \<le> ?majorant root" for root
    using q_positive r_positive by simp
  have young: "?V root \<le> ennreal (?majorant root)" for root
  proof -
    have raw:
        "f root powr (2 - a) * g (output - root) powr (2 - b) \<le>
          (f root powr (2 - a)) powr q / q +
          (g (output - root) powr (2 - b)) powr r / r"
      by (rule Youngs_inequality[OF q_lower r_lower split_conjugate]) simp_all
    have normalized:
        "(f root powr (2 - a)) powr q / q +
            (g (output - root) powr (2 - b)) powr r / r =
          ?majorant root"
      using q_scale r_scale by (simp add: powr_powr)
    have real_bound:
        "f root powr (2 - a) * g (output - root) powr (2 - b) \<le>
          ?majorant root"
      using raw normalized by simp
    show ?thesis
      by (rule ennreal_leI[OF real_bound])
  qed
  have V_bound:
      "(\<integral>\<^sup>+ root. ?V root \<partial>lborel) \<le>
        ennreal
          (integral\<^sup>L lborel (\<lambda>x. f x powr a) / q +
            integral\<^sup>L lborel (\<lambda>x. g x powr b) / r)"
  proof -
    have mono:
        "(\<integral>\<^sup>+ root. ?V root \<partial>lborel) \<le>
          (\<integral>\<^sup>+ root. ennreal (?majorant root) \<partial>lborel)"
      by (rule nn_integral_mono) (rule young)
    have majorant_nn:
        "(\<integral>\<^sup>+ root. ennreal (?majorant root) \<partial>lborel) =
          ennreal (integral\<^sup>L lborel ?majorant)"
      by (rule nn_integral_eq_integral[OF majorant_integrable])
        (rule AE_I2, rule majorant_nonnegative)
    have majorant_integral:
        "integral\<^sup>L lborel ?majorant =
          integral\<^sup>L lborel (\<lambda>x. f x powr a) / q +
          integral\<^sup>L lborel (\<lambda>x. g x powr b) / r"
      using f_power_integrable g_reflected_integrable q_nonzero r_nonzero
        g_reflected_integral by simp
    show ?thesis
      using mono majorant_nn majorant_integral by simp
  qed
  have U_nonnegative:
      "0 \<le> (\<integral>\<^sup>+ root. ?U root \<partial>lborel)"
    by simp
  have scaled_V:
      "(\<integral>\<^sup>+ root. ?U root \<partial>lborel) *
          (\<integral>\<^sup>+ root. ?V root \<partial>lborel) \<le>
        (\<integral>\<^sup>+ root. ?U root \<partial>lborel) *
          ennreal
            (integral\<^sup>L lborel (\<lambda>x. f x powr a) / q +
              integral\<^sup>L lborel (\<lambda>x. g x powr b) / r)"
    by (rule mult_left_mono[OF V_bound U_nonnegative])
  show ?thesis
    using cauchy scaled_V by (rule order_trans)
qed

end
