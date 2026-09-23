theory Inverse_Schrodinger_Lp_Natural_Mixed_Unit_Transpose
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Mixed_Principal_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Mixed_Center_Density_Unweighted_Mass_Finite"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Right_Graph_Natural_Recursive_Branch_Identity"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The natural unit mixed transpose\<close>

context aim_planar_riesz_hls
begin

theorem slp_natural_mixed_unit_integration_data:
  fixes n m :: nat and R C p :: real
    and cutoff q qt Q :: slp_scalar_field
  assumes R_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and Q_integrable: "integrable lborel Q"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
  shows "let PL = PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure));
             PR = PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure));
             MJ = ((((PL \<Otimes>\<^sub>M PL) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M
               ((PR \<Otimes>\<^sub>M PR) \<Otimes>\<^sub>M lborel)) \<Otimes>\<^sub>M lborel);
             lp = (\<lambda>c. map (\<lambda>j. (fst (fst (fst c)) j, snd (fst (fst c)) j)) [0..<n]);
             rp = (\<lambda>c. map (\<lambda>j. (fst (fst (snd c)) j, snd (fst (snd c)) j)) [0..<m]);
             center = (\<lambda>z. slp_mixed_branch_center (snd z)
               (lp (fst z)) (snd (fst (fst z))) (rp (fst z)) (snd (snd (fst z))));
             phase = (\<lambda>z. slp_mixed_branch_residual (snd z)
               (lp (fst z)) (snd (fst (fst z))) (rp (fst z)) (snd (snd (fst z))));
             a = slp_natural_mixed_weighted_amplitude n m Q cutoff q (\<lambda>_. 1)
               qt (\<lambda>_. 1) (\<lambda>_. 1)
    in center \<in> measurable MJ lborel \<and>
       phase \<in> borel_measurable MJ \<and> integrable MJ a"
proof -
  let ?PL = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?PR = "PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?BL = "(?PL \<Otimes>\<^sub>M ?PL) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?BR = "(?PR \<Otimes>\<^sub>M ?PR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "(?BL \<Otimes>\<^sub>M ?BR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?lp = "\<lambda>c. map (\<lambda>j. (fst (fst (fst c)) j, snd (fst (fst c)) j)) [0..<n]"
  let ?rp = "\<lambda>c. map (\<lambda>j. (fst (fst (snd c)) j, snd (fst (snd c)) j)) [0..<m]"
  let ?s = "\<lambda>z. snd (fst (fst z))"
  let ?t = "\<lambda>z. snd (snd (fst z))"
  let ?u = "\<lambda>z. slp_left_branch_output (?lp (fst z)) (?s z)"
  let ?v = "\<lambda>z. slp_right_branch_output (?rp (fst z)) (?t z)"
  let ?center = "\<lambda>z. slp_mixed_branch_center (snd z)
    (?lp (fst z)) (?s z) (?rp (fst z)) (?t z)"
  let ?phase = "\<lambda>z. slp_mixed_branch_residual (snd z)
    (?lp (fst z)) (?s z) (?rp (fst z)) (?t z)"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?a = "slp_natural_mixed_weighted_amplitude n m Q cutoff q ?one qt ?one ?one"
  have left_output_map: "?u \<in> measurable ?MJ lborel"
    by (rule slp_natural_branch_output_param_measurable; measurable)
  have left_output_borel[measurable]: "?u \<in> borel_measurable ?MJ"
    using left_output_map by (simp only: measurable_lborel1)
  have right_output_map:
    "(\<lambda>z. slp_left_branch_output (?rp (fst z)) (?t z)) \<in> measurable ?MJ lborel"
    by (rule slp_natural_branch_output_param_measurable; measurable)
  have right_output_borel[measurable]: "?v \<in> borel_measurable ?MJ"
    using right_output_map
    by (simp only: measurable_lborel1 slp_left_branch_output_eq_right)
  have center_borel: "?center \<in> borel_measurable ?MJ"
    unfolding slp_mixed_branch_center_def by measurable
  have center_map: "?center \<in> measurable ?MJ lborel"
    using center_borel by (simp only: measurable_lborel1)
  have left_residual_borel[measurable]:
    "(\<lambda>z. slp_left_branch_residual (?lp (fst z)) (?s z)) \<in> borel_measurable ?MJ"
    by (rule slp_natural_branch_residual_param_measurable; measurable)
  have right_left_residual_borel:
    "(\<lambda>z. slp_left_branch_residual (?rp (fst z)) (?t z)) \<in> borel_measurable ?MJ"
    by (rule slp_natural_branch_residual_param_measurable; measurable)
  have right_residual_borel[measurable]:
    "(\<lambda>z. slp_right_branch_residual (?rp (fst z)) (?t z)) \<in> borel_measurable ?MJ"
    using right_left_residual_borel
    by (simp only: slp_left_branch_residual_def slp_right_branch_residual_def)
  have quadratic_compose:
    "(\<lambda>z. slp_point_quadratic_value (f z)) \<in> borel_measurable ?MJ"
    if f_borel: "f \<in> borel_measurable ?MJ" for f
  proof -
    have nth[measurable]: "(\<lambda>z. f z $ i) \<in> borel_measurable ?MJ" for i :: 2
      using measurable_comp[OF f_borel borel_measurable_nth[of i]]
      by (simp only: comp_def)
    show ?thesis unfolding slp_point_quadratic_value_def by measurable
  qed
  have root_quadratic[measurable]:
    "(\<lambda>z. slp_point_quadratic_value (snd z)) \<in> borel_measurable ?MJ"
    by (rule quadratic_compose; measurable)
  have left_quadratic[measurable]:
    "(\<lambda>z. slp_point_quadratic_value (?u z)) \<in> borel_measurable ?MJ"
    by (rule quadratic_compose; measurable)
  have right_quadratic[measurable]:
    "(\<lambda>z. slp_point_quadratic_value (?v z)) \<in> borel_measurable ?MJ"
    by (rule quadratic_compose; measurable)
  have center_quadratic[measurable]:
    "(\<lambda>z. slp_point_quadratic_value (-snd z + ?u z + ?v z)) \<in> borel_measurable ?MJ"
    by (rule quadratic_compose; measurable)
  have phase_borel: "?phase \<in> borel_measurable ?MJ"
    unfolding slp_mixed_branch_residual_def slp_mixed_core_residual_def by measurable
  have q_measurable: "q \<in> borel_measurable lborel"
    using q_lp unfolding aim_complex_lp_on_plane_def by blast
  have qt_measurable: "qt \<in> borel_measurable lborel"
    using qt_lp unfolding aim_complex_lp_on_plane_def by blast
  have Q_measurable: "Q \<in> borel_measurable lborel"
    using Q_integrable by measurable
  have one_measurable: "?one \<in> borel_measurable lborel" by measurable
  have radius_nonnegative: "0 \<le> 2 * R" using R_nonnegative by simp
  have mass:
    "nn_integral lborel (slp_mixed_center_density (2 * R) cutoff q qt
      (\<lambda>_. 1) (\<lambda>_. 1) n m Q) < top_class.top"
    by (rule slp_mixed_center_density_unweighted_mass_finite[
          OF radius_nonnegative p_lower p_upper cutoff_measurable q_lp qt_lp
            cutoff_bound C_nonnegative Q_integrable])
  have amplitude_integrable: "integrable ?MJ ?a"
    by (rule slp_natural_mixed_weighted_amplitude_integrable_from_density[
          OF R_nonnegative cutoff_measurable q_measurable one_measurable
            qt_measurable one_measurable Q_measurable one_measurable
            Q_support cutoff_support q_support qt_support])
      (use mass in \<open>auto\<close>)
  show ?thesis unfolding Let_def using center_map phase_borel amplitude_integrable by blast
qed

theorem slp_natural_mixed_unit_root_integral:
  fixes n m :: nat and R C p tau :: real and y :: slp_point
    and cutoff q qt Q :: slp_scalar_field
  assumes R_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and Q_integrable: "integrable lborel Q"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
  shows "let PL = PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure));
             PR = PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure));
             MJ = ((((PL \<Otimes>\<^sub>M PL) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M
               ((PR \<Otimes>\<^sub>M PR) \<Otimes>\<^sub>M lborel)) \<Otimes>\<^sub>M lborel);
             lp = (\<lambda>c. map (\<lambda>j. (fst (fst (fst c)) j, snd (fst (fst c)) j)) [0..<n]);
             rp = (\<lambda>c. map (\<lambda>j. (fst (fst (snd c)) j, snd (fst (snd c)) j)) [0..<m]);
             center = (\<lambda>z. slp_mixed_branch_center (snd z)
               (lp (fst z)) (snd (fst (fst z))) (rp (fst z)) (snd (snd (fst z))));
             phase = (\<lambda>z. slp_mixed_branch_residual (snd z)
               (lp (fst z)) (snd (fst (fst z))) (rp (fst z)) (snd (snd (fst z))));
             a = slp_natural_mixed_weighted_amplitude n m Q cutoff q (\<lambda>_. 1)
               qt (\<lambda>_. 1) (\<lambda>_. 1);
             f = (\<lambda>z. exp (\<i> * of_real (tau * phase z)) * a z *
               slp_center_kernel tau (center z) y);
             r = (\<lambda>x. Q x * slp_center_kernel (-tau) y x *
               slp_left_recursive_branch n tau y cutoff q (\<lambda>_. 1) x *
               slp_right_recursive_branch m tau y cutoff qt (\<lambda>_. 1) x)
    in integrable MJ f \<and> integrable lborel r \<and>
       integral\<^sup>L MJ f = integral\<^sup>L lborel r"
proof -
  let ?PL = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?PR = "PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?BL = "(?PL \<Otimes>\<^sub>M ?PL) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?BR = "(?PR \<Otimes>\<^sub>M ?PR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?N = "?BL \<Otimes>\<^sub>M ?BR"
  let ?MJ = "?N \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?lp = "\<lambda>c. map (\<lambda>j. (fst (fst (fst c)) j, snd (fst (fst c)) j)) [0..<n]"
  let ?rp = "\<lambda>c. map (\<lambda>j. (fst (fst (snd c)) j, snd (fst (snd c)) j)) [0..<m]"
  let ?s = "\<lambda>z. snd (fst (fst z))"
  let ?t = "\<lambda>z. snd (snd (fst z))"
  let ?center = "\<lambda>z. slp_mixed_branch_center (snd z)
    (?lp (fst z)) (?s z) (?rp (fst z)) (?t z)"
  let ?phase = "\<lambda>z. slp_mixed_branch_residual (snd z)
    (?lp (fst z)) (?s z) (?rp (fst z)) (?t z)"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?a = "slp_natural_mixed_weighted_amplitude n m Q cutoff q ?one qt ?one ?one"
  let ?f = "\<lambda>z. exp (\<i> * of_real (tau * ?phase z)) * ?a z *
    slp_center_kernel tau (?center z) y"
  let ?L = "\<lambda>x. slp_left_branch_oscillatory_graph_kernel_natural n tau y cutoff q ?one x"
  let ?R = "\<lambda>x. slp_right_branch_oscillatory_graph_kernel_natural m tau y cutoff qt ?one x"
  let ?r = "\<lambda>x. Q x * slp_center_kernel (-tau) y x *
    slp_left_recursive_branch n tau y cutoff q ?one x *
    slp_right_recursive_branch m tau y cutoff qt ?one x"
  note data = slp_natural_mixed_unit_integration_data[
    OF R_nonnegative p_lower p_upper cutoff_measurable q_lp qt_lp cutoff_bound
      C_nonnegative Q_integrable Q_support cutoff_support q_support qt_support,
    where n=n and m=m]
  have center_map: "?center \<in> measurable ?MJ lborel"
    using data by (auto simp only: Let_def)
  have phase_borel[measurable]: "?phase \<in> borel_measurable ?MJ"
    using data by (auto simp only: Let_def)
  have a_integrable: "integrable ?MJ ?a"
    using data by (auto simp only: Let_def)
  have a_borel[measurable]: "?a \<in> borel_measurable ?MJ"
    using a_integrable by measurable
  have kernel_borel[measurable]:
    "(\<lambda>z. slp_center_kernel tau (?center z) y) \<in> borel_measurable ?MJ"
    using measurable_compose[OF center_map slp_center_kernel_measurable[of tau y]]
    by (simp only: slp_center_kernel_symmetric)
  have f_integrable: "integrable ?MJ ?f"
  proof (rule Bochner_Integration.integrable_bound[OF a_integrable])
    show "?f \<in> borel_measurable ?MJ" by measurable
    show "AE z in ?MJ. norm (?f z) \<le> norm (?a z)"
      by (simp add: norm_mult norm_exp_i_times)
  qed
  interpret natural_product: product_sigma_finite
    "(\<lambda>_::nat. (lborel :: slp_point measure))" by standard
  interpret left_family: sigma_finite_measure ?PL
    by (rule natural_product.sigma_finite) simp
  interpret right_family: sigma_finite_measure ?PR
    by (rule natural_product.sigma_finite) simp
  interpret left_arrays: pair_sigma_finite ?PL ?PL ..
  interpret right_arrays: pair_sigma_finite ?PR ?PR ..
  interpret left_array_measure: sigma_finite_measure "(?PL \<Otimes>\<^sub>M ?PL)" by standard
  interpret right_array_measure: sigma_finite_measure "(?PR \<Otimes>\<^sub>M ?PR)" by standard
  interpret left_coordinates: pair_sigma_finite
    "(?PL \<Otimes>\<^sub>M ?PL)" "(lborel :: slp_point measure)" ..
  interpret right_coordinates: pair_sigma_finite
    "(?PR \<Otimes>\<^sub>M ?PR)" "(lborel :: slp_point measure)" ..
  interpret left_measure: sigma_finite_measure ?BL by standard
  interpret right_measure: sigma_finite_measure ?BR by standard
  interpret branches: pair_sigma_finite ?BL ?BR ..
  interpret branch_measure: sigma_finite_measure ?N by standard
  interpret joint: pair_sigma_finite ?N "(lborel :: slp_point measure)" ..
  have product_integral:
    "integral\<^sup>L ?N (\<lambda>c. lf (fst c) * rf (snd c)) =
      integral\<^sup>L ?BL lf * integral\<^sup>L ?BR rf"
    if lf_integrable: "integrable ?BL lf" and rf_integrable: "integrable ?BR rf"
    for lf rf :: "(((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point)) \<times> slp_point)
      \<Rightarrow> complex"
  proof -
    have lf_borel[measurable]: "lf \<in> borel_measurable ?BL"
      using lf_integrable by measurable
    have rf_borel[measurable]: "rf \<in> borel_measurable ?BR"
      using rf_integrable by measurable
    have product_borel: "(\<lambda>c. lf (fst c) * rf (snd c)) \<in> borel_measurable ?N"
      by measurable
    have outer_norm:
      "integrable ?BL (\<lambda>l. integral\<^sup>L ?BR (\<lambda>r. norm (lf l * rf r)))"
      by (simp only: norm_mult Bochner_Integration.integral_mult_right_zero;
          intro Bochner_Integration.integrable_mult_left
            Bochner_Integration.integrable_norm lf_integrable)
    have sections: "AE l in ?BL. integrable ?BR (\<lambda>r. lf l * rf r)"
      by (intro AE_I2 Bochner_Integration.integrable_mult_right rf_integrable)
    have product_L1: "integrable ?N (\<lambda>c. lf (fst c) * rf (snd c))"
      by (rule branches.Fubini_integrable[OF product_borel])
        (simp_all only: fst_conv snd_conv outer_norm sections)
    show ?thesis
      using branches.integral_fst'[OF product_L1, symmetric]
      by (simp only: fst_conv snd_conv Bochner_Integration.integral_mult_right_zero
          Bochner_Integration.integral_mult_left_zero)
  qed
  have guarded_pairs:
    "map (\<lambda>j. (slp_left_branch_natural_value k pos j,
        slp_left_branch_natural_value k neg j)) [0..<k] =
      map (\<lambda>j. (pos j, neg j)) [0..<k]" for k pos neg
    by (rule map_cong) (auto simp: slp_left_branch_natural_value_def)
  have left_graph:
    "?L (snd z) (fst (fst z)) =
      exp (\<i> * of_real (tau * slp_left_branch_phase y (?lp (fst z)) (?s z))) *
      slp_left_branch_complex_kernel_list cutoff q ?one
        (?lp (fst z)) (snd z) (?s z)" for z
    unfolding slp_left_branch_oscillatory_graph_kernel_natural_def
      slp_left_branch_oscillatory_graph_kernel_def
    by (simp only: guarded_pairs)
  have right_graph:
    "?R (snd z) (snd (fst z)) =
      exp (\<i> * of_real (tau * slp_right_branch_phase y (?rp (fst z)) (?t z))) *
      cnj (slp_left_branch_complex_kernel_list (\<lambda>x. cnj (cutoff x))
        (\<lambda>x. cnj (qt x)) ?one (?rp (fst z)) (snd z) (?t z))" for z
    unfolding slp_right_branch_oscillatory_graph_kernel_natural_def
      slp_left_branch_oscillatory_graph_kernel_natural_def
      slp_left_branch_oscillatory_graph_kernel_def
    by (simp add: guarded_pairs exp_cnj slp_left_branch_phase_def
        slp_right_branch_phase_def)
  have phase_identity:
    "?phase z + slp_center_phase (?center z) y =
      - slp_center_phase y (snd z) +
      slp_left_branch_phase y (?lp (fst z)) (?s z) +
      slp_right_branch_phase y (?rp (fst z)) (?t z)" for z
    using slp_mixed_branch_phase_split[of y "snd z"
      "?lp (fst z)" "?s z" "?rp (fst z)" "?t z"]
    by (simp add: slp_mixed_branch_phase_def slp_center_phase_symmetric add.commute)
  have phase_factor:
    "exp (\<i> * of_real (tau * ?phase z)) * slp_center_kernel tau (?center z) y =
      slp_center_kernel (-tau) y (snd z) *
      exp (\<i> * of_real (tau * slp_left_branch_phase y (?lp (fst z)) (?s z))) *
      exp (\<i> * of_real (tau * slp_right_branch_phase y (?rp (fst z)) (?t z)))" for z
  proof -
    have args:
      "(\<i>::complex) * of_real (tau * ?phase z) +
        \<i> * of_real (tau * slp_center_phase (?center z) y) =
      (\<i> * of_real ((-tau) * slp_center_phase y (snd z)) +
        \<i> * of_real (tau * slp_left_branch_phase y (?lp (fst z)) (?s z))) +
        \<i> * of_real (tau * slp_right_branch_phase y (?rp (fst z)) (?t z))"
    proof -
      have "(\<i>::complex) * of_real (tau * (?phase z + slp_center_phase (?center z) y)) =
        \<i> * of_real (tau * (- slp_center_phase y (snd z) +
          slp_left_branch_phase y (?lp (fst z)) (?s z) +
          slp_right_branch_phase y (?rp (fst z)) (?t z)))"
        by (simp only: phase_identity)
      then show ?thesis by (simp add: algebra_simps)
    qed
    show ?thesis unfolding slp_center_kernel_def
      by (simp only: exp_add[symmetric] args)
  qed
  have integrand_factor:
    "?f z = Q (snd z) * slp_center_kernel (-tau) y (snd z) *
      ?L (snd z) (fst (fst z)) * ?R (snd z) (snd (fst z))" for z
  proof -
    let ?KL = "slp_left_branch_complex_kernel_list cutoff q ?one
      (?lp (fst z)) (snd z) (?s z)"
    let ?KR = "cnj (slp_left_branch_complex_kernel_list (\<lambda>x. cnj (cutoff x))
      (\<lambda>x. cnj (qt x)) ?one (?rp (fst z)) (snd z) (?t z))"
    have amplitude:
      "?a z = Q (snd z) *
        slp_left_branch_complex_kernel_list cutoff q ?one
          (?lp (fst z)) (snd z) (?s z) *
        cnj (slp_left_branch_complex_kernel_list (\<lambda>x. cnj (cutoff x))
          (\<lambda>x. cnj (qt x)) ?one (?rp (fst z)) (snd z) (?t z))"
      by (simp add: slp_natural_mixed_weighted_amplitude_def Let_def)
    have "?f z =
      (exp (\<i> * of_real (tau * ?phase z)) * slp_center_kernel tau (?center z) y) *
      (Q (snd z) * ?KL * ?KR)"
      by (simp only: amplitude mult_ac)
    also have "\<dots> =
      (slp_center_kernel (-tau) y (snd z) *
        exp (\<i> * of_real (tau * slp_left_branch_phase y (?lp (fst z)) (?s z))) *
        exp (\<i> * of_real (tau * slp_right_branch_phase y (?rp (fst z)) (?t z)))) *
      (Q (snd z) * ?KL * ?KR)"
      by (simp only: phase_factor)
    also have "\<dots> = Q (snd z) * slp_center_kernel (-tau) y (snd z) *
      ?L (snd z) (fst (fst z)) * ?R (snd z) (snd (fst z))"
      by (simp only: left_graph right_graph mult_ac)
    finally show ?thesis .
  qed
  have cutoff_cnj_measurable: "(\<lambda>x. cnj (cutoff x)) \<in> borel_measurable lborel"
  proof -
    have cnj_borel: "cnj \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI[OF continuous_on_cnj[OF continuous_on_id]])
    show ?thesis using measurable_comp[OF cutoff_measurable cnj_borel]
      by (simp only: comp_def)
  qed
  have qt_cnj_lp: "aim_complex_lp_on_plane p (\<lambda>x. cnj (qt x))"
    using qt_lp by simp
  have cutoff_cnj_support: "\<And>x. cnj (cutoff x) \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    by (rule cutoff_support) simp
  have qt_cnj_support: "\<And>x. cnj (qt x) \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    by (rule qt_support) simp
  have cutoff_cnj_bound: "\<And>x. norm (cnj (cutoff x)) \<le> C"
    using cutoff_bound by simp
  have root_factor:
    "?f (c,x) = Q x * slp_center_kernel (-tau) y x *
      ?L x (fst c) * ?R x (snd c)" for c x
    using integrand_factor[of "(c,x)"] by (simp only: fst_conv snd_conv)
  have root_section:
    "integral\<^sup>L ?N (\<lambda>c. ?f (c,x)) = ?r x" for x
  proof (cases "Q x = 0")
    case True
    show ?thesis by (simp only: root_factor; simp add: True)
  next
    case False
    have origin_bound: "norm x \<le> R" by (rule Q_support[OF False])
    have left_L1: "integrable ?BL (?L x)"
      by (rule slp_left_branch_oscillatory_graph_kernel_natural_integrable_hls[
            OF R_nonnegative origin_bound cutoff_support q_support p_lower p_upper
              cutoff_measurable q_lp cutoff_bound C_nonnegative]) auto
    have right_cnj_L1:
      "integrable ?BR (slp_left_branch_oscillatory_graph_kernel_natural m (-tau) y
        (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (qt x)) ?one x)"
      by (rule slp_left_branch_oscillatory_graph_kernel_natural_integrable_hls[
            OF R_nonnegative origin_bound cutoff_cnj_support qt_cnj_support p_lower p_upper
              cutoff_cnj_measurable qt_cnj_lp cutoff_cnj_bound C_nonnegative]) auto
    have right_L1: "integrable ?BR (?R x)"
      using right_cnj_L1
      by (simp only: slp_right_branch_oscillatory_graph_kernel_natural_integrable_iff complex_cnj_one)
    have left_value:
      "integral\<^sup>L ?BL (?L x) = slp_left_recursive_branch n tau y cutoff q ?one x"
      by (rule slp_left_branch_oscillatory_graph_kernel_natural_integral_eq_recursive_hls[
            OF R_nonnegative origin_bound cutoff_support q_support p_lower p_upper
              cutoff_measurable q_lp cutoff_bound C_nonnegative]) auto
    have right_value:
      "integral\<^sup>L ?BR (?R x) = slp_right_recursive_branch m tau y cutoff qt ?one x"
      by (rule slp_right_branch_oscillatory_graph_kernel_natural_integral_eq_recursive_hls[
            OF R_nonnegative origin_bound cutoff_support qt_support p_lower p_upper
              cutoff_measurable qt_lp cutoff_bound C_nonnegative]) auto
    show ?thesis
      by (simp only: root_factor; simp only: mult.assoc
          Bochner_Integration.integral_mult_right_zero
          product_integral[OF left_L1 right_L1] left_value right_value)
  qed
  have curried_L1: "integrable ?MJ (case_prod (\<lambda>c x. ?f (c,x)))"
    using f_integrable by (simp add: case_prod_unfold)
  have r_integrable: "integrable lborel ?r"
    using joint.integrable_snd[OF curried_L1] by (simp only: root_section)
  have exact: "integral\<^sup>L ?MJ ?f = integral\<^sup>L lborel ?r"
    using joint.integral_snd[OF curried_L1]
    by (simp only: root_section; simp add: case_prod_unfold)
  show ?thesis unfolding Let_def using f_integrable r_integrable exact by blast
qed

theorem slp_natural_mixed_unit_average_transpose:
  fixes n m :: nat and R C p tau :: real
    and cutoff q qt Q h :: slp_scalar_field
  assumes R_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and Q_integrable: "integrable lborel Q"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and h_integrable: "integrable lborel h"
  shows "let PL = PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure));
             PR = PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure));
             MJ = ((((PL \<Otimes>\<^sub>M PL) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M
               ((PR \<Otimes>\<^sub>M PR) \<Otimes>\<^sub>M lborel)) \<Otimes>\<^sub>M lborel);
             lp = (\<lambda>c. map (\<lambda>j. (fst (fst (fst c)) j, snd (fst (fst c)) j)) [0..<n]);
             rp = (\<lambda>c. map (\<lambda>j. (fst (fst (snd c)) j, snd (fst (snd c)) j)) [0..<m]);
             center = (\<lambda>z. slp_mixed_branch_center (snd z)
               (lp (fst z)) (snd (fst (fst z))) (rp (fst z)) (snd (snd (fst z))));
             phase = (\<lambda>z. slp_mixed_branch_residual (snd z)
               (lp (fst z)) (snd (fst (fst z))) (rp (fst z)) (snd (snd (fst z))));
             a = slp_natural_mixed_weighted_amplitude n m Q cutoff q (\<lambda>_. 1)
               qt (\<lambda>_. 1) (\<lambda>_. 1);
             left = (\<lambda>z. exp (\<i> * of_real (tau * phase z)) * a z *
               slp_center_average tau h (center z));
             right = (\<lambda>y. h y * (of_real (tau / pi) *
               integral\<^sup>L lborel (\<lambda>x. Q x * slp_center_kernel (-tau) y x *
                 slp_left_recursive_branch n tau y cutoff q (\<lambda>_. 1) x *
                 slp_right_recursive_branch m tau y cutoff qt (\<lambda>_. 1) x)))
    in integrable MJ left \<and> integrable lborel right \<and>
       integral\<^sup>L MJ left = integral\<^sup>L lborel right"
proof -
  let ?PL = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?PR = "PiM {..<m} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?BL = "(?PL \<Otimes>\<^sub>M ?PL) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?BR = "(?PR \<Otimes>\<^sub>M ?PR) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?N = "?BL \<Otimes>\<^sub>M ?BR"
  let ?MJ = "?N \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MY = "?MJ \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?lp = "\<lambda>c. map (\<lambda>j. (fst (fst (fst c)) j, snd (fst (fst c)) j)) [0..<n]"
  let ?rp = "\<lambda>c. map (\<lambda>j. (fst (fst (snd c)) j, snd (fst (snd c)) j)) [0..<m]"
  let ?s = "\<lambda>z. snd (fst (fst z))"
  let ?t = "\<lambda>z. snd (snd (fst z))"
  let ?center = "\<lambda>z. slp_mixed_branch_center (snd z)
    (?lp (fst z)) (?s z) (?rp (fst z)) (?t z)"
  let ?phase = "\<lambda>z. slp_mixed_branch_residual (snd z)
    (?lp (fst z)) (?s z) (?rp (fst z)) (?t z)"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?a = "slp_natural_mixed_weighted_amplitude n m Q cutoff q ?one qt ?one ?one"
  let ?scale = "of_real (tau / pi) :: complex"
  let ?F = "\<lambda>z. exp (\<i> * of_real (tau * ?phase z)) * ?a z"
  let ?G = "\<lambda>z y. ?F z * slp_center_kernel tau (?center z) y * h y"
  let ?r = "\<lambda>y x. Q x * slp_center_kernel (-tau) y x *
    slp_left_recursive_branch n tau y cutoff q ?one x *
    slp_right_recursive_branch m tau y cutoff qt ?one x"
  let ?left = "\<lambda>z. ?F z * slp_center_average tau h (?center z)"
  let ?right = "\<lambda>y. h y * (?scale * integral\<^sup>L lborel (?r y))"
  note data = slp_natural_mixed_unit_integration_data[
    OF R_nonnegative p_lower p_upper cutoff_measurable q_lp qt_lp cutoff_bound
      C_nonnegative Q_integrable Q_support cutoff_support q_support qt_support,
    where n=n and m=m]
  have center_map: "?center \<in> measurable ?MJ lborel"
    using data by (auto simp only: Let_def)
  have center_borel[measurable]: "?center \<in> borel_measurable ?MJ"
    using center_map by (simp only: measurable_lborel1)
  have phase_borel[measurable]: "?phase \<in> borel_measurable ?MJ"
    using data by (auto simp only: Let_def)
  have a_integrable: "integrable ?MJ ?a"
    using data by (auto simp only: Let_def)
  have a_borel[measurable]: "?a \<in> borel_measurable ?MJ"
    using a_integrable by measurable
  have h_borel[measurable]: "h \<in> borel_measurable lborel"
    using h_integrable by measurable
  have center_lift: "(\<lambda>zy. ?center (fst zy)) \<in> borel_measurable ?MY"
    by measurable
  have target_lift: "snd \<in> borel_measurable ?MY" by measurable
  have center_nth[measurable]:
    "(\<lambda>zy. ?center (fst zy) $ i) \<in> borel_measurable ?MY" for i :: 2
    using measurable_comp[OF center_lift borel_measurable_nth[of i]]
    by (simp only: comp_def)
  have target_nth[measurable]:
    "(\<lambda>zy. snd zy $ i) \<in> borel_measurable ?MY" for i :: 2
    using measurable_comp[OF target_lift borel_measurable_nth[of i]]
    by (simp only: comp_def)
  have kernel_joint_borel[measurable]:
    "(\<lambda>zy. slp_center_kernel tau (?center (fst zy)) (snd zy)) \<in> borel_measurable ?MY"
    unfolding slp_center_kernel_def slp_center_phase_def by measurable
  have G_borel: "case_prod ?G \<in> borel_measurable ?MY"
    unfolding case_prod_unfold by measurable
  have G_norm: "norm (?G z y) = norm (?a z) * norm (h y)" for z y
    by (simp add: norm_mult norm_exp_i_times)
  have outer_norm:
    "integrable ?MJ (\<lambda>z. integral\<^sup>L lborel (\<lambda>y. norm (?G z y)))"
    by (simp only: G_norm Bochner_Integration.integral_mult_right_zero;
        intro Bochner_Integration.integrable_mult_left
          Bochner_Integration.integrable_norm a_integrable)
  have section_L1: "integrable lborel (?G z)" for z
    by (simp only: mult.assoc;
        intro Bochner_Integration.integrable_mult_right
          slp_center_kernel_integrable_mult h_integrable)
  have sections: "AE z in ?MJ. integrable lborel (?G z)"
    by (intro AE_I2 section_L1)
  interpret natural_product: product_sigma_finite
    "(\<lambda>_::nat. (lborel :: slp_point measure))" by standard
  interpret left_family: sigma_finite_measure ?PL
    by (rule natural_product.sigma_finite) simp
  interpret right_family: sigma_finite_measure ?PR
    by (rule natural_product.sigma_finite) simp
  interpret left_arrays: pair_sigma_finite ?PL ?PL ..
  interpret right_arrays: pair_sigma_finite ?PR ?PR ..
  interpret left_array_measure: sigma_finite_measure "(?PL \<Otimes>\<^sub>M ?PL)" by standard
  interpret right_array_measure: sigma_finite_measure "(?PR \<Otimes>\<^sub>M ?PR)" by standard
  interpret left_coordinates: pair_sigma_finite
    "(?PL \<Otimes>\<^sub>M ?PL)" "(lborel :: slp_point measure)" ..
  interpret right_coordinates: pair_sigma_finite
    "(?PR \<Otimes>\<^sub>M ?PR)" "(lborel :: slp_point measure)" ..
  interpret left_measure: sigma_finite_measure ?BL by standard
  interpret right_measure: sigma_finite_measure ?BR by standard
  interpret branches: pair_sigma_finite ?BL ?BR ..
  interpret branch_measure: sigma_finite_measure ?N by standard
  interpret joint: pair_sigma_finite ?N "(lborel :: slp_point measure)" ..
  interpret joint_measure: sigma_finite_measure ?MJ by standard
  interpret averaging: pair_sigma_finite ?MJ "(lborel :: slp_point measure)" ..
  have G_integrable: "integrable ?MY (case_prod ?G)"
    by (rule averaging.Fubini_integrable[OF G_borel])
      (simp_all only: case_prod_conv outer_norm sections)
  have left_identity: "?left z = ?scale * integral\<^sup>L lborel (?G z)" for z
    unfolding slp_center_average_def
    by (simp only: mult.assoc Bochner_Integration.integral_mult_right_zero;
        simp only: mult_ac)
  have root_value:
    "integral\<^sup>L ?MJ (\<lambda>z. ?F z * slp_center_kernel tau (?center z) y) =
      integral\<^sup>L lborel (?r y)" for y
    using slp_natural_mixed_unit_root_integral[
      OF R_nonnegative p_lower p_upper cutoff_measurable q_lp qt_lp cutoff_bound
        C_nonnegative Q_integrable Q_support cutoff_support q_support qt_support,
      where n=n and m=m and tau=tau and y=y]
    by (auto simp only: Let_def)
  have right_identity:
    "?right y = ?scale * integral\<^sup>L ?MJ (\<lambda>z. ?G z y)" for y
    by (simp only: Bochner_Integration.integral_mult_left_zero root_value;
        simp only: mult_ac)
  have left_integrable: "integrable ?MJ ?left"
    unfolding left_identity
    by (intro Bochner_Integration.integrable_mult_right averaging.integrable_fst[OF G_integrable])
  have right_integrable: "integrable lborel ?right"
    unfolding right_identity
    by (intro Bochner_Integration.integrable_mult_right averaging.integrable_snd[OF G_integrable])
  have exact: "integral\<^sup>L ?MJ ?left = integral\<^sup>L lborel ?right"
    using averaging.Fubini_integral[OF G_integrable]
    by (simp only: left_identity right_identity Bochner_Integration.integral_mult_right_zero)
  show ?thesis unfolding Let_def using left_integrable right_integrable exact by blast
qed

end

end
