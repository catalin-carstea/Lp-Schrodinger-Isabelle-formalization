theory Inverse_Schrodinger_Lp_Natural_Mixed_Born_Identity
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Mixed_Preaverage_Integration"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The original natural mixed Born functional\<close>

theorem slp_natural_mixed_preaverage_graph_factor:
  fixes n m :: nat and tau :: real and y :: slp_point
    and Q cutoff q qt T U :: slp_scalar_field
  shows "let lp = (\<lambda>c. map (\<lambda>j. (fst (fst (fst c)) j, snd (fst (fst c)) j)) [0..<n]);
             rp = (\<lambda>c. map (\<lambda>j. (fst (fst (snd c)) j, snd (fst (snd c)) j)) [0..<m]);
             center = slp_mixed_branch_center (snd z)
               (lp (fst z)) (snd (fst (fst z))) (rp (fst z)) (snd (snd (fst z)));
             phase = slp_mixed_branch_residual (snd z)
               (lp (fst z)) (snd (fst (fst z))) (rp (fst z)) (snd (snd (fst z)));
             a = slp_natural_mixed_weighted_amplitude n m Q cutoff q (\<lambda>_. 1)
               qt (\<lambda>_. 1) (\<lambda>_. 1)
    in exp (\<i> * of_real (tau * phase)) * a z * slp_center_kernel tau center y *
         T (snd (fst (fst z))) * U (snd (snd (fst z))) =
       Q (snd z) * slp_center_kernel (-tau) y (snd z) *
         slp_left_branch_oscillatory_graph_kernel_natural n tau y cutoff q T
           (snd z) (fst (fst z)) *
         slp_right_branch_oscillatory_graph_kernel_natural m tau y cutoff qt U
           (snd z) (snd (fst z))"
proof -
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
  let ?w = "slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U ?one"
  let ?f = "\<lambda>z. exp (\<i> * of_real (tau * ?phase z)) * ?a z *
    slp_center_kernel tau (?center z) y * T (?s z) * U (?t z)"
  let ?L = "\<lambda>x. slp_left_branch_oscillatory_graph_kernel_natural n tau y cutoff q T x"
  let ?R = "\<lambda>x. slp_right_branch_oscillatory_graph_kernel_natural m tau y cutoff qt U x"
  have guarded_pairs:
    "map (\<lambda>j. (slp_left_branch_natural_value k pos j,
        slp_left_branch_natural_value k neg j)) [0..<k] =
      map (\<lambda>j. (pos j, neg j)) [0..<k]" for k pos neg
    by (rule map_cong) (auto simp: slp_left_branch_natural_value_def)
  have left_graph:
    "?L (snd z) (fst (fst z)) =
      exp (\<i> * of_real (tau * slp_left_branch_phase y (?lp (fst z)) (?s z))) *
      slp_left_branch_complex_kernel_list cutoff q T
        (?lp (fst z)) (snd z) (?s z)" for z
    unfolding slp_left_branch_oscillatory_graph_kernel_natural_def
      slp_left_branch_oscillatory_graph_kernel_def
    by (simp only: guarded_pairs)
  have right_graph:
    "?R (snd z) (snd (fst z)) =
      exp (\<i> * of_real (tau * slp_right_branch_phase y (?rp (fst z)) (?t z))) *
      cnj (slp_left_branch_complex_kernel_list (\<lambda>x. cnj (cutoff x))
        (\<lambda>x. cnj (qt x)) (\<lambda>x. cnj (U x)) (?rp (fst z)) (snd z) (?t z))" for z
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
  have weighted: "?w z = ?a z * T (?s z) * U (?t z)" for z
    using slp_natural_mixed_amplitude_terminal_factor[
      where n=n and m=m and Q=Q and cutoff=cutoff and q=q and qt=qt
        and T=T and U=U and H="?one" and z=z]
    by (simp only: Let_def mult_1_right)
  have factor:
    "?f z = Q (snd z) * slp_center_kernel (-tau) y (snd z) *
      ?L (snd z) (fst (fst z)) * ?R (snd z) (snd (fst z))" for z
  proof -
    let ?KL = "slp_left_branch_complex_kernel_list cutoff q T
      (?lp (fst z)) (snd z) (?s z)"
    let ?KR = "cnj (slp_left_branch_complex_kernel_list (\<lambda>x. cnj (cutoff x))
      (\<lambda>x. cnj (qt x)) (\<lambda>x. cnj (U x)) (?rp (fst z)) (snd z) (?t z))"
    have amplitude: "?w z = Q (snd z) * ?KL * ?KR"
      by (simp add: slp_natural_mixed_weighted_amplitude_def Let_def)
    have "?f z =
      (exp (\<i> * of_real (tau * ?phase z)) * slp_center_kernel tau (?center z) y) *
        ?w z"
      by (simp only: weighted mult_ac)
    also have "\<dots> =
      (slp_center_kernel (-tau) y (snd z) *
        exp (\<i> * of_real (tau * slp_left_branch_phase y (?lp (fst z)) (?s z))) *
        exp (\<i> * of_real (tau * slp_right_branch_phase y (?rp (fst z)) (?t z)))) *
        (Q (snd z) * ?KL * ?KR)"
      by (simp only: phase_factor amplitude)
    also have "\<dots> = Q (snd z) * slp_center_kernel (-tau) y (snd z) *
      ?L (snd z) (fst (fst z)) * ?R (snd z) (snd (fst z))"
      by (simp only: left_graph right_graph mult_ac)
    finally show ?thesis .
  qed
  show ?thesis unfolding Let_def by (rule factor)
qed

context aim_planar_riesz_hls_cauchy
begin

theorem slp_natural_mixed_preaverage_root_integral:
  fixes n m :: nat and R C p :: real and X :: "slp_point set"
    and tau :: real and y :: slp_point
    and cutoff q qt Q :: slp_scalar_field and lo ro :: slp_cauchy_orientation
  assumes R_nonnegative: "0 \<le> R"
    and C_nonnegative: "0 \<le> C"
    and p_lower: "1 < p" and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel" and X_bounded: "bounded X"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_outside: "\<And>x. x \<notin> X \<Longrightarrow> Q x = 0"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
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
             A = slp_cauchy_transform lo q;
             B = slp_cauchy_transform ro qt;
             a = slp_natural_mixed_weighted_amplitude n m Q cutoff q (\<lambda>_. 1)
               qt (\<lambda>_. 1) (\<lambda>_. 1);
             F = (\<lambda>z. exp (\<i> * of_real (tau * phase z)) * a z *
               slp_center_kernel tau (center z) y *
               (A (snd (fst (fst z))) - A y) * (B (snd (snd (fst z))) - B y));
             r = (\<lambda>x. Q x * slp_center_kernel (-tau) y x *
               slp_left_neumann_iterate n tau y cutoff q lo x *
               slp_right_neumann_iterate m tau y cutoff qt ro x)
    in integrable MJ F \<and> integrable lborel r \<and>
       integral\<^sup>L MJ F = integral\<^sup>L lborel r"
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
  let ?A = "slp_cauchy_transform lo q"
  let ?B = "slp_cauchy_transform ro qt"
  let ?W = "\<lambda>T U H. slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U H"
  let ?a = "?W ?one ?one ?one"
  let ?e = "\<lambda>z. exp (\<i> * of_real (tau * ?phase z))"
  let ?F = "\<lambda>z. ?e z * ?a z * slp_center_kernel tau (?center z) y *
    (?A (?s z) - ?A y) * (?B (?t z) - ?B y)"
  let ?L = "\<lambda>x. slp_left_branch_oscillatory_graph_kernel_natural n tau y cutoff q
    (\<lambda>u. ?A u - ?A y) x"
  let ?R = "\<lambda>x. slp_right_branch_oscillatory_graph_kernel_natural m tau y cutoff qt
    (\<lambda>u. ?B u - ?B y) x"
  let ?r = "\<lambda>x. Q x * slp_center_kernel (-tau) y x *
    slp_left_neumann_iterate n tau y cutoff q lo x *
    slp_right_neumann_iterate m tau y cutoff qt ro x"
  have F_integrable: "integrable ?MJ ?F"
    using slp_natural_mixed_fixed_preaverage_integrable[
      OF R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound Q_support
        cutoff_support q_support qt_support,
      where n=n and m=m and lo=lo and ro=ro and tau=tau and y=y]
    by (auto simp only: Let_def)
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
  have integrand_factor:
    "?F z = Q (snd z) * slp_center_kernel (-tau) y (snd z) *
      ?L (snd z) (fst (fst z)) * ?R (snd z) (snd (fst z))" for z
    using slp_natural_mixed_preaverage_graph_factor[
      where n=n and m=m and Q=Q and cutoff=cutoff and q=q and qt=qt
        and T="\<lambda>u. ?A u - ?A y" and U="\<lambda>u. ?B u - ?B y"
        and tau=tau and y=y and z=z]
    by (simp only: Let_def)
  have root_factor:
    "?F (c,x) = Q x * slp_center_kernel (-tau) y x *
      ?L x (fst c) * ?R x (snd c)" for c x
    using integrand_factor[of "(c,x)"] by (simp only: fst_conv snd_conv)
  have root_section: "integral\<^sup>L ?N (\<lambda>c. ?F (c,x)) = ?r x" for x
  proof (cases "Q x = 0")
    case True
    show ?thesis by (simp only: root_factor; simp add: True)
  next
    case False
    have origin_bound: "norm x \<le> R" by (rule Q_support[OF False])
    have left_L1: "integrable ?BL (?L x)"
      by (rule slp_left_branch_oscillatory_graph_kernel_natural_primitive_diff_integrable[
        OF R_nonnegative origin_bound cutoff_support q_support p_lower p_upper
          cutoff_measurable q_lp cutoff_bound C_nonnegative])
    have right_L1: "integrable ?BR (?R x)"
      by (rule slp_right_branch_oscillatory_graph_kernel_natural_primitive_diff_integrable[
        OF R_nonnegative origin_bound cutoff_support qt_support p_lower p_upper
          cutoff_measurable qt_lp cutoff_bound C_nonnegative])
    have left_value:
      "integral\<^sup>L ?BL (?L x) = slp_left_neumann_iterate n tau y cutoff q lo x"
      by (rule slp_left_branch_oscillatory_graph_kernel_natural_integral_eq_neumann_iterate[
        OF R_nonnegative origin_bound cutoff_support q_support p_lower p_upper
          cutoff_measurable q_lp cutoff_bound C_nonnegative])
    have right_value:
      "integral\<^sup>L ?BR (?R x) = slp_right_neumann_iterate m tau y cutoff qt ro x"
      by (rule slp_right_natural_graph_integral_eq_neumann[
        OF R_nonnegative origin_bound cutoff_support qt_support p_lower p_upper
          cutoff_measurable qt_lp cutoff_bound C_nonnegative])
    show ?thesis
      by (simp only: root_factor; simp only: mult.assoc
        Bochner_Integration.integral_mult_right_zero
        product_integral[OF left_L1 right_L1] left_value right_value)
  qed
  have curried_L1: "integrable ?MJ (case_prod (\<lambda>c x. ?F (c,x)))"
    using F_integrable by (simp add: case_prod_unfold)
  have r_integrable: "integrable lborel ?r"
    using joint.integrable_snd[OF curried_L1] by (simp only: root_section)
  have exact: "integral\<^sup>L ?MJ ?F = integral\<^sup>L lborel ?r"
    using joint.integral_snd[OF curried_L1]
    by (simp only: root_section; simp add: case_prod_unfold)
  show ?thesis unfolding Let_def using F_integrable r_integrable exact by blast
qed

theorem slp_natural_mixed_born_bracket_identity:
  fixes n m :: nat and R C p :: real and X :: "slp_point set"
    and tau :: real and phi :: slp_scalar_field
    and cutoff q qt Q :: slp_scalar_field and lo ro :: slp_cauchy_orientation
  assumes R_nonnegative: "0 \<le> R"
    and C_nonnegative: "0 \<le> C"
    and p_lower: "1 < p" and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel" and X_bounded: "bounded X"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_outside: "\<And>x. x \<notin> X \<Longrightarrow> Q x = 0"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and phi_test: "slp_test_function_on UNIV phi"
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
             A = slp_cauchy_transform lo q;
             B = slp_cauchy_transform ro qt;
             a = slp_natural_mixed_weighted_amplitude n m Q cutoff q (\<lambda>_. 1)
               qt (\<lambda>_. 1) (\<lambda>_. 1);
             I = (\<lambda>z. exp (\<i> * of_real (tau * phase z)) * a z *
               slp_mixed_center_average_bracket tau phi A B (center z)
                 (snd (fst (fst z))) (snd (snd (fst z))));
             r = (\<lambda>y x. Q x * slp_center_kernel (-tau) y x *
               slp_left_neumann_iterate n tau y cutoff q lo x *
               slp_right_neumann_iterate m tau y cutoff qt ro x)
    in (\<forall>y. integrable lborel (r y)) \<and>
       integrable lborel (\<lambda>y. phi y * integral\<^sup>L lborel (r y)) \<and>
       integrable MJ I \<and>
       slp_mixed_born_functional n m tau phi Q cutoff q qt lo ro = integral\<^sup>L MJ I"
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
  let ?A = "slp_cauchy_transform lo q"
  let ?B = "slp_cauchy_transform ro qt"
  let ?W = "\<lambda>T U H. slp_natural_mixed_weighted_amplitude n m Q cutoff q T qt U H"
  let ?a = "?W ?one ?one ?one"
  let ?e = "\<lambda>z. exp (\<i> * of_real (tau * ?phase z))"
  let ?F = "\<lambda>z y. ?e z * ?a z * slp_center_kernel tau (?center z) y *
    (?A (?s z) - ?A y) * (?B (?t z) - ?B y)"
  let ?G = "\<lambda>z y. ?F z y * phi y"
  let ?I = "\<lambda>z. ?e z * ?a z *
    slp_mixed_center_average_bracket tau phi ?A ?B (?center z) (?s z) (?t z)"
  let ?r = "\<lambda>y x. Q x * slp_center_kernel (-tau) y x *
    slp_left_neumann_iterate n tau y cutoff q lo x *
    slp_right_neumann_iterate m tau y cutoff qt ro x"
  let ?scale = "of_real (tau / pi) :: complex"
  note bracket = slp_natural_mixed_preaverage_bracket_fubini[
    OF R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound Q_support
      cutoff_support q_support qt_support phi_test,
    where n=n and m=m and lo=lo and ro=ro and tau=tau]
  have I_integrable: "integrable ?MJ ?I"
    using bracket by (auto simp only: Let_def)
  have outer_integrable: "integrable lborel (\<lambda>y. integral\<^sup>L ?MJ (\<lambda>z. ?G z y))"
    using bracket by (auto simp only: Let_def)
  have preaverage: "?scale * integral\<^sup>L lborel
      (\<lambda>y. integral\<^sup>L ?MJ (\<lambda>z. ?G z y)) = integral\<^sup>L ?MJ ?I"
    using bracket by (auto simp only: Let_def)
  have root_data:
    "integrable lborel (?r y) \<and>
      integral\<^sup>L ?MJ (\<lambda>z. ?F z y) = integral\<^sup>L lborel (?r y)" for y
    using slp_natural_mixed_preaverage_root_integral[
      OF R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound Q_support
        cutoff_support q_support qt_support,
      where n=n and m=m and lo=lo and ro=ro and tau=tau and y=y]
    by (auto simp only: Let_def)
  have root_integrable: "integrable lborel (?r y)" for y
    using root_data[of y] by (rule conjunct1)
  have root_value:
    "integral\<^sup>L ?MJ (\<lambda>z. ?F z y) = integral\<^sup>L lborel (?r y)" for y
    using root_data[of y] by (rule conjunct2)
  have original_inner:
    "integral\<^sup>L ?MJ (\<lambda>z. ?G z y) = phi y * integral\<^sup>L lborel (?r y)" for y
    by (simp only: Bochner_Integration.integral_mult_left_zero root_value;
        simp only: mult.commute)
  have original_integrable:
    "integrable lborel (\<lambda>y. phi y * integral\<^sup>L lborel (?r y))"
    using outer_integrable by (simp only: original_inner)
  have normalization:
    "(of_real tau :: complex) * inverse (of_real pi) = of_real (tau / pi)"
    by (simp add: divide_inverse)
  have exact:
    "slp_mixed_born_functional n m tau phi Q cutoff q qt lo ro = integral\<^sup>L ?MJ ?I"
    using preaverage unfolding slp_mixed_born_functional_def
    by (simp only: original_inner normalization)
  show ?thesis unfolding Let_def
    using root_integrable original_integrable I_integrable exact by blast
qed

end

end
