theory Inverse_Schrodinger_Lp_Natural_One_Sided_Root_Integration
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Preaverage_Integration"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Natural one-sided graph and root integration\<close>

theorem slp_natural_one_sided_preaverage_graph_factor:
  fixes n :: nat and tau :: real and y :: slp_point
    and Q cutoff q T :: slp_scalar_field
  shows "let ps = (\<lambda>z. map (\<lambda>k. (fst (fst (fst z)) k,
               snd (fst (fst z)) k)) [0..<n]);
             s = (\<lambda>z. snd (fst z));
             output = (\<lambda>z. slp_left_branch_output (ps z) (s z));
             phase = (\<lambda>z. slp_left_branch_residual (ps z) (s z));
             a = slp_natural_one_sided_weighted_amplitude n Q cutoff q
               (\<lambda>_. 1) (\<lambda>_. 1)
    in exp (\<i> * of_real (tau * phase z)) * a z *
         slp_center_kernel tau (output z) y * T (s z) =
       Q (snd z) *
         slp_left_branch_oscillatory_graph_kernel_natural n tau y cutoff q T
           (snd z) (fst z)"
proof -
  let ?ps = "\<lambda>z. map (\<lambda>k.
    (fst (fst (fst z)) k, snd (fst (fst z)) k)) [0..<n]"
  let ?s = "\<lambda>z. snd (fst z)"
  let ?output = "\<lambda>z. slp_left_branch_output (?ps z) (?s z)"
  let ?phase = "\<lambda>z. slp_left_branch_residual (?ps z) (?s z)"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?a = "slp_natural_one_sided_weighted_amplitude n Q cutoff q ?one ?one"
  let ?w = "slp_natural_one_sided_weighted_amplitude n Q cutoff q T ?one"
  let ?f = "\<lambda>z. exp (\<i> * of_real (tau * ?phase z)) * ?a z *
    slp_center_kernel tau (?output z) y * T (?s z)"
  let ?L = "\<lambda>x. slp_left_branch_oscillatory_graph_kernel_natural
    n tau y cutoff q T x"
  have guarded_pairs:
    "map (\<lambda>j. (slp_left_branch_natural_value k pos j,
        slp_left_branch_natural_value k neg j)) [0..<k] =
      map (\<lambda>j. (pos j, neg j)) [0..<k]" for k pos neg
    by (rule map_cong) (auto simp: slp_left_branch_natural_value_def)
  have left_graph:
    "?L (snd z) (fst z) =
      exp (\<i> * of_real (tau * slp_left_branch_phase y (?ps z) (?s z))) *
      slp_left_branch_complex_kernel_list cutoff q T
        (?ps z) (snd z) (?s z)" for z
    unfolding slp_left_branch_oscillatory_graph_kernel_natural_def
      slp_left_branch_oscillatory_graph_kernel_def
    by (simp only: guarded_pairs)
  have phase_identity:
    "?phase z + slp_center_phase (?output z) y =
      slp_left_branch_phase y (?ps z) (?s z)" for z
    using slp_left_branch_phase_split[of y "?ps z" "?s z"]
    by (simp add: slp_center_phase_symmetric add.commute)
  have phase_factor:
    "exp (\<i> * of_real (tau * ?phase z)) *
      slp_center_kernel tau (?output z) y =
      exp (\<i> * of_real (tau * slp_left_branch_phase y (?ps z) (?s z)))"
    for z
  proof -
    have args:
      "(\<i>::complex) * of_real (tau * ?phase z) +
        \<i> * of_real (tau * slp_center_phase (?output z) y) =
      \<i> * of_real (tau * slp_left_branch_phase y (?ps z) (?s z))"
    proof -
      have "(\<i>::complex) *
          of_real (tau * (?phase z + slp_center_phase (?output z) y)) =
        \<i> * of_real
          (tau * slp_left_branch_phase y (?ps z) (?s z))"
        by (simp only: phase_identity)
      then show ?thesis by (simp add: algebra_simps)
    qed
    show ?thesis unfolding slp_center_kernel_def
      by (simp only: exp_add[symmetric] args)
  qed
  have weighted: "?w z = ?a z * T (?s z)" for z
    using slp_natural_one_sided_amplitude_terminal_factor[
      where n=n and Q=Q and cutoff=cutoff and q=q and T=T and H="?one" and z=z]
    by (simp only: Let_def mult_1_right)
  have factor: "?f z = Q (snd z) * ?L (snd z) (fst z)" for z
  proof -
    let ?K = "slp_left_branch_complex_kernel_list cutoff q T
      (?ps z) (snd z) (?s z)"
    have amplitude: "?w z = Q (snd z) * ?K"
      by (simp add: slp_natural_one_sided_weighted_amplitude_def Let_def)
    have "?f z =
      (exp (\<i> * of_real (tau * ?phase z)) *
        slp_center_kernel tau (?output z) y) * ?w z"
      by (simp only: weighted mult_ac)
    also have "\<dots> =
      exp (\<i> * of_real (tau * slp_left_branch_phase y (?ps z) (?s z))) *
        (Q (snd z) * ?K)"
      by (simp only: phase_factor amplitude)
    also have "\<dots> = Q (snd z) * ?L (snd z) (fst z)"
      by (simp only: left_graph mult_ac)
    finally show ?thesis .
  qed
  show ?thesis unfolding Let_def by (rule factor)
qed

context aim_planar_riesz_hls_cauchy
begin

theorem slp_natural_one_sided_preaverage_root_integral:
  fixes n :: nat and R C p :: real and X :: "slp_point set"
    and tau :: real and y :: slp_point
    and cutoff q Q :: slp_scalar_field
    and orientation :: slp_cauchy_orientation
  assumes R_nonnegative: "0 \<le> R"
    and p_lower: "1 < p" and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel" and X_bounded: "bounded X"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_lp: "aim_complex_lp_on_plane p q"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_outside: "\<And>x. x \<notin> X \<Longrightarrow> Q x = 0"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
  shows "let P = PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure));
             MJ = ((P \<Otimes>\<^sub>M P) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M lborel;
             ps = (\<lambda>z. map (\<lambda>k. (fst (fst (fst z)) k,
               snd (fst (fst z)) k)) [0..<n]);
             s = (\<lambda>z. snd (fst z));
             output = (\<lambda>z. slp_left_branch_output (ps z) (s z));
             phase = (\<lambda>z. slp_left_branch_residual (ps z) (s z));
             A = slp_cauchy_transform orientation q;
             a = slp_natural_one_sided_weighted_amplitude n Q cutoff q
               (\<lambda>_. 1) (\<lambda>_. 1);
             F = (\<lambda>z. exp (\<i> * of_real (tau * phase z)) * a z *
               slp_center_kernel tau (output z) y * (A (s z) - A y));
             r = (\<lambda>x. Q x *
               slp_left_neumann_iterate n tau y cutoff q orientation x)
    in integrable MJ F \<and> integrable lborel r \<and>
       integral\<^sup>L MJ F = integral\<^sup>L lborel r"
proof -
  let ?P = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?B = "(?P \<Otimes>\<^sub>M ?P) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "?B \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?ps = "\<lambda>z. map (\<lambda>k.
    (fst (fst (fst z)) k, snd (fst (fst z)) k)) [0..<n]"
  let ?s = "\<lambda>z. snd (fst z)"
  let ?output = "\<lambda>z. slp_left_branch_output (?ps z) (?s z)"
  let ?phase = "\<lambda>z. slp_left_branch_residual (?ps z) (?s z)"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?A = "slp_cauchy_transform orientation q"
  let ?a = "slp_natural_one_sided_weighted_amplitude n Q cutoff q ?one ?one"
  let ?e = "\<lambda>z. exp (\<i> * of_real (tau * ?phase z))"
  let ?F = "\<lambda>z. ?e z * ?a z * slp_center_kernel tau (?output z) y *
    (?A (?s z) - ?A y)"
  let ?L = "\<lambda>x. slp_left_branch_oscillatory_graph_kernel_natural
    n tau y cutoff q (\<lambda>u. ?A u - ?A y) x"
  let ?r = "\<lambda>x. Q x *
    slp_left_neumann_iterate n tau y cutoff q orientation x"
  have F_integrable: "integrable ?MJ ?F"
    using slp_natural_one_sided_fixed_preaverage_integrable[
      OF R_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative
        Q_support cutoff_support q_support,
      where n=n and orientation=orientation and tau=tau and y=y]
    by (auto simp only: Let_def)
  interpret natural_product: product_sigma_finite
    "(\<lambda>_::nat. (lborel :: slp_point measure))" by standard
  interpret family: sigma_finite_measure ?P
    by (rule natural_product.sigma_finite) simp
  interpret arrays: pair_sigma_finite ?P ?P ..
  interpret array_measure: sigma_finite_measure "(?P \<Otimes>\<^sub>M ?P)" by standard
  interpret coordinates: pair_sigma_finite
    "(?P \<Otimes>\<^sub>M ?P)" "(lborel :: slp_point measure)" ..
  interpret branch_measure: sigma_finite_measure ?B by standard
  interpret joint: pair_sigma_finite ?B "(lborel :: slp_point measure)" ..
  have integrand_factor: "?F z = Q (snd z) * ?L (snd z) (fst z)" for z
    using slp_natural_one_sided_preaverage_graph_factor[
      where n=n and Q=Q and cutoff=cutoff and q=q
        and T="\<lambda>u. ?A u - ?A y" and tau=tau and y=y and z=z]
    by (simp only: Let_def)
  have root_factor: "?F (c,x) = Q x * ?L x c" for c x
    using integrand_factor[of "(c,x)"] by (simp only: fst_conv snd_conv)
  have root_section: "integral\<^sup>L ?B (\<lambda>c. ?F (c,x)) = ?r x" for x
  proof (cases "Q x = 0")
    case True
    show ?thesis by (simp only: root_factor; simp add: True)
  next
    case False
    have origin_bound: "norm x \<le> R" by (rule Q_support[OF False])
    have graph_L1: "integrable ?B (?L x)"
      by (rule slp_left_branch_oscillatory_graph_kernel_natural_primitive_diff_integrable[
        OF R_nonnegative origin_bound cutoff_support q_support p_lower p_upper
          cutoff_measurable q_lp cutoff_bound C_nonnegative])
    have graph_value:
      "integral\<^sup>L ?B (?L x) =
        slp_left_neumann_iterate n tau y cutoff q orientation x"
      by (rule slp_left_branch_oscillatory_graph_kernel_natural_integral_eq_neumann_iterate[
        OF R_nonnegative origin_bound cutoff_support q_support p_lower p_upper
          cutoff_measurable q_lp cutoff_bound C_nonnegative])
    show ?thesis
      by (simp only: root_factor; simp only: mult.assoc
        Bochner_Integration.integral_mult_right_zero graph_value)
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

end

end
