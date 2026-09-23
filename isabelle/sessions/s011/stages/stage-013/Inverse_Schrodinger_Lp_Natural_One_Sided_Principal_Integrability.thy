theory Inverse_Schrodinger_Lp_Natural_One_Sided_Principal_Integrability
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Amplitude_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Error_Mass"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Mixed_Principal_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Finite_Amplitude_Integrable_Lp_Root"
begin

hide_const (open) Commutative_Ring.norm

section \<open>All-natural one-sided principal-amplitude integrability\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_natural_one_sided_cauchy_terminal_density_mass_finite:
  fixes n :: nat and R C p :: real and X :: "slp_point set"
    and cutoff q Q :: slp_scalar_field
    and orientation :: slp_cauchy_orientation
  assumes R_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_lp: "aim_complex_lp_on_plane p q"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_outside: "\<And>x. x \<notin> X \<Longrightarrow> Q x = 0"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
  shows "nn_integral lborel
    (slp_positive_root_output_density (2 * R) cutoff q
      (\<lambda>s. ennreal (norm (slp_cauchy_transform orientation q s))) n Q) <
    top_class.top"
proof -
  let ?A = "slp_cauchy_transform orientation q"
  let ?T = "\<lambda>s. ennreal (norm (?A s))"
  let ?M = "slp_positive_terminal_riesz_weight (2 * R) q"
  have radius_nonnegative: "0 \<le> 2 * R"
    using R_nonnegative by simp
  have q_measurable[measurable]: "q \<in> borel_measurable lborel"
    using q_lp unfolding aim_complex_lp_on_plane_def by blast
  have Q_measurable[measurable]: "Q \<in> borel_measurable lborel"
    using Q_lp unfolding aim_complex_lp_on_plane_def by blast
  have A_measurable[measurable]: "?A \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF p_lower p_upper q_lp])
  have T_measurable[measurable]: "?T \<in> borel_measurable lborel"
    by measurable
  have M_measurable[measurable]: "?M \<in> borel_measurable lborel"
    by (rule slp_positive_terminal_riesz_weight_measurable[OF q_measurable])
  have support_radius:
    "\<And>x y::slp_point. \<lbrakk>cutoff x \<noteq> 0; q y \<noteq> 0\<rbrakk> \<Longrightarrow>
      norm (x - y) \<le> 2 * R"
    by (rule slp_norm_sub_le_two_radius[OF R_nonnegative cutoff_support q_support])
  have terminal_weight_le:
    "\<And>x. ennreal (norm (cutoff x)) * ?T x \<le>
      ennreal (norm (cutoff x)) * ?M x"
    by (rule slp_cauchy_transform_cutoff_terminal_riesz_bound[OF support_radius])
  have majorant_mass_finite:
    "nn_integral lborel
      (slp_positive_root_output_density (2 * R) cutoff q ?M n Q) <
      top_class.top"
    by (rule
      slp_positive_root_output_density_terminal_weighted_mass_finite_lp_root[OF
        radius_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative])
  have actual_mass_le:
    "nn_integral lborel
      (slp_positive_root_output_density (2 * R) cutoff q ?T n Q) \<le>
     nn_integral lborel
      (slp_positive_root_output_density (2 * R) cutoff q ?M n Q)"
    using slp_positive_root_output_density_pairing_cutoff_mono[
      where R = "2 * R" and cutoff = cutoff and potential = q
        and terminal_weight = ?T and terminal_majorant = ?M and n = n
        and root_weight = Q and test = "\<lambda>_::slp_point. 1::ennreal",
      OF cutoff_measurable q_measurable T_measurable M_measurable
        Q_measurable _ terminal_weight_le]
    by simp
  show ?thesis
    by (rule le_less_trans[OF actual_mass_le majorant_mass_finite])
qed

theorem slp_natural_one_sided_principal_density_masses_finite:
  fixes n :: nat and R C p :: real and X :: "slp_point set"
    and cutoff q Q phi :: slp_scalar_field
    and orientation :: slp_cauchy_orientation
  assumes R_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_lp: "aim_complex_lp_on_plane p q"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_outside: "\<And>x. x \<notin> X \<Longrightarrow> Q x = 0"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and phi_test: "slp_test_function_on UNIV phi"
  shows "let A = slp_cauchy_transform orientation q;
             DA = slp_positive_root_output_density (2 * R) cutoff q
               (\<lambda>s. ennreal (norm (A s))) n Q;
             D1 = slp_positive_root_output_density (2 * R) cutoff q (\<lambda>_. 1) n Q
    in nn_integral lborel (\<lambda>u. ennreal (norm (phi u)) * DA u) < top_class.top \<and>
       nn_integral lborel (\<lambda>u. ennreal (norm (phi u * A u)) * D1 u) < top_class.top"
proof -
  let ?A = "slp_cauchy_transform orientation q"
  let ?DA = "slp_positive_root_output_density (2 * R) cutoff q
    (\<lambda>s. ennreal (norm (?A s))) n Q"
  let ?D1 = "slp_positive_root_output_density (2 * R) cutoff q (\<lambda>_. 1) n Q"
  have radius_nonnegative: "0 \<le> 2 * R"
    using R_nonnegative by simp
  have q_measurable[measurable]: "q \<in> borel_measurable lborel"
    using q_lp unfolding aim_complex_lp_on_plane_def by blast
  have Q_measurable[measurable]: "Q \<in> borel_measurable lborel"
    using Q_lp unfolding aim_complex_lp_on_plane_def by blast
  have A_measurable[measurable]: "?A \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF p_lower p_upper q_lp])
  have DA_measurable: "?DA \<in> borel_measurable lborel"
    by (rule slp_positive_root_output_density_measurable[
      OF cutoff_measurable q_measurable _ Q_measurable]) measurable
  have DA_finite: "nn_integral lborel ?DA < top_class.top"
    by (rule slp_natural_one_sided_cauchy_terminal_density_mass_finite[
      OF R_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative
        cutoff_support q_support])
  have phi_bounded: "bounded (range phi)"
    by (rule slp_test_function_integrable_bounded(2)[OF phi_test])
  obtain K where phi_bound: "\<And>x. norm (phi x) \<le> K"
    using phi_bounded unfolding bounded_iff by auto
  have terminal_bound:
    "nn_integral lborel (\<lambda>u. ennreal (norm (phi u)) * ?DA u) \<le>
      nn_integral lborel (\<lambda>u. ennreal K * ?DA u)"
  proof (rule nn_integral_mono)
    fix u :: slp_point
    assume "u \<in> space (lborel :: slp_point measure)"
    show "ennreal (norm (phi u)) * ?DA u \<le> ennreal K * ?DA u"
      by (rule mult_right_mono[OF ennreal_leI[OF phi_bound]]) simp
  qed
  have terminal_constant:
    "nn_integral lborel (\<lambda>u. ennreal K * ?DA u) =
      ennreal K * nn_integral lborel ?DA"
    by (rule nn_integral_cmult[OF DA_measurable])
  have terminal_finite:
    "nn_integral lborel (\<lambda>u. ennreal (norm (phi u)) * ?DA u) < top_class.top"
    by (rule le_less_trans[OF terminal_bound])
      (use DA_finite terminal_constant in \<open>simp add: ennreal_mult_less_top\<close>)
  have D1_L2: "slp_positive_ennreal_lp_on_plane 2 ?D1"
    by (rule slp_natural_one_sided_unit_density_l2[
      OF radius_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative])
  have phiA_L2: "aim_complex_lp_on_plane 2 (\<lambda>u. phi u * ?A u)"
    by (rule slp_test_cauchy_product_l2[OF p_lower p_upper q_lp phi_test])
  have output_raw:
    "nn_integral lborel (\<lambda>u. ?D1 u * ennreal (norm (phi u * ?A u))) <
      top_class.top"
    by (rule slp_positive_ennreal_lp_complex_pairing_lt_top[
      OF _ _ _ D1_L2 phiA_L2]) simp_all
  have output_finite:
    "nn_integral lborel (\<lambda>u. ennreal (norm (phi u * ?A u)) * ?D1 u) <
      top_class.top"
    using output_raw by (simp add: mult.commute)
  show ?thesis
    unfolding Let_def using terminal_finite output_finite by blast
qed

theorem slp_natural_one_sided_principal_components_integrable:
  fixes n :: nat and R C p omega :: real and X :: "slp_point set"
    and cutoff q Q phi :: slp_scalar_field
    and orientation :: slp_cauchy_orientation
  assumes R_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_lp: "aim_complex_lp_on_plane p q"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_outside: "\<And>x. x \<notin> X \<Longrightarrow> Q x = 0"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and phi_test: "slp_test_function_on UNIV phi"
  shows "let A = slp_cauchy_transform orientation q;
             P = PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure));
             MJ = ((P \<Otimes>\<^sub>M P) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M lborel;
             ps = (\<lambda>z. map (\<lambda>k.
               (fst (fst (fst z)) k, snd (fst (fst z)) k)) [0..<n]);
             residual = (\<lambda>z. slp_left_branch_residual (ps z) (snd (fst z)))
    in integrable MJ (\<lambda>z. exp (\<i> * of_real (omega * residual z)) *
      (slp_natural_one_sided_weighted_amplitude n Q cutoff q A phi z -
       slp_natural_one_sided_weighted_amplitude n Q cutoff q (\<lambda>_. 1)
         (\<lambda>u. phi u * A u) z))"
proof -
  let ?P = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?MJ = "((?P \<Otimes>\<^sub>M ?P) \<Otimes>\<^sub>M (lborel :: slp_point measure))
    \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?A = "slp_cauchy_transform orientation q"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?phiA = "\<lambda>u. phi u * ?A u"
  let ?ps = "\<lambda>z. map (\<lambda>k.
    (fst (fst (fst z)) k, snd (fst (fst z)) k)) [0..<n]"
  let ?residual = "\<lambda>z. slp_left_branch_residual (?ps z) (snd (fst z))"
  let ?phase = "\<lambda>z. omega * ?residual z"
  let ?W = "\<lambda>T H. slp_natural_one_sided_weighted_amplitude n Q cutoff q T H"
  have q_measurable[measurable]: "q \<in> borel_measurable lborel"
    using q_lp unfolding aim_complex_lp_on_plane_def by blast
  have Q_measurable[measurable]: "Q \<in> borel_measurable lborel"
    using Q_lp unfolding aim_complex_lp_on_plane_def by blast
  have A_measurable[measurable]: "?A \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF p_lower p_upper q_lp])
  have phi_measurable[measurable]: "phi \<in> borel_measurable lborel"
    using slp_test_function_integrable_bounded(1)[OF phi_test] by measurable
  have one_measurable: "?one \<in> borel_measurable lborel"
    by measurable
  have phiA_measurable: "?phiA \<in> borel_measurable lborel"
    by measurable
  have residual_measurable[measurable]: "?residual \<in> borel_measurable ?MJ"
    by (rule slp_natural_branch_residual_param_measurable; measurable)
  have phase_measurable[measurable]: "?phase \<in> borel_measurable ?MJ"
    by measurable
  note masses = slp_natural_one_sided_principal_density_masses_finite[
    OF R_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative
      cutoff_support q_support phi_test, where n = n and orientation = orientation]
  have terminal_mass:
    "nn_integral lborel (\<lambda>u. ennreal (norm (phi u)) *
      slp_positive_root_output_density (2 * R) cutoff q
        (\<lambda>s. ennreal (norm (?A s))) n Q u) < top_class.top"
    using masses by (auto simp only: Let_def)
  have output_mass:
    "nn_integral lborel (\<lambda>u. ennreal (norm (?phiA u)) *
      slp_positive_root_output_density (2 * R) cutoff q (\<lambda>_. 1) n Q u) <
      top_class.top"
    using masses by (auto simp only: Let_def)
  have output_mass_exact:
    "nn_integral lborel (\<lambda>u. ennreal (norm (?phiA u)) *
      slp_positive_root_output_density (2 * R) cutoff q
        (\<lambda>s. ennreal (norm (?one s))) n Q u) < top_class.top"
    using output_mass by (simp only: norm_one ennreal_1)
  have terminal_integrable:
    "integrable ?MJ (\<lambda>z. exp (\<i> * of_real (?phase z)) * ?W ?A phi z)"
    by (rule slp_natural_one_sided_oscillatory_integral_bound(1)[
      OF R_nonnegative cutoff_measurable q_measurable A_measurable
        Q_measurable phi_measurable Q_support cutoff_support q_support
        phase_measurable terminal_mass])
  have output_integrable:
    "integrable ?MJ (\<lambda>z. exp (\<i> * of_real (?phase z)) * ?W ?one ?phiA z)"
    by (rule slp_natural_one_sided_oscillatory_integral_bound(1)[
      OF R_nonnegative cutoff_measurable q_measurable one_measurable
        Q_measurable phiA_measurable Q_support cutoff_support q_support
        phase_measurable output_mass_exact])
  have bracket_integrable:
    "integrable ?MJ (\<lambda>z. exp (\<i> * of_real (?phase z)) *
      (?W ?A phi z - ?W ?one ?phiA z))"
    using Bochner_Integration.integrable_diff[OF terminal_integrable output_integrable]
    by (simp only: right_diff_distrib)
  show ?thesis
    unfolding Let_def using bracket_integrable by simp
qed

end

end
