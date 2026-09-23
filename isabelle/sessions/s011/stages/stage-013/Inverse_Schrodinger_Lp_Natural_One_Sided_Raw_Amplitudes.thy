theory Inverse_Schrodinger_Lp_Natural_One_Sided_Raw_Amplitudes
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Smooth_Error_Decay"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Raw natural one-sided amplitudes\<close>

theorem slp_natural_one_sided_amplitude_terminal_factor:
  fixes n :: nat and Q cutoff q T H :: slp_scalar_field
  shows "slp_natural_one_sided_weighted_amplitude n Q cutoff q T H z =
    (let ps = map (\<lambda>k. (fst (fst (fst z)) k,
                            snd (fst (fst z)) k)) [0..<n];
         s = snd (fst z);
         output = slp_left_branch_output ps s
     in slp_natural_one_sided_weighted_amplitude n Q cutoff q
          (\<lambda>_. 1) (\<lambda>_. 1) z * T s * H output)"
proof -
  let ?ps = "map (\<lambda>k. (fst (fst (fst z)) k,
    snd (fst (fst z)) k)) [0..<n]"
  let ?s = "snd (fst z)"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  have terminal_factor:
      "slp_left_branch_complex_kernel_list cutoff q T ?ps (snd z) ?s =
        T ?s * slp_left_branch_complex_kernel_list cutoff q ?one
          ?ps (snd z) ?s"
    by (rule slp_left_branch_list_terminal_factor)
  show ?thesis
    unfolding slp_natural_one_sided_weighted_amplitude_def Let_def
    by (simp add: terminal_factor algebra_simps)
qed

context aim_planar_riesz_hls_cauchy
begin

theorem slp_natural_one_sided_raw_amplitudes_integrable:
  fixes n :: nat and R C p :: real and X :: "slp_point set"
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
             A = slp_cauchy_transform orientation q;
             W = (\<lambda>T. slp_natural_one_sided_weighted_amplitude n Q cutoff q
               T (\<lambda>_. 1))
    in integrable MJ (W A) \<and> integrable MJ (W (\<lambda>_. 1))"
proof -
  let ?P = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?B = "(?P \<Otimes>\<^sub>M ?P) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "?B \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?A = "slp_cauchy_transform orientation q"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?W = "\<lambda>T. slp_natural_one_sided_weighted_amplitude n Q cutoff q T ?one"
  have radius_nonnegative: "0 \<le> 2 * R" using R_nonnegative by simp
  have q_measurable[measurable]: "q \<in> borel_measurable lborel"
    using q_lp unfolding aim_complex_lp_on_plane_def by blast
  have Q_measurable[measurable]: "Q \<in> borel_measurable lborel"
    using Q_lp unfolding aim_complex_lp_on_plane_def by blast
  have A_measurable: "?A \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF p_lower p_upper q_lp])
  have one_measurable: "?one \<in> borel_measurable lborel" by measurable
  have terminal_mass:
      "nn_integral lborel
        (slp_positive_root_output_density (2 * R) cutoff q
          (\<lambda>s. ennreal (norm (?A s))) n Q) < top_class.top"
    by (rule slp_natural_one_sided_cauchy_terminal_density_mass_finite[
      OF R_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative
        cutoff_support q_support])
  have unit_mass:
      "nn_integral lborel
        (slp_positive_root_output_density (2 * R) cutoff q
          (\<lambda>_. 1) n Q) < top_class.top"
    by (rule slp_positive_root_output_density_unweighted_mass_finite_lp_root[
      OF radius_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative])
  have component_integrable: "integrable ?MJ (?W T)"
    if T_measurable: "T \<in> borel_measurable lborel"
      and mass: "nn_integral lborel
        (slp_positive_root_output_density (2 * R) cutoff q
          (\<lambda>s. ennreal (norm (T s))) n Q) < top_class.top"
    for T :: slp_scalar_field
  proof -
    have phase_measurable:
        "(\<lambda>_::((((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point)) \<times>
          slp_point) \<times> slp_point). (0::real)) \<in> borel_measurable ?MJ"
      by measurable
    have weighted_mass:
        "nn_integral lborel (\<lambda>u. ennreal (norm (?one u)) *
          slp_positive_root_output_density (2 * R) cutoff q
            (\<lambda>s. ennreal (norm (T s))) n Q u) < top_class.top"
      using mass by simp
    note bound = slp_natural_one_sided_oscillatory_integral_bound[
      where n=n and R=R and psi="\<lambda>_::((((nat \<Rightarrow> slp_point) \<times>
        (nat \<Rightarrow> slp_point)) \<times> slp_point) \<times> slp_point). 0",
      OF R_nonnegative cutoff_measurable q_measurable T_measurable
        Q_measurable one_measurable Q_support cutoff_support q_support
        phase_measurable weighted_mass]
    show ?thesis using bound(1) by simp
  qed
  have terminal: "integrable ?MJ (?W ?A)"
    by (rule component_integrable[OF A_measurable terminal_mass])
  have unit: "integrable ?MJ (?W ?one)"
    by (rule component_integrable[OF one_measurable])
      (use unit_mass in simp)
  show ?thesis unfolding Let_def using terminal unit by blast
qed

end

end
