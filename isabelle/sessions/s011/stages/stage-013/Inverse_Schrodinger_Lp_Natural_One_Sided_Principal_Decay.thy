theory Inverse_Schrodinger_Lp_Natural_One_Sided_Principal_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Zero_Principal_Decay"
begin

context aim_planar_riesz_hls_cauchy
begin

section \<open>All-natural one-sided principal decay\<close>

theorem slp_natural_one_sided_principal_decay:
  fixes n :: nat and R C p :: real and X :: "slp_point set"
    and cutoff q Q phi :: slp_scalar_field
    and orientation :: slp_cauchy_orientation
  assumes stationary:
      "hormander_quadratic_stationary_phase_decay_claim TYPE(2)"
    and density: "evans_compact_smooth_l1_density_claim TYPE(2)"
    and R_nonnegative: "0 \<le> R"
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
    in ((\<lambda>omega::real. integral\<^sup>L MJ
      (\<lambda>z. exp (\<i> * of_real (omega * residual z)) *
        (slp_natural_one_sided_weighted_amplitude n Q cutoff q A phi z -
         slp_natural_one_sided_weighted_amplitude n Q cutoff q (\<lambda>_. 1)
           (\<lambda>u. phi u * A u) z))) \<longlongrightarrow> 0) at_top"
proof (cases n)
  case 0
  then show ?thesis
    using slp_natural_one_sided_zero_principal_decay[
      where Q = Q and cutoff = cutoff and q = q
        and A = "slp_cauchy_transform orientation q" and phi = phi]
    by simp
next
  case (Suc k)
  then show ?thesis
    using slp_natural_one_sided_positive_principal_decay[
      OF stationary density R_nonnegative p_lower p_upper X_measurable
        X_bounded cutoff_measurable q_lp Q_lp Q_outside cutoff_bound
        C_nonnegative Q_support cutoff_support q_support phi_test,
      where n = k and orientation = orientation]
    by simp
qed

end

end
