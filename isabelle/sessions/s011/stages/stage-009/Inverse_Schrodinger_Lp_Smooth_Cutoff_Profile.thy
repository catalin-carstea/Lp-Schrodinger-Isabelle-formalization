theory Inverse_Schrodinger_Lp_Smooth_Cutoff_Profile
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Smooth_Cutoff_Approximation"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Scaled_Cutoff"
begin

hide_const (open) Commutative_Ring.norm

section \<open>A constructed global smooth cutoff profile\<close>

theorem slp_smooth_cutoff_profile_exists:
  "\<exists>chi Dchi L.
    slp_cutoff_profile chi Dchi L \<and>
    smooth_on UNIV chi \<and>
    0 \<le> L \<and>
    (\<forall>x. 0 \<le> chi x) \<and>
    (\<forall>x. chi x \<le> 1) \<and>
    (\<forall>x \<in> cball (0 :: slp_point) 1. chi x = 1) \<and>
    csupport_on UNIV chi \<subseteq> ball 0 2"
proof -
  have closed_inner:
      "closedin
        (top_of_set (manifold_eucl.carrier :: slp_point set))
        (cball 0 1)"
    by simp
  have inner_subset_outer:
      "cball (0 :: slp_point) 1 \<subseteq> ball 0 2"
    by auto
  have outer_subset_carrier:
      "ball (0 :: slp_point) 2 \<subseteq>
        (manifold_eucl.carrier :: slp_point set)"
    by simp
  have outer_open: "open (ball (0 :: slp_point) 2)"
    by simp
  from manifold_eucl.smooth_bump_functionE[
      OF closed_inner inner_subset_outer outer_subset_carrier outer_open,
      where k=infinity]
  obtain chi :: "slp_point \<Rightarrow> real" where
      chi_diff_fun: "diff_fun infinity charts_eucl chi"
    and chi_nonnegative: "\<And>x. 0 \<le> chi x"
    and chi_at_most_one: "\<And>x. chi x \<le> 1"
    and chi_one:
      "\<And>x. x \<in> cball (0 :: slp_point) 1 \<Longrightarrow> chi x = 1"
    and chi_support:
      "csupport_on UNIV chi \<subseteq> ball (0 :: slp_point) 2"
    by auto

  have chi_smooth: "smooth_on UNIV chi"
    using diff_fun_charts_euclD[OF chi_diff_fun] by simp
  have chi_differentiable: "chi differentiable at x" for x
    using smooth_on_imp_differentiable_on[OF chi_smooth]
    by (simp add: differentiable_on_def)
  let ?Dchi = "\<lambda>x. frechet_derivative chi (at x)"

  have chi_outer: "chi x = 0" if "2 \<le> norm x" for x
  proof (rule ccontr)
    assume "chi x \<noteq> 0"
    then have x_support: "x \<in> support_on UNIV chi"
      by (simp add: support_on_def)
    have "x \<in> closure (support_on UNIV chi)"
      using closure_subset x_support by blast
    then have "x \<in> csupport_on UNIV chi"
      by (simp only: csupport_on_def)
    then have "x \<in> ball (0 :: slp_point) 2"
      using chi_support by blast
    with that show False by simp
  qed

  have derivative_inner_zero:
      "?Dchi x h = 0" if "norm x < 1" for x h
  proof -
    have x_inside: "x \<in> ball (0 :: slp_point) 1"
      using that by simp
    have local_constant:
        "chi y = (\<lambda>_ :: slp_point. (1 :: real)) y"
      if "y \<in> ball (0 :: slp_point) 1" for y
      using chi_one[of y] that by simp
    have
      "frechet_derivative chi (at x) =
        frechet_derivative (\<lambda>_ :: slp_point. (1 :: real)) (at x)"
      by (rule frechet_derivative_transform_within_open[
            OF chi_differentiable open_ball x_inside local_constant])
    then show ?thesis by simp
  qed

  have derivative_outer_zero:
      "?Dchi x h = 0" if "2 < norm x" for x h
  proof -
    let ?exterior = "- cball (0 :: slp_point) 2"
    have exterior_open: "open ?exterior"
      by (rule open_Compl) simp
    have x_exterior: "x \<in> ?exterior"
      using that by simp
    have local_zero:
        "chi y = (\<lambda>_ :: slp_point. (0 :: real)) y"
      if "y \<in> ?exterior" for y
      using chi_outer[of y] that by simp
    have
      "frechet_derivative chi (at x) =
        frechet_derivative (\<lambda>_ :: slp_point. (0 :: real)) (at x)"
      by (rule frechet_derivative_transform_within_open[
            OF chi_differentiable exterior_open x_exterior local_zero])
    then show ?thesis by simp
  qed

  have derivative_support:
      "1 \<le> norm x \<and> norm x \<le> 2"
    if "?Dchi x h \<noteq> 0" for x h
  proof -
    have "\<not> norm x < 1"
      using that derivative_inner_zero[of x h] by blast
    moreover have "\<not> 2 < norm x"
      using that derivative_outer_zero[of x h] by blast
    ultimately show ?thesis by simp
  qed

  have basis_bound_exists:
      "\<exists>M. 0 \<le> M \<and>
        (\<forall>x \<in> cball (0 :: slp_point) 2.
          norm (?Dchi x b) \<le> M)"
    if "b \<in> (Basis :: slp_point set)" for b
  proof -
    have derivative_smooth:
        "smooth_on UNIV (\<lambda>x. ?Dchi x b)"
      by (rule smooth_on_frechet_derivative[OF chi_smooth])
    have derivative_continuous:
        "continuous_on (cball (0 :: slp_point) 2)
          (\<lambda>x. ?Dchi x b)"
    proof (rule continuous_on_subset)
      show "continuous_on UNIV (\<lambda>x. ?Dchi x b)"
        by (rule higher_differentiable_on_imp_continuous_on)
          (rule smooth_onD[OF derivative_smooth], simp)
      show "cball (0 :: slp_point) 2 \<subseteq> UNIV"
        by simp
    qed
    from continuous_on_compact_bound[
        OF compact_cball derivative_continuous]
    obtain M where "0 \<le> M"
      and "\<And>x. x \<in> cball (0 :: slp_point) 2 \<Longrightarrow>
        norm (?Dchi x b) \<le> M"
      by blast
    then show ?thesis by blast
  qed
  then obtain M :: "slp_point \<Rightarrow> real" where
      M_nonnegative: "\<And>b. b \<in> Basis \<Longrightarrow> 0 \<le> M b"
    and M_bound:
      "\<And>b x. b \<in> Basis \<Longrightarrow>
        x \<in> cball (0 :: slp_point) 2 \<Longrightarrow>
        norm (?Dchi x b) \<le> M b"
    by metis
  let ?L = "\<Sum>b \<in> (Basis :: slp_point set). M b"
  have L_nonnegative: "0 \<le> ?L"
    by (rule sum_nonneg) (use M_nonnegative in blast)

  have derivative_bound:
      "norm (?Dchi x h) \<le> ?L * norm h" for x h
  proof (cases "x \<in> cball (0 :: slp_point) 2")
    case True
    have derivative_linear: "linear (?Dchi x)"
      by (rule linear_frechet_derivative[OF chi_differentiable])
    have derivative_expansion:
        "?Dchi x h =
          (\<Sum>b \<in> Basis. (h \<bullet> b) *\<^sub>R (?Dchi x b))"
    proof -
      have
        "?Dchi x h =
          ?Dchi x (\<Sum>b \<in> Basis. (h \<bullet> b) *\<^sub>R b)"
        by (simp only: euclidean_representation)
      also have "... =
          (\<Sum>b \<in> Basis. ?Dchi x ((h \<bullet> b) *\<^sub>R b))"
        by (rule linear_sum[OF derivative_linear])
      also have "... =
          (\<Sum>b \<in> Basis. (h \<bullet> b) *\<^sub>R (?Dchi x b))"
        by (rule sum.cong[OF refl])
          (simp add: linear_scale[OF derivative_linear])
      finally show ?thesis .
    qed
    have basis_term_bound:
        "norm ((h \<bullet> b) *\<^sub>R (?Dchi x b)) \<le>
          M b * norm h" if "b \<in> Basis" for b
    proof -
      have component_bound: "\<bar>h \<bullet> b\<bar> \<le> norm h"
        by (rule Basis_le_norm[OF that])
      have direction_bound: "norm (?Dchi x b) \<le> M b"
        by (rule M_bound[OF that True])
      have M_nonnegative_b: "0 \<le> M b"
        by (rule M_nonnegative[OF that])
      have
        "norm ((h \<bullet> b) *\<^sub>R (?Dchi x b)) =
          \<bar>h \<bullet> b\<bar> * norm (?Dchi x b)"
        by (rule norm_scaleR)
      also have "... \<le> norm h * M b"
        by (rule mult_mono[OF component_bound direction_bound]) simp_all
      also have "... = M b * norm h"
        by (rule mult.commute)
      finally show ?thesis .
    qed
    have
      "norm (?Dchi x h) \<le>
        (\<Sum>b \<in> Basis. norm ((h \<bullet> b) *\<^sub>R (?Dchi x b)))"
      unfolding derivative_expansion by (rule norm_sum)
    also have "... \<le> (\<Sum>b \<in> Basis. M b * norm h)"
      by (rule sum_mono) (rule basis_term_bound)
    also have "... = ?L * norm h"
      by (simp add: sum_distrib_right)
    finally show ?thesis .
  next
    case False
    then have "2 < norm x" by simp
    then have "?Dchi x h = 0"
      by (rule derivative_outer_zero)
    then show ?thesis using L_nonnegative by simp
  qed

  have profile: "slp_cutoff_profile chi ?Dchi ?L"
  proof unfold_locales
    show "chi x = 1" if "norm x \<le> 1" for x
      by (rule chi_one) (use that in simp)
    show "chi x = 0" if "2 \<le> norm x" for x
      by (rule chi_outer[OF that])
    show "norm (chi x) \<le> 1" for x
      using chi_nonnegative[of x] chi_at_most_one[of x] by simp
    show "(chi has_derivative ?Dchi x) (at x)" for x
      using chi_differentiable[of x]
      by (simp only: frechet_derivative_works)
    show "norm (?Dchi x h) \<le> ?L * norm h" for x h
      by (rule derivative_bound)
    show "1 \<le> norm x \<and> norm x \<le> 2"
      if "?Dchi x h \<noteq> 0" for x h
      by (rule derivative_support[OF that])
  qed
  show ?thesis
    using profile chi_smooth L_nonnegative chi_nonnegative chi_at_most_one
      chi_one chi_support
    by blast
qed

definition slp_global_cutoff_data ::
  "(slp_point \<Rightarrow> real) \<times>
    (slp_point \<Rightarrow> slp_point \<Rightarrow> real) \<times> real"
where
  "slp_global_cutoff_data =
    (SOME data.
      case data of (chi, Dchi, L) \<Rightarrow>
        slp_cutoff_profile chi Dchi L \<and>
        smooth_on UNIV chi \<and>
        0 \<le> L \<and>
        (\<forall>x. 0 \<le> chi x) \<and>
        (\<forall>x. chi x \<le> 1) \<and>
        (\<forall>x \<in> cball (0 :: slp_point) 1. chi x = 1) \<and>
        csupport_on UNIV chi \<subseteq> ball 0 2)"

definition slp_global_cutoff_chi :: "slp_point \<Rightarrow> real" where
  "slp_global_cutoff_chi = fst slp_global_cutoff_data"

definition slp_global_cutoff_Dchi ::
  "slp_point \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_global_cutoff_Dchi = fst (snd slp_global_cutoff_data)"

definition slp_global_cutoff_L :: real where
  "slp_global_cutoff_L = snd (snd slp_global_cutoff_data)"

theorem slp_global_cutoff_profile_spec:
  "slp_cutoff_profile slp_global_cutoff_chi
      slp_global_cutoff_Dchi slp_global_cutoff_L \<and>
    smooth_on UNIV slp_global_cutoff_chi \<and>
    0 \<le> slp_global_cutoff_L \<and>
    (\<forall>x. 0 \<le> slp_global_cutoff_chi x) \<and>
    (\<forall>x. slp_global_cutoff_chi x \<le> 1) \<and>
    (\<forall>x \<in> cball (0 :: slp_point) 1.
      slp_global_cutoff_chi x = 1) \<and>
    csupport_on UNIV slp_global_cutoff_chi \<subseteq> ball 0 2"
proof -
  have data_exists:
      "\<exists>data ::
        (slp_point \<Rightarrow> real) \<times>
          (slp_point \<Rightarrow> slp_point \<Rightarrow> real) \<times> real.
        case data of (chi, Dchi, L) \<Rightarrow>
          slp_cutoff_profile chi Dchi L \<and>
          smooth_on UNIV chi \<and>
          0 \<le> L \<and>
          (\<forall>x. 0 \<le> chi x) \<and>
          (\<forall>x. chi x \<le> 1) \<and>
          (\<forall>x \<in> cball (0 :: slp_point) 1. chi x = 1) \<and>
          csupport_on UNIV chi \<subseteq> ball 0 2"
    using slp_smooth_cutoff_profile_exists by blast
  have data_spec:
      "case slp_global_cutoff_data of (chi, Dchi, L) \<Rightarrow>
        slp_cutoff_profile chi Dchi L \<and>
        smooth_on UNIV chi \<and>
        0 \<le> L \<and>
        (\<forall>x. 0 \<le> chi x) \<and>
        (\<forall>x. chi x \<le> 1) \<and>
        (\<forall>x \<in> cball (0 :: slp_point) 1. chi x = 1) \<and>
        csupport_on UNIV chi \<subseteq> ball 0 2"
    unfolding slp_global_cutoff_data_def
    by (rule someI_ex[OF data_exists])
  obtain chi Dchi L where data:
      "slp_global_cutoff_data = (chi, Dchi, L)"
    by (cases slp_global_cutoff_data) auto
  show ?thesis
    using data_spec
    unfolding slp_global_cutoff_chi_def slp_global_cutoff_Dchi_def
      slp_global_cutoff_L_def data
    by simp
qed

interpretation slp_global_cutoff:
  slp_cutoff_profile slp_global_cutoff_chi
    slp_global_cutoff_Dchi slp_global_cutoff_L
  by (rule slp_global_cutoff_profile_spec[THEN conjunct1])

end
