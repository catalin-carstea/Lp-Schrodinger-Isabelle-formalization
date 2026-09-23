theory Inverse_Schrodinger_Lp_Scaled_Cutoff
  imports Inverse_Schrodinger_Lp_Center_Kernel_Derivative
begin

section \<open>Positive scaling of a cutoff profile\<close>

locale slp_cutoff_profile =
  fixes chi :: "slp_point \<Rightarrow> real"
    and Dchi :: "slp_point \<Rightarrow> slp_point \<Rightarrow> real"
    and L :: real
  assumes inner_value: "norm x \<le> 1 \<Longrightarrow> chi x = 1"
    and outer_value: "2 \<le> norm x \<Longrightarrow> chi x = 0"
    and range_bound: "norm (chi x) \<le> 1"
    and profile_derivative:
      "(chi has_derivative Dchi x) (at x)"
    and derivative_bound:
      "norm (Dchi x h) \<le> L * norm h"
    and derivative_support:
      "Dchi x h \<noteq> 0 \<Longrightarrow> 1 \<le> norm x \<and> norm x \<le> 2"
begin

definition slp_cutoff_argument ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> slp_point"
where
  "slp_cutoff_argument delta c z = inverse delta *\<^sub>R (z - c)"

definition slp_scaled_cutoff ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_scaled_cutoff delta c z = chi (slp_cutoff_argument delta c z)"

definition slp_scaled_cutoff_derivative ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow>
    slp_point \<Rightarrow> real"
where
  "slp_scaled_cutoff_derivative delta c z h =
    Dchi (slp_cutoff_argument delta c z) (inverse delta *\<^sub>R h)"

lemma slp_cutoff_argument_norm:
  assumes delta_positive: "0 < delta"
  shows "norm (slp_cutoff_argument delta c z) = norm (z - c) / delta"
  unfolding slp_cutoff_argument_def
  using delta_positive
  by (simp add: norm_scaleR abs_of_pos divide_inverse)

lemma slp_scaled_cutoff_inner:
  assumes delta_positive: "0 < delta"
    and inside: "norm (z - c) \<le> delta"
  shows "slp_scaled_cutoff delta c z = 1"
proof -
  have "norm (slp_cutoff_argument delta c z) \<le> 1"
    using inside delta_positive
    by (simp add: slp_cutoff_argument_norm divide_le_eq)
  then show ?thesis
    unfolding slp_scaled_cutoff_def by (rule inner_value)
qed

lemma slp_scaled_cutoff_outer:
  assumes delta_positive: "0 < delta"
    and outside: "2 * delta \<le> norm (z - c)"
  shows "slp_scaled_cutoff delta c z = 0"
proof -
  have "2 \<le> norm (slp_cutoff_argument delta c z)"
    using outside delta_positive
    by (simp add: slp_cutoff_argument_norm le_divide_eq)
  then show ?thesis
    unfolding slp_scaled_cutoff_def by (rule outer_value)
qed

lemma slp_scaled_cutoff_norm:
  "norm (slp_scaled_cutoff delta c z) \<le> 1"
  unfolding slp_scaled_cutoff_def by (rule range_bound)

lemma slp_scaled_cutoff_has_derivative:
  "((slp_scaled_cutoff delta c) has_derivative
      slp_scaled_cutoff_derivative delta c z) (at z)"
proof -
  have argument_derivative:
    "((\<lambda>w :: slp_point. inverse delta *\<^sub>R (w - c))
      has_derivative (\<lambda>h. inverse delta *\<^sub>R h)) (at z)"
    by (auto intro!: derivative_eq_intros)
  have composed:
    "((\<lambda>w. chi (inverse delta *\<^sub>R (w - c))) has_derivative
      (\<lambda>h. Dchi (inverse delta *\<^sub>R (z - c))
        (inverse delta *\<^sub>R h))) (at z)"
    by (rule has_derivative_compose[OF argument_derivative
          profile_derivative])
  show ?thesis
    unfolding slp_scaled_cutoff_def slp_cutoff_argument_def
      slp_scaled_cutoff_derivative_def
    by (rule composed)
qed

lemma slp_scaled_cutoff_derivative_bound:
  assumes delta_positive: "0 < delta"
  shows "norm (slp_scaled_cutoff_derivative delta c z h) \<le>
    (L / delta) * norm h"
proof -
  have bound:
    "norm (Dchi (slp_cutoff_argument delta c z)
      (inverse delta *\<^sub>R h)) \<le>
      L * norm (inverse delta *\<^sub>R h)"
    by (rule derivative_bound)
  have scaled_norm:
    "norm (inverse delta *\<^sub>R h) = inverse delta * norm h"
    using delta_positive by (simp add: norm_scaleR abs_of_pos)
  show ?thesis
    unfolding slp_scaled_cutoff_derivative_def
    using bound
    by (simp only: scaled_norm divide_inverse mult.assoc)
qed

lemma slp_scaled_cutoff_derivative_support:
  assumes delta_positive: "0 < delta"
    and derivative_nonzero:
      "slp_scaled_cutoff_derivative delta c z h \<noteq> 0"
  shows "delta \<le> norm (z - c) \<and> norm (z - c) \<le> 2 * delta"
proof -
  have profile_nonzero:
    "Dchi (slp_cutoff_argument delta c z)
      (inverse delta *\<^sub>R h) \<noteq> 0"
    using derivative_nonzero
    unfolding slp_scaled_cutoff_derivative_def .
  have support:
    "1 \<le> norm (slp_cutoff_argument delta c z) \<and>
      norm (slp_cutoff_argument delta c z) \<le> 2"
    by (rule derivative_support[OF profile_nonzero])
  show ?thesis
    using support delta_positive
    by (simp add: slp_cutoff_argument_norm
        le_divide_eq divide_le_eq algebra_simps)
qed

lemma slp_scaled_cutoff_complement_support:
  assumes delta_positive: "0 < delta"
    and complement_nonzero: "1 - slp_scaled_cutoff delta c z \<noteq> 0"
  shows "delta < norm (z - c)"
proof (rule ccontr)
  assume "\<not> delta < norm (z - c)"
  then have "norm (z - c) \<le> delta" by simp
  then have "slp_scaled_cutoff delta c z = 1"
    by (rule slp_scaled_cutoff_inner[OF delta_positive])
  with complement_nonzero show False by simp
qed

end

end
