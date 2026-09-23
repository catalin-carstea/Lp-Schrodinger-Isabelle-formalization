theory Inverse_Schrodinger_Lp_Annulus_Logarithmic_Growth
  imports Inverse_Schrodinger_Lp_Annulus_Dyadic_Growth
begin

section \<open>Ceiling-logarithm control of the squared radial annulus\<close>

definition slp_dyadic_index :: "real \<Rightarrow> nat" where
  "slp_dyadic_index r = nat \<lceil>log 2 r\<rceil>"

lemma slp_dyadic_index_power_upper:
  assumes radius_lower: "1 \<le> r"
  shows "r \<le> (2::real) ^ slp_dyadic_index r"
proof -
  have "r \<le> (2::real) ^ nat \<lceil>log 2 r\<rceil>"
    by (rule power_of_nat_log_ge) simp
  then show ?thesis
    unfolding slp_dyadic_index_def .
qed

lemma slp_dyadic_index_real_upper:
  assumes radius_lower: "1 \<le> r"
  shows "real (slp_dyadic_index r) \<le> 1 + log 2 r"
proof -
  have radius_positive: "0 < r"
    using radius_lower by linarith
  have log_nonnegative: "0 \<le> log 2 r"
    using radius_lower radius_positive by simp
  have ceiling_upper:
    "(of_int \<lceil>log 2 r\<rceil> :: real) \<le> log 2 r + 1"
    by simp
  have cast_index:
    "real (nat \<lceil>log 2 r\<rceil>) =
      (of_int \<lceil>log 2 r\<rceil> :: real)"
    using log_nonnegative by simp
  show ?thesis
    unfolding slp_dyadic_index_def
    using ceiling_upper cast_index by linarith
qed

lemma slp_squared_radial_annulus_logarithmic_majorant:
  assumes radius_lower: "1 \<le> R"
  shows "integral\<^sup>L lborel (slp_squared_radial_annulus 1 R) \<le>
    (1 + log 2 R) *
      integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
proof -
  let ?n = "slp_dyadic_index R"
  have dyadic_upper: "R \<le> (2::real) ^ ?n"
    by (rule slp_dyadic_index_power_upper[OF radius_lower])
  have annulus_bound:
    "integral\<^sup>L lborel (slp_squared_radial_annulus 1 R) \<le>
      real ?n * integral\<^sup>L lborel
        (slp_squared_radial_annulus 1 2)"
    by (rule slp_squared_radial_annulus_dyadic_majorant[OF radius_lower
          dyadic_upper])
  have index_bound: "real ?n \<le> 1 + log 2 R"
    by (rule slp_dyadic_index_real_upper[OF radius_lower])
  have annulus_constant_nonnegative:
    "0 \<le> integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
    by (rule Bochner_Integration.integral_nonneg) simp
  have weighted_index_bound:
    "real ?n * integral\<^sup>L lborel (slp_squared_radial_annulus 1 2) \<le>
      (1 + log 2 R) *
        integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
    by (rule mult_right_mono[OF index_bound annulus_constant_nonnegative])
  show ?thesis
    using annulus_bound weighted_index_bound by linarith
qed

lemma slp_squared_radial_annulus_rescaled_logarithmic_majorant:
  assumes delta_positive: "0 < delta"
    and normalized_lower: "1 \<le> R / delta"
  shows "integral\<^sup>L lborel (slp_squared_radial_annulus delta R) \<le>
    (1 + log 2 (R / delta)) *
      integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
proof -
  have normalize:
    "integral\<^sup>L lborel (slp_squared_radial_annulus delta R) =
      integral\<^sup>L lborel
        (slp_squared_radial_annulus 1 (R / delta))"
    by (rule slp_squared_radial_annulus_integral_normalize[OF delta_positive])
  have normalized_bound:
    "integral\<^sup>L lborel
        (slp_squared_radial_annulus 1 (R / delta)) \<le>
      (1 + log 2 (R / delta)) *
        integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
    by (rule slp_squared_radial_annulus_logarithmic_majorant[OF
          normalized_lower])
  show ?thesis
    using normalize normalized_bound by simp
qed

end
