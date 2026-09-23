theory Inverse_Schrodinger_Lp_Weighted_NN_Integral_Pair
  imports Inverse_Schrodinger_Lp_Weighted_NN_Integral
begin

section \<open>Two-variable weighted Cauchy--Schwarz estimate\<close>

lemma slp_nn_integral_weighted_cauchy_schwarz_pair:
  fixes weight datum :: "slp_point \<Rightarrow> slp_point \<Rightarrow> ennreal"
  assumes [measurable]:
    "case_prod weight \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    "case_prod datum \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
  shows
    "(\<integral>\<^sup>+x. \<integral>\<^sup>+y. weight x y * datum x y
        \<partial>lborel \<partial>lborel)\<^sup>2 \<le>
      (\<integral>\<^sup>+x. \<integral>\<^sup>+y. weight x y
        \<partial>lborel \<partial>lborel) *
      (\<integral>\<^sup>+x. \<integral>\<^sup>+y.
        weight x y * datum x y ^ 2 \<partial>lborel \<partial>lborel)"
proof -
  let ?W = "case_prod weight"
  let ?D = "case_prod datum"
  have product_bound:
      "(\<integral>\<^sup>+xy. ?W xy * ?D xy
          \<partial>(lborel \<Otimes>\<^sub>M lborel))\<^sup>2 \<le>
        (\<integral>\<^sup>+xy. ?W xy
          \<partial>(lborel \<Otimes>\<^sub>M lborel)) *
        (\<integral>\<^sup>+xy. ?W xy * ?D xy ^ 2
          \<partial>(lborel \<Otimes>\<^sub>M lborel))"
    by (rule slp_nn_integral_weighted_cauchy_schwarz) measurable
  have product_left:
      "(\<integral>\<^sup>+xy. ?W xy * ?D xy
          \<partial>(lborel \<Otimes>\<^sub>M lborel)) =
        (\<integral>\<^sup>+x. \<integral>\<^sup>+y. weight x y * datum x y
          \<partial>lborel \<partial>lborel)"
    using lborel.nn_integral_fst[
      of "\<lambda>xy. ?W xy * ?D xy" lborel]
    by simp
  have product_weight:
      "(\<integral>\<^sup>+xy. ?W xy
          \<partial>(lborel \<Otimes>\<^sub>M lborel)) =
        (\<integral>\<^sup>+x. \<integral>\<^sup>+y. weight x y
          \<partial>lborel \<partial>lborel)"
    using lborel.nn_integral_fst[of ?W lborel]
    by simp
  have product_square:
      "(\<integral>\<^sup>+xy. ?W xy * ?D xy ^ 2
          \<partial>(lborel \<Otimes>\<^sub>M lborel)) =
        (\<integral>\<^sup>+x. \<integral>\<^sup>+y.
          weight x y * datum x y ^ 2 \<partial>lborel \<partial>lborel)"
    using lborel.nn_integral_fst[
      of "\<lambda>xy. ?W xy * ?D xy ^ 2" lborel]
    by simp
  show ?thesis
    using product_bound product_left product_weight product_square by simp
qed

end
