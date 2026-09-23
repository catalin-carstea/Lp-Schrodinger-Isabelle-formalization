theory Inverse_Schrodinger_Lp_Annulus_Dyadic_Growth
  imports Inverse_Schrodinger_Lp_Annulus_Shell_Additivity
begin

section \<open>Dyadic growth of the squared radial annulus\<close>

lemma slp_squared_radial_annulus_unit_zero:
  "integral\<^sup>L lborel (slp_squared_radial_annulus 1 1) = 0"
proof -
  have sphere_negligible: "negligible (sphere (0::slp_point) 1)"
    by (rule negligible_sphere)
  have sphere_null: "sphere (0::slp_point) 1 \<in> null_sets lborel"
    using sphere_negligible
    by (auto simp: negligible_iff_null_sets null_sets_completion_iff)
  have outside_sphere:
    "AE y in (lborel :: slp_point measure). y \<notin> sphere 0 1"
    by (rule AE_not_in[OF sphere_null])
  have ae_zero:
    "AE y in lborel. slp_squared_radial_annulus 1 1 y = 0"
  proof (rule eventually_mono[OF outside_sphere])
    fix y :: slp_point
    assume outside: "y \<notin> sphere 0 1"
    have "norm y \<noteq> 1"
      using outside by (simp add: sphere_def dist_norm)
    then show "slp_squared_radial_annulus 1 1 y = 0"
      unfolding slp_squared_radial_annulus_def by auto
  qed
  show ?thesis
    by (rule integral_eq_zero_AE[OF ae_zero])
qed

lemma slp_squared_radial_annulus_dyadic:
  "integral\<^sup>L lborel
      (slp_squared_radial_annulus 1 ((2::real) ^ n)) =
    real n * integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
proof (induction n)
  case 0
  then show ?case
    using slp_squared_radial_annulus_unit_zero by simp
next
  case (Suc n)
  have power_lower: "1 \<le> (2::real) ^ n"
    by simp
  have step:
    "integral\<^sup>L lborel
        (slp_squared_radial_annulus 1 (((2::real) ^ n) * 2)) =
      integral\<^sup>L lborel
          (slp_squared_radial_annulus 1 ((2::real) ^ n)) +
        integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
    by (rule slp_squared_radial_annulus_multiplicative_additivity[OF
          power_lower]) simp
  show ?case
    using step Suc.IH
    by (simp add: power_Suc algebra_simps)
qed

lemma slp_squared_radial_annulus_dyadic_majorant:
  assumes radius_lower: "1 \<le> R"
    and radius_upper: "R \<le> (2::real) ^ n"
  shows "integral\<^sup>L lborel (slp_squared_radial_annulus 1 R) \<le>
    real n * integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
proof -
  have upper:
    "integral\<^sup>L lborel (slp_squared_radial_annulus 1 R) \<le>
      integral\<^sup>L lborel
        (slp_squared_radial_annulus 1 ((2::real) ^ n))"
    by (rule slp_squared_radial_annulus_upper_mono) (use radius_upper in auto)
  show ?thesis
    using upper slp_squared_radial_annulus_dyadic[of n] by simp
qed

lemma slp_squared_radial_annulus_rescaled_dyadic_majorant:
  assumes delta_positive: "0 < delta"
    and normalized_lower: "1 \<le> R / delta"
    and normalized_upper: "R / delta \<le> (2::real) ^ n"
  shows "integral\<^sup>L lborel (slp_squared_radial_annulus delta R) \<le>
    real n * integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
proof -
  have normalize:
    "integral\<^sup>L lborel (slp_squared_radial_annulus delta R) =
      integral\<^sup>L lborel
        (slp_squared_radial_annulus 1 (R / delta))"
    by (rule slp_squared_radial_annulus_integral_normalize[OF delta_positive])
  have majorant:
    "integral\<^sup>L lborel
        (slp_squared_radial_annulus 1 (R / delta)) \<le>
      real n * integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
    by (rule slp_squared_radial_annulus_dyadic_majorant[OF normalized_lower
          normalized_upper])
  show ?thesis
    using normalize majorant by simp
qed

end
