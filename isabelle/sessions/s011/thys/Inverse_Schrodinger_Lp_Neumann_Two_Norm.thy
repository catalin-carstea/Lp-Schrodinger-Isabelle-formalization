theory Inverse_Schrodinger_Lp_Neumann_Two_Norm
  imports Inverse_Schrodinger_Lp_Neumann_Fixed_Point
begin

section \<open>Normalized two-norm coefficient bounds\<close>

lemma slp_neumann_iterate_secondary_geometric_le:
  fixes S :: "'a::real_normed_vector \<Rightarrow> 'a"
    and B :: 'a
    and secondary :: "'a \<Rightarrow> real"
    and rho D Q :: real
  assumes rho_nonnegative: "0 \<le> rho"
    and D_nonnegative: "0 \<le> D"
    and primary_step: "\<And>f. norm (S f) \<le> rho * norm f"
    and secondary_step: "\<And>f. secondary (S f) \<le> D * norm f"
    and secondary_base: "secondary B \<le> Q"
    and normalization: "D * norm B \<le> Q * rho"
  shows "secondary (slp_neumann_iterate S B j) \<le> Q * rho ^ j"
proof (cases j)
  case 0
  then show ?thesis
    using secondary_base by simp
next
  case (Suc k)
  have raw:
    "secondary (slp_neumann_iterate S B (Suc k))
      \<le> D * norm B * rho ^ k"
    by (rule slp_neumann_iterate_secondary_le[
          OF rho_nonnegative D_nonnegative primary_step secondary_step])
  have scaled: "D * norm B * rho ^ k \<le> (Q * rho) * rho ^ k"
    by (rule mult_right_mono[OF normalization],
        rule zero_le_power[OF rho_nonnegative])
  have "secondary (slp_neumann_iterate S B (Suc k))
      \<le> (Q * rho) * rho ^ k"
    using raw scaled by (rule order_trans)
  also have "... = Q * rho ^ Suc k"
    by (simp add: power_Suc algebra_simps)
  finally show ?thesis
    using Suc by simp
qed

theorem slp_neumann_iterate_two_norm_bounds:
  fixes S :: "'a::real_normed_vector \<Rightarrow> 'a"
    and B :: 'a
    and secondary :: "'a \<Rightarrow> real"
    and rho D P Q :: real
  assumes rho_nonnegative: "0 \<le> rho"
    and D_nonnegative: "0 \<le> D"
    and primary_step: "\<And>f. norm (S f) \<le> rho * norm f"
    and secondary_step: "\<And>f. secondary (S f) \<le> D * norm f"
    and primary_base: "norm B \<le> P"
    and secondary_base: "secondary B \<le> Q"
    and normalization: "D * norm B \<le> Q * rho"
  shows "norm (slp_neumann_iterate S B j) \<le> P * rho ^ j"
    and "secondary (slp_neumann_iterate S B j) \<le> Q * rho ^ j"
proof -
  have raw_primary:
    "norm (slp_neumann_iterate S B j) \<le> norm B * rho ^ j"
    by (rule slp_neumann_iterate_norm_le[OF rho_nonnegative primary_step])
  have scaled_primary: "norm B * rho ^ j \<le> P * rho ^ j"
    by (rule mult_right_mono[OF primary_base],
        rule zero_le_power[OF rho_nonnegative])
  show "norm (slp_neumann_iterate S B j) \<le> P * rho ^ j"
    using raw_primary scaled_primary by (rule order_trans)
  show "secondary (slp_neumann_iterate S B j) \<le> Q * rho ^ j"
    by (rule slp_neumann_iterate_secondary_geometric_le[
          OF rho_nonnegative D_nonnegative primary_step secondary_step
            secondary_base normalization])
qed

end
