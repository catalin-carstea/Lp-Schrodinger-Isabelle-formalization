theory Inverse_Schrodinger_Lp_W1p_Norm_AE_Congruence
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Valid_Pair_Guards"
begin

section \<open>Almost-everywhere invariance of the reviewed Sobolev norm\<close>

theorem slp_w1p_norm_on_cong_AE:
  assumes first_pair: "slp_w1p_pair_on p X u Du"
    and second_pair: "slp_w1p_pair_on p X v Dv"
    and function_AE: "AE x in lborel. u x = v x"
    and gradient_AE: "AE x in lborel. Du x = Dv x"
  shows "slp_w1p_norm_on p X u Du = slp_w1p_norm_on p X v Dv"
proof -
  note first_integrable = slp_w1p_pair_power_integrable[OF first_pair]
  note second_integrable = slp_w1p_pair_power_integrable[OF second_pair]
  have function_power_AE:
      "AE x in lborel.
        Real_Vector_Spaces.norm (slp_restrict_field X u x) powr p =
        Real_Vector_Spaces.norm (slp_restrict_field X v x) powr p"
    using function_AE by eventually_elim (simp add: slp_restrict_field_def)
  have derivative_zero_power_AE:
      "AE x in lborel.
        Real_Vector_Spaces.norm
          (slp_restrict_field X (\<lambda>y. Du y $ 0) x) powr p =
        Real_Vector_Spaces.norm
          (slp_restrict_field X (\<lambda>y. Dv y $ 0) x) powr p"
    using gradient_AE by eventually_elim (simp add: slp_restrict_field_def)
  have derivative_one_power_AE:
      "AE x in lborel.
        Real_Vector_Spaces.norm
          (slp_restrict_field X (\<lambda>y. Du y $ 1) x) powr p =
        Real_Vector_Spaces.norm
          (slp_restrict_field X (\<lambda>y. Dv y $ 1) x) powr p"
    using gradient_AE by eventually_elim (simp add: slp_restrict_field_def)
  have function_integral:
      "integral\<^sup>L lborel
          (\<lambda>x. Real_Vector_Spaces.norm (slp_restrict_field X u x) powr p) =
        integral\<^sup>L lborel
          (\<lambda>x. Real_Vector_Spaces.norm (slp_restrict_field X v x) powr p)"
    by (rule integral_cong_AE[
          OF borel_measurable_integrable[OF first_integrable(1)]
            borel_measurable_integrable[OF second_integrable(1)]
            function_power_AE])
  have derivative_zero_integral:
      "integral\<^sup>L lborel
          (\<lambda>x. Real_Vector_Spaces.norm
            (slp_restrict_field X (\<lambda>y. Du y $ 0) x) powr p) =
        integral\<^sup>L lborel
          (\<lambda>x. Real_Vector_Spaces.norm
            (slp_restrict_field X (\<lambda>y. Dv y $ 0) x) powr p)"
    by (rule integral_cong_AE[
          OF borel_measurable_integrable[OF first_integrable(2)]
            borel_measurable_integrable[OF second_integrable(2)]
            derivative_zero_power_AE])
  have derivative_one_integral:
      "integral\<^sup>L lborel
          (\<lambda>x. Real_Vector_Spaces.norm
            (slp_restrict_field X (\<lambda>y. Du y $ 1) x) powr p) =
        integral\<^sup>L lborel
          (\<lambda>x. Real_Vector_Spaces.norm
            (slp_restrict_field X (\<lambda>y. Dv y $ 1) x) powr p)"
    by (rule integral_cong_AE[
          OF borel_measurable_integrable[OF first_integrable(3)]
            borel_measurable_integrable[OF second_integrable(3)]
            derivative_one_power_AE])
  show ?thesis
    unfolding slp_w1p_norm_on_def
    using function_integral derivative_zero_integral derivative_one_integral
    by simp
qed

end
