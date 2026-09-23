theory Inverse_Schrodinger_Lp_W1p_Zero_Pair_AE_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Pair_Difference"
begin

section \<open>Restricted almost-everywhere invariance of the Sobolev norm\<close>

theorem slp_w1p_norm_on_cong_restrict_AE:
  assumes X_measurable: "X \<in> sets lborel"
    and first_pair: "slp_w1p_pair_on p X u Du"
    and second_pair: "slp_w1p_pair_on p X v Dv"
    and function_AE: "AE x in restrict_space lborel X. u x = v x"
    and gradient_AE: "AE x in restrict_space lborel X. Du x = Dv x"
  shows "slp_w1p_norm_on p X u Du = slp_w1p_norm_on p X v Dv"
proof -
  have function_inside: "AE x in lborel. x \<in> X \<longrightarrow> u x = v x"
    using function_AE X_measurable by (simp add: AE_restrict_space_iff)
  have gradient_inside: "AE x in lborel. x \<in> X \<longrightarrow> Du x = Dv x"
    using gradient_AE X_measurable by (simp add: AE_restrict_space_iff)
  have function_power_AE:
      "AE x in lborel.
        Real_Vector_Spaces.norm (slp_restrict_field X u x) powr p =
        Real_Vector_Spaces.norm (slp_restrict_field X v x) powr p"
    using function_inside
    by eventually_elim (simp add: slp_restrict_field_def)
  have derivative_zero_power_AE:
      "AE x in lborel.
        Real_Vector_Spaces.norm
          (slp_restrict_field X (\<lambda>y. Du y $ 0) x) powr p =
        Real_Vector_Spaces.norm
          (slp_restrict_field X (\<lambda>y. Dv y $ 0) x) powr p"
    using gradient_inside
    by eventually_elim (simp add: slp_restrict_field_def)
  have derivative_one_power_AE:
      "AE x in lborel.
        Real_Vector_Spaces.norm
          (slp_restrict_field X (\<lambda>y. Du y $ 1) x) powr p =
        Real_Vector_Spaces.norm
          (slp_restrict_field X (\<lambda>y. Dv y $ 1) x) powr p"
    using gradient_inside
    by eventually_elim (simp add: slp_restrict_field_def)
  note first_integrable = slp_w1p_pair_power_integrable[OF first_pair]
  note second_integrable = slp_w1p_pair_power_integrable[OF second_pair]
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

section \<open>Representative transport of the compact-smooth closure\<close>

theorem slp_w1p_zero_pair_on_cong_restrict_AE:
  assumes exponent_one_le: "1 \<le> p"
    and X_measurable: "X \<in> sets lborel"
    and source_zero: "slp_w1p_zero_pair_on p X u Du"
    and target_pair: "slp_w1p_pair_on p X v Dv"
    and function_AE: "AE x in restrict_space lborel X. u x = v x"
    and gradient_AE: "AE x in restrict_space lborel X. Du x = Dv x"
  shows "slp_w1p_zero_pair_on p X v Dv"
proof -
  obtain phi :: "nat \<Rightarrow> slp_scalar_field" where
      phi_pairs:
        "\<forall>n. slp_test_function_on X (phi n) \<and>
          slp_w1p_pair_on p X (phi n) (slp_classical_gradient (phi n))"
    and phi_converges:
        "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
          slp_w1p_norm_on p X
            (\<lambda>x. phi n x - u x)
            (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
    using source_zero unfolding slp_w1p_zero_pair_on_def by blast
  have source_pair: "slp_w1p_pair_on p X u Du"
    using source_zero unfolding slp_w1p_zero_pair_on_def by blast
  have difference_norm:
      "slp_w1p_norm_on p X
          (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x) =
        slp_w1p_norm_on p X
          (\<lambda>x. phi n x - v x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Dv x)" for n
  proof -
    have approximant_pair:
        "slp_w1p_pair_on p X (phi n) (slp_classical_gradient (phi n))"
      using phi_pairs by blast
    have source_difference:
        "slp_w1p_pair_on p X
          (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x)"
      by (rule slp_w1p_pair_on_diff[
            OF exponent_one_le approximant_pair source_pair])
    have target_difference:
        "slp_w1p_pair_on p X
          (\<lambda>x. phi n x - v x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Dv x)"
      by (rule slp_w1p_pair_on_diff[
            OF exponent_one_le approximant_pair target_pair])
    have function_difference_AE:
        "AE x in restrict_space lborel X.
          phi n x - u x = phi n x - v x"
      using function_AE by eventually_elim simp
    have gradient_difference_AE:
        "AE x in restrict_space lborel X.
          slp_classical_gradient (phi n) x - Du x =
            slp_classical_gradient (phi n) x - Dv x"
      using gradient_AE by eventually_elim simp
    show ?thesis
      by (rule slp_w1p_norm_on_cong_restrict_AE[
            OF X_measurable source_difference target_difference
              function_difference_AE gradient_difference_AE])
  qed
  have target_converges:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on p X
          (\<lambda>x. phi n x - v x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Dv x) < epsilon"
  proof (intro allI impI)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    obtain N where tail:
        "\<forall>n\<ge>N.
          slp_w1p_norm_on p X
            (\<lambda>x. phi n x - u x)
            (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
      using phi_converges epsilon_positive by blast
    show "\<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on p X
          (\<lambda>x. phi n x - v x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Dv x) < epsilon"
      by (rule exI[of _ N]) (use tail in \<open>auto simp: difference_norm\<close>)
  qed
  show ?thesis
    unfolding slp_w1p_zero_pair_on_def
    using target_pair phi_pairs target_converges by blast
qed

end
