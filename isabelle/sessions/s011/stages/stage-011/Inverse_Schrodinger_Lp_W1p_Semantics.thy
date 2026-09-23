theory Inverse_Schrodinger_Lp_W1p_Semantics
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_Qstar_Zero_Positive_Tau_Local_Gain"
begin

section \<open>Exponent-parametric first-order Sobolev pairs\<close>

definition slp_w1p_pair_on ::
  "real \<Rightarrow> slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_gradient_field \<Rightarrow> bool"
where
  "slp_w1p_pair_on p X u Du \<longleftrightarrow>
    slp_weak_gradient_on X u Du \<and>
    slp_complex_lp_on p X u \<and>
    slp_complex_lp_on p X (\<lambda>x. Du x $ 0) \<and>
    slp_complex_lp_on p X (\<lambda>x. Du x $ 1)"

definition slp_w1p_norm_on ::
  "real \<Rightarrow> slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_gradient_field \<Rightarrow> real"
where
  "slp_w1p_norm_on p X u Du =
    ((integral\<^sup>L lborel
        (\<lambda>x. Real_Vector_Spaces.norm (slp_restrict_field X u x) powr p)) +
      (integral\<^sup>L lborel
        (\<lambda>x. Real_Vector_Spaces.norm
          (slp_restrict_field X (\<lambda>y. Du y $ 0) x) powr p)) +
      (integral\<^sup>L lborel
        (\<lambda>x. Real_Vector_Spaces.norm
          (slp_restrict_field X (\<lambda>y. Du y $ 1) x) powr p)))
      powr (1 / p)"

definition slp_w1p_zero_pair_on ::
  "real \<Rightarrow> slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_gradient_field \<Rightarrow> bool"
where
  "slp_w1p_zero_pair_on p X u Du \<longleftrightarrow>
    slp_w1p_pair_on p X u Du \<and>
    (\<exists>phi :: nat \<Rightarrow> slp_scalar_field.
      (\<forall>n. slp_test_function_on X (phi n) \<and>
        slp_w1p_pair_on p X (phi n) (slp_classical_gradient (phi n))) \<and>
      (\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on p X
          (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon))"

section \<open>Official rough qstar estimate\<close>

definition slp_qstar_w1p_claim ::
  "real \<Rightarrow> slp_point set \<Rightarrow> slp_point set \<Rightarrow> bool"
where
  "slp_qstar_w1p_claim a X Z \<longleftrightarrow>
    (1 < a \<and> a < 2 \<and> open X \<and> X \<noteq> {} \<and>
      bounded X \<and> compact Z)
    \<longrightarrow>
      (\<exists>C::real. 0 < C \<and>
        (\<forall>tau z0 f Df.
          2 \<le> tau \<and> z0 \<in> Z \<and>
          slp_w1p_zero_pair_on a X f Df
          \<longrightarrow>
            slp_complex_lp_on (aim_hls_target_exponent a) X
              (slp_partial_psi_inverse tau z0 (slp_restrict_field X f)) \<and>
            slp_complex_lp_norm_on (aim_hls_target_exponent a) X
              (slp_partial_psi_inverse tau z0 (slp_restrict_field X f))
              \<le> C * inverse (sqrt tau) * slp_w1p_norm_on a X f Df))"

end
