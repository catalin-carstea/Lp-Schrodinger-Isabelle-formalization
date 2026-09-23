theory Inverse_Schrodinger_Lp_AE_Interface
  imports
    "Paper_Inverse_Schrodinger_Lp_Uniqueness.Inverse_Schrodinger_Lp_Main_Statement"
begin

section \<open>Almost-everywhere equivalence relations\<close>

lemma slp_h1_data_ae_eq_refl [simp]:
  "slp_h1_data_ae_eq U F F"
  by (simp add: slp_h1_data_ae_eq_def)

lemma slp_h1_data_ae_eq_sym:
  assumes "slp_h1_data_ae_eq U F G"
  shows "slp_h1_data_ae_eq U G F"
  using assms
  unfolding slp_h1_data_ae_eq_def
  by eventually_elim auto

lemma slp_h1_data_ae_eq_trans:
  assumes "slp_h1_data_ae_eq U F G"
    and "slp_h1_data_ae_eq U G H"
  shows "slp_h1_data_ae_eq U F H"
  using assms
  unfolding slp_h1_data_ae_eq_def
  by eventually_elim auto

lemma slp_potential_ae_equal_refl [simp]:
  "slp_potential_ae_equal U V V"
  by (simp add: slp_potential_ae_equal_def)

lemma slp_potential_ae_equal_sym:
  assumes "slp_potential_ae_equal U V W"
  shows "slp_potential_ae_equal U W V"
  using assms
  unfolding slp_potential_ae_equal_def
  by eventually_elim auto

lemma slp_potential_ae_equal_trans:
  assumes "slp_potential_ae_equal U V W"
    and "slp_potential_ae_equal U W Z"
  shows "slp_potential_ae_equal U V Z"
  using assms
  unfolding slp_potential_ae_equal_def
  by eventually_elim auto

section \<open>Congruence of the weak form\<close>

lemma slp_set_lebesgue_integral_cong_restrict_AE:
  fixes f g :: "slp_point \<Rightarrow> complex"
  assumes measurable_U: "U \<in> sets lborel"
    and ae_eq: "AE x in restrict_space lborel U. f x = g x"
    and integrable_f: "set_integrable lborel U f"
    and integrable_g: "set_integrable lborel U g"
  shows "set_lebesgue_integral lborel U f =
    set_lebesgue_integral lborel U g"
proof -
  have ae_eq_lborel: "AE x in lborel. x \<in> U \<longrightarrow> f x = g x"
    using ae_eq measurable_U
    by (simp add: AE_restrict_space_iff)
  have ae_indicator:
      "AE x in lborel.
        indicator U x *\<^sub>R f x = indicator U x *\<^sub>R g x"
    using ae_eq_lborel by eventually_elim auto
  have measurable_f:
      "(\<lambda>x. indicator U x *\<^sub>R f x) \<in> borel_measurable lborel"
    using integrable_f borel_measurable_integrable
    unfolding set_integrable_def by blast
  have measurable_g:
      "(\<lambda>x. indicator U x *\<^sub>R g x) \<in> borel_measurable lborel"
    using integrable_g borel_measurable_integrable
    unfolding set_integrable_def by blast
  show ?thesis
    unfolding set_lebesgue_integral_def
    by (rule integral_cong_AE[OF measurable_f measurable_g ae_indicator])
qed

lemma slp_weak_form_cong_ae:
  assumes measurable_U: "U \<in> sets lborel"
    and F_eq: "slp_h1_data_ae_eq U F F'"
    and G_eq: "slp_h1_data_ae_eq U G G'"
    and V_eq: "slp_potential_ae_equal U V V'"
    and integrable_left: "slp_weak_form_integrable U V F G"
    and integrable_right: "slp_weak_form_integrable U V' F' G'"
  shows "slp_weak_form U V F G = slp_weak_form U V' F' G'"
proof -
  have F_eq_ae:
      "AE x in restrict_space lborel U.
        fst F x = fst F' x \<and> snd F x = snd F' x"
    using F_eq unfolding slp_h1_data_ae_eq_def .
  have G_eq_ae:
      "AE x in restrict_space lborel U.
        fst G x = fst G' x \<and> snd G x = snd G' x"
    using G_eq unfolding slp_h1_data_ae_eq_def .
  have V_eq_ae: "AE x in restrict_space lborel U. V x = V' x"
    using V_eq unfolding slp_potential_ae_equal_def .
  have gradient_ae:
      "AE x in restrict_space lborel U.
        (\<Sum>i\<in>UNIV. snd F x $ i * snd G x $ i) =
        (\<Sum>i\<in>UNIV. snd F' x $ i * snd G' x $ i)"
    using F_eq_ae G_eq_ae by eventually_elim auto
  have potential_ae:
      "AE x in restrict_space lborel U.
        V x * fst F x * fst G x = V' x * fst F' x * fst G' x"
    using F_eq_ae G_eq_ae V_eq_ae by eventually_elim auto
  have gradient_integrable_left:
      "set_integrable lborel U
        (\<lambda>x. \<Sum>i\<in>UNIV. snd F x $ i * snd G x $ i)"
    using integrable_left unfolding slp_weak_form_integrable_def by blast
  have gradient_integrable_right:
      "set_integrable lborel U
        (\<lambda>x. \<Sum>i\<in>UNIV. snd F' x $ i * snd G' x $ i)"
    using integrable_right unfolding slp_weak_form_integrable_def by blast
  have potential_integrable_left:
      "set_integrable lborel U (\<lambda>x. V x * fst F x * fst G x)"
    using integrable_left unfolding slp_weak_form_integrable_def by blast
  have potential_integrable_right:
      "set_integrable lborel U (\<lambda>x. V' x * fst F' x * fst G' x)"
    using integrable_right unfolding slp_weak_form_integrable_def by blast
  have gradient_integral:
      "set_lebesgue_integral lborel U
          (\<lambda>x. \<Sum>i\<in>UNIV. snd F x $ i * snd G x $ i) =
        set_lebesgue_integral lborel U
          (\<lambda>x. \<Sum>i\<in>UNIV. snd F' x $ i * snd G' x $ i)"
    by (rule slp_set_lebesgue_integral_cong_restrict_AE
          [OF measurable_U gradient_ae gradient_integrable_left
            gradient_integrable_right])
  have potential_integral:
      "set_lebesgue_integral lborel U
          (\<lambda>x. V x * fst F x * fst G x) =
        set_lebesgue_integral lborel U
          (\<lambda>x. V' x * fst F' x * fst G' x)"
    by (rule slp_set_lebesgue_integral_cong_restrict_AE
          [OF measurable_U potential_ae potential_integrable_left
            potential_integrable_right])
  show ?thesis
    using gradient_integral potential_integral
    unfolding slp_weak_form_def by simp
qed

corollary slp_weak_form_cong_h1_data_ae:
  assumes "U \<in> sets lborel"
    and "slp_h1_data_ae_eq U F F'"
    and "slp_h1_data_ae_eq U G G'"
    and "slp_weak_form_integrable U V F G"
    and "slp_weak_form_integrable U V F' G'"
  shows "slp_weak_form U V F G = slp_weak_form U V F' G'"
  by (rule slp_weak_form_cong_ae[OF assms(1-3)
        slp_potential_ae_equal_refl assms(4-5)])

corollary slp_weak_form_cong_potential_ae:
  assumes "U \<in> sets lborel"
    and "slp_potential_ae_equal U V V'"
    and "slp_weak_form_integrable U V F G"
    and "slp_weak_form_integrable U V' F G"
  shows "slp_weak_form U V F G = slp_weak_form U V' F G"
  by (rule slp_weak_form_cong_ae[OF assms(1)
        slp_h1_data_ae_eq_refl slp_h1_data_ae_eq_refl assms(2-4)])

end

