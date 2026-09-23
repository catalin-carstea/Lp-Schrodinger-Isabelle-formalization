theory Inverse_Schrodinger_Lp_Setup
  imports
    "HOL-Analysis.Analysis"
    "Smooth_Manifolds.Smooth"
begin

section \<open>Planar domain and scalar fields\<close>

text \<open>
  The manuscript identifies the Euclidean plane with the complex plane.  The
  point type remains real and scalar fields are complex valued.
\<close>

type_synonym slp_point = "real ^ 2"
type_synonym slp_scalar_field = "slp_point \<Rightarrow> complex"
type_synonym slp_gradient_field = "slp_point \<Rightarrow> complex ^ 2"
type_synonym slp_h1_data = "slp_scalar_field \<times> slp_gradient_field"

definition slp_smooth_boundary_at ::
  "slp_point set \<Rightarrow> slp_point \<Rightarrow> bool"
where
  "slp_smooth_boundary_at D x \<longleftrightarrow>
    (\<exists>(U :: slp_point set) (W :: slp_point set)
       (f :: slp_point \<Rightarrow> slp_point)
       (g :: slp_point \<Rightarrow> slp_point) (i :: 2).
      open U \<and> open W \<and> x \<in> U \<and>
      homeomorphism U W f g \<and>
      smooth_on U f \<and> smooth_on W g \<and>
      f ` (D \<inter> U) = W \<inter> {y. 0 < y $ i})"

definition slp_bounded_smooth_domain :: "slp_point set \<Rightarrow> bool"
where
  "slp_bounded_smooth_domain D \<longleftrightarrow>
    D \<noteq> {} \<and> open D \<and> connected D \<and> bounded D \<and>
    (\<forall>x\<in>frontier D. slp_smooth_boundary_at D x)"

section \<open>Complex Sobolev representatives\<close>

definition slp_complex_partial_derivative ::
  "slp_scalar_field \<Rightarrow> 2 \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_complex_partial_derivative phi i x =
    frechet_derivative phi (at x) (axis i 1)"

definition slp_classical_gradient ::
  "slp_scalar_field \<Rightarrow> slp_gradient_field"
where
  "slp_classical_gradient phi x =
    (\<chi> i. slp_complex_partial_derivative phi i x)"

definition slp_test_function_on ::
  "slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow> bool"
where
  "slp_test_function_on U phi \<longleftrightarrow>
    smooth_on UNIV phi \<and>
    compact (closure {x. phi x \<noteq> 0}) \<and>
    closure {x. phi x \<noteq> 0} \<subseteq> U"

definition slp_weak_gradient_on ::
  "slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_gradient_field \<Rightarrow> bool"
where
  "slp_weak_gradient_on U u Du \<longleftrightarrow>
    (\<forall>phi. slp_test_function_on U phi \<longrightarrow>
      (\<forall>i.
        set_integrable lborel U
          (\<lambda>x. u x * slp_complex_partial_derivative phi i x) \<and>
        set_integrable lborel U (\<lambda>x. Du x $ i * phi x) \<and>
        set_lebesgue_integral lborel U
          (\<lambda>x. u x * slp_complex_partial_derivative phi i x) =
        - set_lebesgue_integral lborel U (\<lambda>x. Du x $ i * phi x)))"

definition slp_h1_pair_on ::
  "slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_gradient_field \<Rightarrow> bool"
where
  "slp_h1_pair_on U u Du \<longleftrightarrow>
    u \<in> borel_measurable (restrict_space lborel U) \<and>
    Du \<in> borel_measurable (restrict_space lborel U) \<and>
    slp_weak_gradient_on U u Du \<and>
    set_integrable lborel U (\<lambda>x. norm (u x) ^ 2) \<and>
    set_integrable lborel U (\<lambda>x. norm (Du x) ^ 2)"

definition slp_h1_data_on :: "slp_point set \<Rightarrow> slp_h1_data \<Rightarrow> bool"
where
  "slp_h1_data_on U F \<longleftrightarrow>
    slp_h1_pair_on U (fst F) (snd F)"

definition slp_h1_squared_distance ::
  "slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_gradient_field \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_gradient_field \<Rightarrow> real"
where
  "slp_h1_squared_distance U u Du v Dv =
    set_lebesgue_integral lborel U
      (\<lambda>x. norm (u x - v x) ^ 2 + norm (Du x - Dv x) ^ 2)"

definition slp_h1_zero_pair_on ::
  "slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_gradient_field \<Rightarrow> bool"
where
  "slp_h1_zero_pair_on U u Du \<longleftrightarrow>
    slp_h1_pair_on U u Du \<and>
    (\<exists>seq :: nat \<Rightarrow> slp_scalar_field.
      (\<forall>m. slp_test_function_on U (seq m) \<and>
        slp_h1_pair_on U (seq m) (slp_classical_gradient (seq m))) \<and>
      (\<forall>epsilon>0. \<exists>N. \<forall>m\<ge>N.
        slp_h1_squared_distance U (seq m)
          (slp_classical_gradient (seq m)) u Du < epsilon))"

definition slp_h1_zero_data_on ::
  "slp_point set \<Rightarrow> slp_h1_data \<Rightarrow> bool"
where
  "slp_h1_zero_data_on U F \<longleftrightarrow>
    slp_h1_zero_pair_on U (fst F) (snd F)"

definition slp_h1_data_ae_eq ::
  "slp_point set \<Rightarrow> slp_h1_data \<Rightarrow> slp_h1_data \<Rightarrow> bool"
where
  "slp_h1_data_ae_eq U F G \<longleftrightarrow>
    (AE x in restrict_space lborel U.
      fst F x = fst G x \<and> snd F x = snd G x)"

definition slp_same_trace ::
  "slp_point set \<Rightarrow> slp_h1_data \<Rightarrow> slp_h1_data \<Rightarrow> bool"
where
  "slp_same_trace U F G \<longleftrightarrow>
    slp_h1_zero_data_on U
      ((\<lambda>x. fst F x - fst G x), (\<lambda>x. snd F x - snd G x))"

section \<open>Weak Schr\<ouml>dinger operator and Dirichlet data\<close>

definition slp_complex_lp_on ::
  "real \<Rightarrow> slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow> bool"
where
  "slp_complex_lp_on p U V \<longleftrightarrow>
    V \<in> borel_measurable (restrict_space lborel U) \<and>
    set_integrable lborel U (\<lambda>x. norm (V x) powr p)"

definition slp_weak_form_integrable ::
  "slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_h1_data \<Rightarrow> slp_h1_data \<Rightarrow> bool"
where
  "slp_weak_form_integrable U V F G \<longleftrightarrow>
    set_integrable lborel U
      (\<lambda>x. \<Sum>i\<in>UNIV. snd F x $ i * snd G x $ i) \<and>
    set_integrable lborel U
      (\<lambda>x. V x * fst F x * fst G x)"

definition slp_weak_form ::
  "slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_h1_data \<Rightarrow> slp_h1_data \<Rightarrow> complex"
where
  "slp_weak_form U V F G =
    set_lebesgue_integral lborel U
      (\<lambda>x. \<Sum>i\<in>UNIV. snd F x $ i * snd G x $ i) +
    set_lebesgue_integral lborel U
      (\<lambda>x. V x * fst F x * fst G x)"

definition slp_weak_solution ::
  "slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_h1_data \<Rightarrow> bool"
where
  "slp_weak_solution U V F \<longleftrightarrow>
    slp_h1_data_on U F \<and>
    (\<forall>G. slp_h1_zero_data_on U G \<longrightarrow>
      slp_weak_form_integrable U V F G \<and>
      slp_weak_form U V F G = 0)"

definition slp_zero_not_dirichlet_eigenvalue ::
  "slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow> bool"
where
  "slp_zero_not_dirichlet_eigenvalue U V \<longleftrightarrow>
    (\<forall>F. slp_h1_zero_data_on U F \<and> slp_weak_solution U V F
      \<longrightarrow> slp_h1_data_ae_eq U F ((\<lambda>_. 0), (\<lambda>_. 0)))"

definition slp_is_weak_dirichlet_solution ::
  "slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_h1_data \<Rightarrow> slp_h1_data \<Rightarrow> bool"
where
  "slp_is_weak_dirichlet_solution U V boundary solution \<longleftrightarrow>
    slp_h1_data_on U boundary \<and>
    slp_weak_solution U V solution \<and>
    slp_same_trace U solution boundary"

definition slp_selected_dirichlet_solution ::
  "slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_h1_data \<Rightarrow> slp_h1_data"
where
  "slp_selected_dirichlet_solution U V boundary =
    (SOME solution. slp_is_weak_dirichlet_solution U V boundary solution)"

definition slp_weak_dn_form ::
  "slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_h1_data \<Rightarrow> slp_h1_data \<Rightarrow> complex"
where
  "slp_weak_dn_form U V F G =
    slp_weak_form U V (slp_selected_dirichlet_solution U V F) G"

definition slp_weak_dn_equal ::
  "slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field \<Rightarrow> bool"
where
  "slp_weak_dn_equal U V V_tilde \<longleftrightarrow>
    (\<forall>F G. slp_h1_data_on U F \<and> slp_h1_data_on U G
      \<longrightarrow> slp_weak_dn_form U V F G =
        slp_weak_dn_form U V_tilde F G)"

definition slp_potential_ae_equal ::
  "slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field \<Rightarrow> bool"
where
  "slp_potential_ae_equal U V V_tilde \<longleftrightarrow>
    (AE x in restrict_space lborel U. V x = V_tilde x)"

end
