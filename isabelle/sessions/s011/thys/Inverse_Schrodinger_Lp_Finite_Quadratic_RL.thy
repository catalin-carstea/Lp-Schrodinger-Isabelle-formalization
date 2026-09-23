theory Inverse_Schrodinger_Lp_Finite_Quadratic_RL
  imports Inverse_Schrodinger_Lp_Quadratic_RL_Passive_Affine
begin

section \<open>Finite quadratic Riemann--Lebesgue lemma\<close>

text \<open>
  This is the explicit post-separation analytic content of official Lemma
  @{text "lem-quadratic-RL"}.  The passive center is represented by
  @{typ "real^'c"}; the nonempty finite coordinate type @{typ 'n} gives the
  required positive-dimensional active fiber.  The fixed symmetric matrix is
  the active Hessian, while @{term b} and @{term p0} expose the passive-dependent
  linear and scalar terms described in the expanded proof.  The later
  original-coordinate instantiation must separately supply the fixed affine
  coordinate map and its nonzero Jacobian.
\<close>

context hormander_quadratic_stationary_phase_decay
begin

theorem slp_finite_quadratic_riemann_lebesgue:
  fixes A :: "real^'n::finite^'n"
    and b :: "real^'c::finite \<Rightarrow> real^'n"
    and p0 :: "real^'c \<Rightarrow> real"
    and F :: "real^'c \<Rightarrow> real^'n \<Rightarrow> complex"
  assumes density:
      "evans_compact_smooth_l1_density_claim TYPE('n)"
    and symmetric: "hormander_real_symmetric_matrix A"
    and nondegenerate: "hormander_real_nondegenerate_matrix A"
    and b_measurable: "b \<in> borel_measurable lborel"
    and p0_measurable: "p0 \<in> borel_measurable lborel"
    and F_integrable: "integrable lborel (case_prod F)"
  shows
    "((\<lambda>omega. integral\<^sup>L lborel
        (\<lambda>(c, u). exp (\<i> * of_real
          (omega * (inner u (A *v u) / 2 +
            inner (b c) u + p0 c))) * F c u))
      \<longlongrightarrow> 0) at_top"
proof -
  have F_integrable_product:
    "integrable (lborel \<Otimes>\<^sub>M lborel) (case_prod F)"
    using F_integrable by (simp only: lborel_prod)
  have decay_product:
    "((\<lambda>omega. integral\<^sup>L (lborel \<Otimes>\<^sub>M lborel)
        (\<lambda>(c, u). exp (\<i> * of_real
          (omega * (inner u (A *v u) / 2 +
            inner (b c) u + p0 c))) * F c u))
      \<longlongrightarrow> 0) at_top"
    by (rule slp_passive_affine_quadratic_decay[
      OF density symmetric nondegenerate b_measurable p0_measurable
        F_integrable_product])
  show ?thesis
    using decay_product by (simp only: lborel_prod)
qed

end

end
