theory Hormander_Quadratic_Stationary_Phase_Interface
  imports
    "HOL-Analysis.Analysis"
    "Smooth_Manifolds.Smooth"
begin

section \<open>Quadratic stationary-phase decay\<close>

definition hormander_compact_smooth_amplitude ::
  "(real^'n::finite \<Rightarrow> complex) \<Rightarrow> bool"
where
  "hormander_compact_smooth_amplitude u \<longleftrightarrow>
    smooth_on UNIV u \<and>
    compact (closure {x. u x \<noteq> 0}) \<and>
    integrable lborel u"

definition hormander_real_symmetric_matrix ::
  "(real^'n::finite^'n) \<Rightarrow> bool"
where
  "hormander_real_symmetric_matrix A \<longleftrightarrow>
    (\<forall>i j. A $ i $ j = A $ j $ i)"

definition hormander_real_nondegenerate_matrix ::
  "(real^'n::finite^'n) \<Rightarrow> bool"
where
  "hormander_real_nondegenerate_matrix A \<longleftrightarrow>
    (\<forall>x. A *v x = 0 \<longrightarrow> x = 0)"

definition hormander_quadratic_oscillatory_integral ::
  "(real^'n::finite^'n) \<Rightarrow> (real^'n \<Rightarrow> complex) \<Rightarrow>
    real \<Rightarrow> complex"
where
  "hormander_quadratic_oscillatory_integral A u omega =
    integral\<^sup>L lborel
      (\<lambda>x. exp (\<i> * of_real
        (omega * inner x (A *v x) / 2)) * u x)"

definition hormander_quadratic_stationary_phase_decay_claim ::
  "'n::finite itself \<Rightarrow> bool"
where
  "hormander_quadratic_stationary_phase_decay_claim dimension_type \<longleftrightarrow>
    (\<forall>(A :: real^'n^'n) u.
      hormander_real_symmetric_matrix A \<and>
      hormander_real_nondegenerate_matrix A \<and>
      hormander_compact_smooth_amplitude u
      \<longrightarrow>
      ((\<lambda>omega. hormander_quadratic_oscillatory_integral A u omega)
        \<longlongrightarrow> 0) at_top)"

text \<open>
  This is the real-matrix, compactly supported smooth, limit-only consequence
  of Hoermander's 1983 Lemma 7.7.3, equation (7.7.7).  The explicit
  integrability conjunct prevents accidental use of Isabelle's totalized
  Bochner integral outside the ordinary source integral.  Isabelle types are
  nonempty, so a finite coordinate type has positive dimension, as required
  for the determinant factor to decay.
\<close>

locale hormander_quadratic_stationary_phase_decay =
  fixes dimension_type :: "'n::finite itself"
  assumes hormander_quadratic_stationary_phase_decay:
    "hormander_quadratic_stationary_phase_decay_claim dimension_type"

end
