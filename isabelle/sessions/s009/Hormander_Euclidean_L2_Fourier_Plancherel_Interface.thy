theory Hormander_Euclidean_L2_Fourier_Plancherel_Interface
  imports "HOL-Analysis.Analysis"
begin

section \<open>Planar L2 Fourier realization, Plancherel, and inversion\<close>

type_synonym hormander_fourier_point = "real ^ 2"
type_synonym hormander_fourier_field =
  "hormander_fourier_point \<Rightarrow> complex"

definition hormander_fourier_l2_on_plane ::
  "hormander_fourier_field \<Rightarrow> bool"
where
  "hormander_fourier_l2_on_plane f \<longleftrightarrow>
    f \<in> borel_measurable lborel \<and>
    integrable lborel (\<lambda>x. norm (f x) ^ 2)"

definition hormander_fourier_phase ::
  "hormander_fourier_point \<Rightarrow> hormander_fourier_point \<Rightarrow>
    complex"
where
  "hormander_fourier_phase xi x =
    exp (\<i> * of_real (- inner x xi))"

definition hormander_fourier_l1_transform ::
  "hormander_fourier_field \<Rightarrow> hormander_fourier_field"
where
  "hormander_fourier_l1_transform f xi =
    integral\<^sup>L lborel (\<lambda>x. hormander_fourier_phase xi x * f x)"

definition hormander_euclidean_l2_fourier_plancherel_claim :: bool
where
  "hormander_euclidean_l2_fourier_plancherel_claim \<longleftrightarrow>
    (\<exists>fourier_l2 :: hormander_fourier_field \<Rightarrow>
        hormander_fourier_field.
      (\<forall>f. hormander_fourier_l2_on_plane f \<longrightarrow>
        hormander_fourier_l2_on_plane (fourier_l2 f)) \<and>
      (\<forall>f. hormander_fourier_l2_on_plane f \<and> integrable lborel f
        \<longrightarrow> (AE xi in lborel.
          fourier_l2 f xi = hormander_fourier_l1_transform f xi)) \<and>
      (\<forall>f. hormander_fourier_l2_on_plane f \<longrightarrow>
        integral\<^sup>L lborel (\<lambda>xi. norm (fourier_l2 f xi) ^ 2) =
          (2 * pi) ^ 2 *
            integral\<^sup>L lborel (\<lambda>x. norm (f x) ^ 2)) \<and>
      (\<forall>f. hormander_fourier_l2_on_plane f \<longrightarrow>
        (AE x in lborel.
          fourier_l2 (fourier_l2 f) x =
            of_real ((2 * pi) ^ 2) * f (-x))))"

text \<open>
  This is the two-dimensional, norm-Plancherel and almost-everywhere inversion
  consequence of Hoermander's Definition 7.1.1, formula (7.1.8), and
  Theorems 7.1.10--7.1.11.  The forward L1 convention is the unnormalised
  integral with exponential exp(-i<x,xi>), so Parseval and the double transform
  carry the factor (2*pi)^2.  The existential operator represents the L2
  Fourier transform on measurable representatives; no value is constrained
  outside the explicit L2 class.
\<close>

locale hormander_euclidean_l2_fourier_plancherel =
  assumes hormander_euclidean_l2_fourier_plancherel:
    hormander_euclidean_l2_fourier_plancherel_claim

end
