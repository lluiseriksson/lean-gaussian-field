import LeanGaussianField.GaussianVector

open GaussianField MeasureTheory

example : HasGaussianVectorLaw (GaussianVectorSpec.zero (Fin 1))
    (Measure.dirac (0 : Fin 1 → ℝ)) := HasGaussianVectorLaw.zero_dirac

example : ¬ HasGaussianVectorLaw (GaussianVectorSpec.zero (Fin 1))
    (0 : Measure (Fin 1 → ℝ)) := by
  intro h
  have hm := h.probability.measure_univ
  simp at hm

example : ¬ HasGaussianVectorLaw (GaussianVectorSpec.zero (Fin 1))
    (Measure.dirac (fun _ : Fin 1 => (1 : ℝ))) := by
  intro h
  have hi : (fun _ : Fin 1 => (1 : ℝ)) ≠ (0 : Fin 1 → ℝ) := by
    intro heq
    have heq0 := congrFun heq 0
    norm_num at heq0
  have heq := h.ext HasGaussianVectorLaw.zero_dirac
  have hm := congrArg (fun μ : Measure (Fin 1 → ℝ) => μ {0}) heq
  simp [hi] at hm

#print axioms GaussianField.dualCoordinates_apply
#print axioms GaussianField.HasGaussianVectorLaw.ext
#print axioms GaussianField.HasGaussianVectorLaw.zero_dirac
