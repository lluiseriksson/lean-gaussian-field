import Interfaces

open scoped BigOperators
open GaussianField

namespace GaussianExistenceChecks

-- Nonzero singular covariance, with nonzero mean: no density or inverse is available.
noncomputable def rankOne : GaussianVectorSpec (Fin 2) where
  mean := ![2, -1]
  covariance := fun _ _ => 1
  covariance_symm := by intros; rfl
  covariance_psd := by
    intro t
    simp only [quadraticForm, Fin.sum_univ_two, mul_one]
    nlinarith [sq_nonneg (t 0 + t 1)]

theorem rankOne_has_kernel :
    (![1, -1] : Fin 2 → ℝ) ≠ 0 ∧
      quadraticForm rankOne.covariance ![1, -1] = 0 := by
  constructor
  · intro h
    have := congrFun h 0
    norm_num at this
  · norm_num [quadraticForm, rankOne, Fin.sum_univ_two]

theorem rankOne_realized : ∃ μ, HasGaussianVectorLaw rankOne μ :=
  exists_gaussian_law rankOne

-- Empty finite products are admitted; no hidden nonempty-index premise.
theorem empty_realized (spec : GaussianVectorSpec (Fin 0)) :
    ∃ μ, HasGaussianVectorLaw spec μ := exists_gaussian_law spec

#print axioms GaussianExistenceChecks.rankOne_realized
#print axioms GaussianExistenceChecks.rankOne_has_kernel
#print axioms GaussianExistenceChecks.empty_realized
end GaussianExistenceChecks
