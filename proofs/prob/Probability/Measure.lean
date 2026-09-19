import Mathlib

open Set

namespace Probability

structure ProbabilityMeasure (Ω : Type*) where
  P : Set Ω → ℝ
  nonneg : ∀ A, P A ≥ 0 
  normal : P univ = 1
  -- TODO: convert finite additivity to countable additivity
  additive : ∀ ⦃A B⦄, Disjoint A B -> P (A ∪ B) = P A + P B

theorem ProbabilityMeasure.prob_empty_zero (M : ProbabilityMeasure Ω) : M.P ∅ = 0 := by
  have h := M.additive (disjoint_empty univ)

  rw [union_empty univ, M.normal] at h
  symm at h
  
  linarith only [h]

theorem ProbabilityMeasure.prob_subset_le (M : ProbabilityMeasure Ω) : A ⊆ B → (M.P A) ≤ (M.P B) := by
  intro h 

  let C := B \ A
  have had := M.additive
  have hdj : Disjoint A C := disjoint_sdiff_right
  specialize had hdj

  have hun : A ∪ C = B := union_sdiff_cancel h
  rw [hun] at had
  
  have hnn : M.P C ≥ 0 := M.nonneg C

  linarith only [had, hnn]

theorem ProbabilityMeasure.prob_ssubset_le (M : ProbabilityMeasure Ω) : A ⊂ B → (M.P A) ≤ (M.P B) := by
  intro h
  exact M.prob_subset_le h.subset

theorem ProbabilityMeasure.prob_le_one (M : ProbabilityMeasure Ω) : (M.P A) ≤ 1 := by
  have hun := subset_univ A
  have hlq := M.prob_subset_le hun
  rw [M.normal] at hlq
  exact hlq

theorem ProbabilityMeasure.prob_bt_zero_one (M : ProbabilityMeasure Ω) : 0 ≤ (M.P A) ∧ (M.P A) ≤ 1 := by
  constructor 
  · have h := M.nonneg A
    exact h
  · apply M.prob_le_one

theorem ProbabilityMeasure.prob_compl_eq_one_sub (M : ProbabilityMeasure Ω) : M.P Aᶜ = 1 - M.P A := by
  have hd : Disjoint A Aᶜ := disjoint_compl_right

  have ha : M.P A + M.P Aᶜ = 1 := by
    have h := M.additive hd
    rw [union_compl_self, M.normal] at h
    symm at h
    exact h

  linarith only [ha]

theorem ProbabilityMeasure.prob_union_eq_add_disjoint (M : ProbabilityMeasure Ω) (h : A ∩ B = ∅) :
    M.P (A ∪ B) = M.P A + M.P B := by
  rw [← disjoint_iff_inter_eq_empty] at h
  exact M.additive h

