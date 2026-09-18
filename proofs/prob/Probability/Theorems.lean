import Mathlib
import Probability.Axioms

open Set

namespace Probability

-- TODO: convert to structure
variable (Ω : Type _)
variable (A B : Set Ω)
variable (P : Set Ω → ℝ)

theorem nothing_never_happens : P ∅ = 0 := by
  have h := additive Ω univ ∅ P
  specialize h (disjoint_empty univ)

  rw [union_empty univ, normalized Ω P] at h
  symm at h
  
  linarith only [h]

theorem prob_subset_leq : A ⊆ B → (P A) ≤ (P B) := by
  intro h 

  let C := B \ A
  have had := additive Ω A C P
  have hdj : Disjoint A C := disjoint_sdiff_right
  specialize had hdj

  have hun : A ∪ C = B := union_sdiff_cancel h
  rw [hun] at had
  
  have hnn : P C ≥ 0 := nonnegative Ω P C

  linarith only [had, hnn]

theorem prob_ssubset_leq : A ⊂ B → (P A) ≤ (P B) := by
  intro h
  apply subset_of_ssubset at h
  exact prob_subset_leq Ω A B P h

lemma prob_leq_one : (P A) ≤ 1 := by
  have h := prob_subset_leq Ω A univ P
  specialize h (subset_univ A)
  rw [normalized Ω P] at h
  exact h

theorem prob_bt_zero_one : 0 ≤ (P A) ∧ (P A) ≤ 1 := by
  constructor 
  · have h := nonnegative Ω P A
    rw [← ge_iff_le]
    exact h
  · apply prob_leq_one Ω A P

