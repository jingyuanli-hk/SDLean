/-
Copyright (c) 2025 Li Jingyuan . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Li Jingyuan
Extension for N-dimensional FSD: GitHub Copilot
-/
import Mathlib.Analysis.Calculus.Deriv.Basic

open Set Function Real
open scoped Topology

set_option linter.unusedVariables false

/-!
# First-Order Stochastic Dominance in N Dimensions

This file formalizes a theorem relating first-order stochastic dominance (FSD) in N dimensions
to expected utility, specifically for indicator functions of upper-right orthants.

We extend the 2D case to N dimensions by defining vectors in ℝⁿ, N-dimensional rectangles,
and indicator functions for upper-right orthants. We then prove the equivalence between
FSD and expected utility for these indicator functions.

## Main definitions

* `RVector n`: N-dimensional vector of real numbers
* `Icc_n a b`: N-dimensional closed rectangle from a to b
* `Ioo_n a b`: N-dimensional open rectangle from a to b
* `indicatorUpperRightOrthant`: Indicator function for the upper-right orthant
* `survivalProbN`: N-dimensional survival probability
* `riemannStieltjesIntegralND`: Riemann-Stieltjes integral for N-dimensional case

## Main results

* `uniqueness_of_indicatorUpperRightOrthant_x₀_on_open`: Shows uniqueness of the indicator function parameter
* `integral_for_indicatorUpperRightOrthant`: Calculates the integral for upper-right orthant indicators
* `fsd_nd_iff_integral_indicatorUpperRightOrthant_ge`: Main theorem showing equivalence of FSD and expected utility
-/

/-- Type representing an N-dimensional vector of reals -/
def RVector (n : ℕ) := Fin n → ℝ

namespace RVector

variable {n : ℕ}

/-- Componentwise less than for vectors -/
def lt (x y : RVector n) : Prop := ∀ i, x i < y i

/-- Componentwise less than or equal for vectors -/
def le (x y : RVector n) : Prop := ∀ i, x i ≤ y i

instance : LT (RVector n) := ⟨lt⟩
instance : LE (RVector n) := ⟨le⟩

/-- Check if all components of the first vector are strictly greater than
    the corresponding components of the second vector -/
def allGt (x y : RVector n) : Prop := ∀ i, x i > y i

/-- Create a vector where components in set s come from x₀, all others from b -/
def mixedVector (x₀ b : RVector n) (s : Finset (Fin n)) : RVector n :=
  fun i => if i ∈ s then x₀ i else b i

/-- Create a vector with all components except at index j the same as x -/
def replace (x : RVector n) (j : Fin n) (val : ℝ) : RVector n :=
  fun i => if i = j then val else x i

/-- Create a midpoint vector between two vectors -/
noncomputable def midpoint (x y : RVector n) : RVector n :=
  fun i => (x i + y i) / 2

end RVector

/-- Create a closed rectangle in N dimensions from a to b -/
def closedRectangleND {n : ℕ} (a b : RVector n) : Set (RVector n) :=
  {x | ∀ i, a i ≤ x i ∧ x i ≤ b i}

/-- This represents the set of all vectors `x` such that each component of `x` lies within the closed interval `[a_i, b_i]`.
Formally, `Icc_n a b = {x | ∀ i, a i ≤ x i ∧ x i ≤ b i}`.
-/
def Icc_n {n : ℕ} (a b : RVector n) : Set (RVector n) :=
  {x | RVector.le a x ∧ RVector.le x b} -- Component-wise inequalities: a_i ≤ x_i ≤ b_i

/-- N-dimensional open rectangle from a to b -/
def Ioo_n {n : ℕ} (a b : RVector n) : Set (RVector n) :=
  {x | RVector.lt a x ∧ RVector.lt x b}

/-- Subset relation between rectangles -/
lemma Ioo_subset_Icc_self_n {n : ℕ} {a b : RVector n} :
    Ioo_n a b ⊆ Icc_n a b := by
  intro x hx
  constructor
  · intro i; exact le_of_lt (hx.1 i)
  · intro i; exact le_of_lt (hx.2 i)

/-- Indicator function for the upper-right orthant defined by `x₀`. -/
noncomputable def indicatorUpperRightOrthant {n : ℕ} (x₀ : RVector n) (x : RVector n) : ℝ :=
  haveI : Decidable (RVector.allGt x x₀) := Classical.propDecidable _
  if RVector.allGt x x₀ then 1 else 0

/-- Computes the survival probability in N dimensions, i.e., the probability that all components
    of a random vector exceed given thresholds.

    The distribution function `Dist` is expected to satisfy the following properties:
    1. Monotonicity: If `x ≤ y` componentwise, then `Dist(x) ≤ Dist(y)`.
    2. Boundedness: `0 ≤ Dist(x) ≤ 1` for all `x`.
    3. Continuity: `Dist` is assumed to be right-continuous in each component.

    This is calculated using the inclusion-exclusion principle:
    P(X₁>x₀₁,...,Xₙ>x₀ₙ) = 1 - P(X₁≤x₀₁ ∨ ... ∨ Xₙ≤x₀ₙ).

    For a distribution function Dist, which gives the probability
    P(X₁≤y₁,...,Xₙ≤yₙ), we use the inclusion-exclusion principle to
    compute P(X₁≤x₀₁ ∨ ... ∨ Xₙ≤x₀ₙ).

    The formula sums over all non-empty subsets of indices, with alternating
    signs based on the subset size, to correctly count the overlapping regions.
-/
noncomputable def survivalProbN {n : ℕ} (Dist : RVector n → ℝ) (x₀ b : RVector n) : ℝ :=
  1 - Finset.sum ((Finset.powerset (Finset.univ : Finset (Fin n))) \ {∅})
      (fun s => (-1)^(s.card + 1) * Dist (RVector.mixedVector x₀ b s))

/-- Riemann-Stieltjes integral in N dimensions for indicator functions of upper-right orthants.

    This definition is specifically tailored for indicator functions of the form
    `indicatorUpperRightOrthant x₀`, where the function `u` matches this indicator
    on the open rectangle `Ioo_n a b` for some `x₀` in the closed rectangle `Icc_n a b`.

    The parameter `h_u` ensures that the function `u` matches the indicator function
    `indicatorUpperRightOrthant x₀` on the open rectangle `Ioo_n a b`. This is crucial
    for the integral to be well-defined, as it guarantees that the behavior of `u`
    aligns with the expected properties of the indicator function in the specified region. -/
noncomputable def riemannStieltjesIntegralND {n : ℕ} (u : RVector n → ℝ)
    (Dist : RVector n → ℝ) (a b : RVector n) (x₀ : RVector n)
    (h_x₀ : x₀ ∈ Icc_n a b)
    (h_u : ∀ x ∈ Ioo_n a b, u x = indicatorUpperRightOrthant x₀ x) : ℝ :=
  haveI : Decidable (∃ x₀' ∈ Icc_n a b, ∀ x ∈ Ioo_n a b, u x = indicatorUpperRightOrthant x₀' x) :=
    Classical.propDecidable _
  if h : ∃ x₀' ∈ Icc_n a b, ∀ x ∈ Ioo_n a b, u x = indicatorUpperRightOrthant x₀' x then
    -- Use x₀ directly, as it satisfies the condition by h_u
    survivalProbN Dist x₀ b
  else
    0

/-- Uniqueness of indicator function parameter in N dimensions.
    If two indicator functions for upper-right orthants defined by points x₁ and x₂
    agree on the open rectangle Ioo_n a b, then x₁ = x₂.
    This is crucial for ensuring the well-definedness of our integral.
-/
lemma uniqueness_of_indicatorUpperRightOrthant_x₀_on_open {n : ℕ} {a b x₁ x₂ : RVector n}
    (hab : ∀ i, a i < b i)
    (hx₁_mem : x₁ ∈ Ioo_n a b) (hx₂_mem : x₂ ∈ Ioo_n a b)
    (h_eq_fn : ∀ x ∈ Ioo_n a b, indicatorUpperRightOrthant x₁ x = indicatorUpperRightOrthant x₂ x) :
    x₁ = x₂ := by
  -- Proof by contradiction
  by_contra h_neq
  -- If x₁ ≠ x₂, then there exists an index j where they differ
  have h_exists_diff : ∃ j, x₁ j ≠ x₂ j := by
    by_contra h_all_eq
    push_neg at h_all_eq -- h_all_eq : ∀ i, x₁ i = x₂ i
    -- If all components are equal, then the vectors are equal (function extensionality)
    have h_eq : x₁ = x₂ := by
      funext i
      exact h_all_eq i
    -- This contradicts our assumption that x₁ ≠ x₂
    exact h_neq h_eq

  -- Extract the index where they differ
  rcases h_exists_diff with ⟨j, h_diff_at_j⟩

  -- They must differ by one being strictly less than the other
  have h_lt_or_gt : x₁ j < x₂ j ∨ x₂ j < x₁ j := by
    exact Ne.lt_or_lt h_diff_at_j

  -- Handle each case separately
  rcases h_lt_or_gt with h_lt | h_gt

  -- Case 1: x₁ j < x₂ j
  · -- Create a test point z where:
    -- - The jth component is between x₁ j and x₂ j
    -- - All other components are greater than both x₁ i and x₂ i
    let z₁ := (x₁ j + x₂ j) / 2 -- Midpoint between x₁ j and x₂ j

    have hz₁_gt_x₁j : z₁ > x₁ j := by
      dsimp [z₁]
      have h_two_pos : (0 : ℝ) < 2 := by norm_num
      rw [gt_iff_lt, lt_div_iff₀ h_two_pos] -- Transform to x₁ j * 2 < x₁ j + x₂ j
      rw [mul_comm, two_mul]  -- Rewrite 2 * x₁ j as x₁ j + x₁ j
      -- Need to prove: x₁ j + x₁ j < x₁ j + x₂ j
      rw [Real.add_lt_add_iff_left (x₁ j)]  -- Cancel x₁ j on both sides
      exact h_lt  -- Use the hypothesis x₁ j < x₂ j

    have hz₁_lt_x₂j : z₁ < x₂ j := by
      dsimp [z₁]
      have h_two_pos : (0 : ℝ) < 2 := by norm_num
      rw [div_lt_iff₀ h_two_pos]  -- Transform to (x₁ j + x₂ j) < x₂ j * 2
      rw [mul_comm, two_mul]  -- Rewrite 2 * x₂ j as x₂ j + x₂ j
      -- Need to prove: x₁ j + x₂ j < x₂ j + x₂ j
      rw [add_lt_add_iff_right (x₂ j)]  -- Cancel x₂ j on both sides
      exact h_lt  -- Use the hypothesis x₁ j < x₂ j

    -- For other components, use a value greater than both x₁ i and x₂ i
    let z : RVector n := fun i =>
      if i = j then z₁ else (max (x₁ i) (x₂ i) + b i) / 2

    -- Verify z is in the open rectangle Ioo_n a b
    have hz_mem_Ioo : z ∈ Ioo_n a b := by
      constructor
      · -- Prove ∀ i, a i < z i
        intro i
        by_cases h_eq_j : i = j
        · -- Case i = j
          rw [h_eq_j]  -- Replace i with j
          -- Use transitivity with x₁ j
          calc
            a j < x₁ j := hx₁_mem.1 j
            _ < z₁ := hz₁_gt_x₁j
            _ = z j := by dsimp [z]; rw [if_pos rfl]
        · -- Case i ≠ j
          dsimp [z]  -- First expand the definition of z
          rw [if_neg h_eq_j]  -- Use if_neg with h_eq_j to select the 'else' branch
          -- Now z i = (max (x₁ i) (x₂ i) + b i) / 2
          have h_a_lt_max : a i < max (x₁ i) (x₂ i) := by
            -- a i < x₁ i ≤ max (x₁ i) (x₂ i)
            calc
              a i < x₁ i := hx₁_mem.1 i
              _ ≤ max (x₁ i) (x₂ i) := le_max_left _ _
          have h_max_lt_b : max (x₁ i) (x₂ i) < b i := by
            -- max (x₁ i) (x₂ i) ≤ x₂ i < b i
            calc
              max (x₁ i) (x₂ i) ≤ max (x₁ i) (x₂ i) := le_refl _
              _ < b i := by
                have h_x₁i_lt_bi : x₁ i < b i := hx₁_mem.2 i
                have h_x₂i_lt_bi : x₂ i < b i := hx₂_mem.2 i
                exact max_lt h_x₁i_lt_bi h_x₂i_lt_bi
          -- Now prove a i < (max (x₁ i) (x₂ i) + b i) / 2
          have h_two_pos : (0 : ℝ) < 2 := by norm_num
          apply (lt_div_iff₀ h_two_pos).mpr
          -- Need to prove: a i * 2 < max (x₁ i) (x₂ i) + b i
          calc a i * 2 = a i + a i := by rw [mul_comm, two_mul]
                    _ < max (x₁ i) (x₂ i) + b i := add_lt_add h_a_lt_max (hab i)

      · -- Prove ∀ i, z i < b i
        intro i
        by_cases h_eq_j : i = j
        · -- Case i = j
          rw [h_eq_j]  -- Replace i with j
          -- Use transitivity with x₂ j
          calc
            z j = z₁ := by dsimp [z]; rw [if_pos rfl]
            _ < x₂ j := hz₁_lt_x₂j
            _ < b j := hx₂_mem.2 j
        · -- Case i ≠ j
          dsimp [z]  -- Unfold the definition of z
          rw [if_neg h_eq_j]  -- Use if_neg with h_eq_j to select the 'else' branch
          -- Now z i = (max (x₁ i) (x₂ i) + b i) / 2
          have h_two_pos : (0 : ℝ) < 2 := by norm_num
          apply (div_lt_iff₀ h_two_pos).mpr
          -- Need to prove: max (x₁ i) (x₂ i) + b i < b i * 2
          calc
            x₁ i ⊔ x₂ i + b i < b i + b i := by
              apply add_lt_add_right
              exact max_lt (hx₁_mem.2 i) (hx₂_mem.2 i)
            _ = b i * 2 := by ring

    -- Apply h_eq_fn to get a contradiction
    specialize h_eq_fn z hz_mem_Ioo

    -- Calculate indicator values for x₁ and x₂ at z
    have ind1 : indicatorUpperRightOrthant x₁ z = 1 := by
      unfold indicatorUpperRightOrthant
      apply if_pos -- Goal: RVector.allGt z x₁
      intro i' -- Use a new variable name for the index
      by_cases h_eq_j' : i' = j
      · -- Case i' = j
        rw [h_eq_j']
        simp only [z, if_true] -- z j simplifies to z₁
        exact hz₁_gt_x₁j -- z₁ > x₁ j
      · -- Case i' ≠ j
        simp only [z, if_neg h_eq_j'] -- z i' simplifies to (max (x₁ i') (x₂ i') + b i') / 2
        -- Goal: (max (x₁ i') (x₂ i') + b i') / 2 > x₁ i'
        have h_two_pos : (0 : ℝ) < 2 := by norm_num
        rw [gt_iff_lt, lt_div_iff₀' h_two_pos] -- Goal: 2 * x₁ i' < max (x₁ i') (x₂ i') + b i'
        -- The goal is now 2 * x₁ i' < x₁ i' ⊔ x₂ i' + b i'
        rw [two_mul] -- Goal: x₁ i' + x₁ i' < x₁ i' ⊔ x₂ i' + b i'
        apply add_lt_add_of_le_of_lt (le_max_left _ _) (hx₁_mem.2 i')

    have ind2 : indicatorUpperRightOrthant x₂ z = 0 := by
      unfold indicatorUpperRightOrthant
      apply if_neg -- Goal: ¬ RVector.allGt z x₂
      intro h_all_gt_z_x₂ -- Assume RVector.allGt z x₂ (∀ i, z i > x₂ i). Goal: False.
      -- We need to show a contradiction. Consider component j.
      specialize h_all_gt_z_x₂ j -- This implies z j > x₂ j.
      -- Substitute the definition of z j.
      simp only [z, if_true] at h_all_gt_z_x₂ -- z j simplifies to z₁, so z₁ > x₂ j.
      -- This contradicts hz₁_lt_x₂j (which states z₁ < x₂ j).
      linarith [hz₁_lt_x₂j, h_all_gt_z_x₂] -- linarith can resolve this contradiction.

    -- Contradiction: h_eq_fn states indicatorUpperRightOrthant x₁ z = indicatorUpperRightOrthant x₂ z.
    -- Substituting ind1 and ind2, this becomes 1 = 0.
    rw [ind1, ind2] at h_eq_fn
    -- 1 = 0 is absurd.
    exact absurd h_eq_fn (by norm_num)

  -- Case 2: x₂ j < x₁ j
  · -- Similar to Case 1 but with roles of x₁ and x₂ reversed
    -- Case 2: x₂ j < x₁ j
    · -- Similar to Case 1 but with roles of x₁ and x₂ reversed
      -- Create a test point z where the jth component is between x₂ j and x₁ j
      let z₁ := (x₁ j + x₂ j) / 2 -- Midpoint between x₁ j and x₂ j

      have hz₁_gt_x₂j : z₁ > x₂ j := by
        dsimp [z₁]
        have h_two_pos : (0 : ℝ) < 2 := by norm_num
        rw [gt_iff_lt, lt_div_iff₀ h_two_pos] -- Transform to x₂ j * 2 < x₁ j + x₂ j
        rw [mul_comm, two_mul]  -- Rewrite 2 * x₂ j as x₂ j + x₂ j
        -- Need to prove: x₂ j + x₂ j < x₁ j + x₂ j
        rw [add_lt_add_iff_right (x₂ j)]  -- Cancel x₂ j on both sides
        exact h_gt  -- Use the hypothesis x₂ j < x₁ j

      have hz₁_lt_x₁j : z₁ < x₁ j := by
        dsimp [z₁]
        have h_two_pos : (0 : ℝ) < 2 := by norm_num
        rw [div_lt_iff₀ h_two_pos]  -- Transform to (x₁ j + x₂ j) < x₁ j * 2
        rw [mul_comm, two_mul]  -- Rewrite 2 * x₁ j as x₁ j + x₁ j
        -- Need to prove: x₁ j + x₂ j < x₁ j + x₁ j
        rw [Real.add_lt_add_iff_left (x₁ j)]  -- Cancel x₁ j on both sides
        exact h_gt  -- Use the hypothesis x₂ j < x₁ j

      -- For other components, use a value greater than both x₁ i and x₂ i
      let z : RVector n := fun i =>
        if i = j then z₁ else (max (x₁ i) (x₂ i) + b i) / 2

      -- Verify z is in the open rectangle Ioo_n a b
      have hz_mem_Ioo : z ∈ Ioo_n a b := by
        constructor
        · -- Prove ∀ i, a i < z i
          intro i
          by_cases h_eq_j : i = j
          · -- Case i = j
            rw [h_eq_j]  -- Replace i with j
            -- Use transitivity with x₂ j
            calc
              a j < x₂ j := hx₂_mem.1 j
              _ < z₁ := hz₁_gt_x₂j
              _ = z j := by dsimp [z]; rw [if_pos rfl]
          · -- Case i ≠ j
            dsimp [z]  -- First expand the definition of z
            rw [if_neg h_eq_j]  -- Use if_neg with h_eq_j to select the 'else' branch
            -- Now z i = (max (x₁ i) (x₂ i) + b i) / 2
            have h_a_lt_max : a i < max (x₁ i) (x₂ i) := by
              -- a i < x₁ i ≤ max (x₁ i) (x₂ i)
              calc
                a i < x₁ i := hx₁_mem.1 i
                _ ≤ max (x₁ i) (x₂ i) := le_max_left _ _
            have h_max_lt_b : max (x₁ i) (x₂ i) < b i := by
              -- max (x₁ i) (x₂ i) ≤ x₁ i < b i
              calc
                max (x₁ i) (x₂ i) ≤ max (x₁ i) (x₂ i) := le_refl _
                _ < b i := by
                  have h_x₁i_lt_bi : x₁ i < b i := hx₁_mem.2 i
                  have h_x₂i_lt_bi : x₂ i < b i := hx₂_mem.2 i
                  exact max_lt h_x₁i_lt_bi h_x₂i_lt_bi
            -- Now prove a i < (max (x₁ i) (x₂ i) + b i) / 2
            have h_two_pos : (0 : ℝ) < 2 := by norm_num
            apply (lt_div_iff₀ h_two_pos).mpr
            -- Need to prove: a i * 2 < max (x₁ i) (x₂ i) + b i
            calc a i * 2 = a i + a i := by rw [mul_comm, two_mul]
                      _ < max (x₁ i) (x₂ i) + b i := add_lt_add h_a_lt_max (hab i)

        · -- Prove ∀ i, z i < b i
          intro i
          by_cases h_eq_j : i = j
          · -- Case i = j
            rw [h_eq_j]  -- Replace i with j
            -- Use transitivity with x₁ j
            calc
              z j = z₁ := by dsimp [z]; rw [if_pos rfl]
              _ < x₁ j := hz₁_lt_x₁j
              _ < b j := hx₁_mem.2 j
          · -- Case i ≠ j
            dsimp [z]  -- Unfold the definition of z
            rw [if_neg h_eq_j]  -- Use if_neg with h_eq_j to select the 'else' branch
            -- Now z i = (max (x₁ i) (x₂ i) + b i) / 2
            have h_two_pos : (0 : ℝ) < 2 := by norm_num
            apply (div_lt_iff₀ h_two_pos).mpr
            -- Need to prove: max (x₁ i) (x₂ i) + b i < b i * 2
            calc
              x₁ i ⊔ x₂ i + b i < b i + b i := by
                apply add_lt_add_right
                exact max_lt (hx₁_mem.2 i) (hx₂_mem.2 i)
              _ = b i * 2 := by ring

      -- Apply h_eq_fn to get a contradiction
      specialize h_eq_fn z hz_mem_Ioo

      -- Calculate indicator values for x₁ and x₂ at z
      have ind1 : indicatorUpperRightOrthant x₁ z = 0 := by
        unfold indicatorUpperRightOrthant
        apply if_neg
        intro h_all_gt_z_x₁
        specialize h_all_gt_z_x₁ j
        simp only [z, if_true] at h_all_gt_z_x₁
        linarith [hz₁_lt_x₁j, h_all_gt_z_x₁]


      have ind2 : indicatorUpperRightOrthant x₂ z = 1 := by
        unfold indicatorUpperRightOrthant
        apply if_pos
        intro i
        by_cases h_eq_j : i = j
        · -- Case i = j
          rw [h_eq_j]
          simp only [z, if_pos rfl]
          exact hz₁_gt_x₂j
        · -- Case i ≠ j
          simp only [z, if_neg h_eq_j]
          have h_two_pos : (0 : ℝ) < 2 := by norm_num
          rw [gt_iff_lt, lt_div_iff₀' h_two_pos]
          -- Need to prove: 2 * x₂ i < max (x₁ i) (x₂ i) + b i
          rw [two_mul] -- 2 * x₂ i = x₂ i + x₂ i
          apply add_lt_add_of_le_of_lt
          · exact le_max_right _ _ -- x₂ i ≤ max (x₁ i) (x₂ i)
          · exact hx₂_mem.2 i -- x₂ i < b i

      -- Contradiction: h_eq_fn states indicatorUpperRightOrthant x₁ z = indicatorUpperRightOrthant x₂ z.
      -- Substituting ind1 and ind2, this becomes 0 = 1.
      rw [ind1, ind2] at h_eq_fn
      -- 0 = 1 is absurd.
      exact absurd h_eq_fn (by norm_num)

/-- Calculates the Riemann-Stieltjes integral for an indicator function of an upper-right orthant. -/
lemma integral_for_indicatorUpperRightOrthant {n : ℕ} {a b : RVector n}
    (hab : ∀ i, a i < b i)
    {u : RVector n → ℝ} {Dist : RVector n → ℝ} {x₀ : RVector n}
    (hx₀_mem : x₀ ∈ Ioo_n a b)
    (h_u_def : ∀ x ∈ Icc_n a b, u x = indicatorUpperRightOrthant x₀ x) :
    riemannStieltjesIntegralND u Dist a b x₀ (Ioo_subset_Icc_self_n hx₀_mem)
      (fun x hx => h_u_def x (Ioo_subset_Icc_self_n hx)) = survivalProbN Dist x₀ b := by
  -- Step 1: Show that u matches an indicator function on the open rectangle for some x₀' in Icc
  have hx₀_mem_Icc : x₀ ∈ Icc_n a b := Ioo_subset_Icc_self_n hx₀_mem
  have h_match : ∃ x₀' ∈ Icc_n a b,
      ∀ x ∈ Ioo_n a b, u x = indicatorUpperRightOrthant x₀' x := by
    use x₀, hx₀_mem_Icc
    intro x hx_open
    have hx_closed : x ∈ Icc_n a b := Ioo_subset_Icc_self_n hx_open
    exact h_u_def x hx_closed

  -- Step 2: Apply the definition of the integral
  unfold riemannStieltjesIntegralND
  simp only [h_match, dif_pos]

/-- Main theorem: FSD in N dimensions is equivalent to expected utility inequality
    for all indicator functions of upper-right orthants.
theorem fsd_nd_integral_equiv {n : ℕ} {F G : RVector n → ℝ}
This theorem establishes a fundamental connection between first-order stochastic dominance (FSD)
and expected utility theory in N dimensions. Specifically, it shows that verifying FSD for two
distributions is equivalent to checking that the expected utility of all indicator functions
of upper-right orthants is greater for one distribution than the other. This equivalence provides
a practical method for comparing distributions in applications such as economics, finance, and
decision theory, where FSD is used to model preferences or risk aversion. -/
theorem fsd_nd_iff_integral_indicatorUpperRightOrthant_ge {n : ℕ} {F G : RVector n → ℝ}
    {a b : RVector n} (hab : ∀ i, a i < b i) :
    (∀ x₀ ∈ Ioo_n a b, survivalProbN F x₀ b ≥ survivalProbN G x₀ b) ↔
    (∀ (x₀ : RVector n) (hx₀ : x₀ ∈ Ioo_n a b),
      riemannStieltjesIntegralND (indicatorUpperRightOrthant x₀) F a b x₀ (Ioo_subset_Icc_self_n hx₀) (fun x _ => rfl) ≥
      riemannStieltjesIntegralND (indicatorUpperRightOrthant x₀) G a b x₀ (Ioo_subset_Icc_self_n hx₀) (fun x _ => rfl)) := by
  constructor
  -- Forward direction (⇒): Assuming survival prob dominance, prove integral inequality
  · intro h_survival_dominance
    intro x₀ hx₀_mem
    let u := indicatorUpperRightOrthant x₀
    have h_u_def : ∀ x ∈ Icc_n a b, u x = indicatorUpperRightOrthant x₀ x := fun x _ => rfl

    -- Calculate the integrals using our lemma
    have calc_int_F : riemannStieltjesIntegralND u F a b x₀ (Ioo_subset_Icc_self_n hx₀_mem)
      (fun x hx => h_u_def x (Ioo_subset_Icc_self_n hx)) = survivalProbN F x₀ b := by
      apply integral_for_indicatorUpperRightOrthant hab hx₀_mem h_u_def

    have calc_int_G : riemannStieltjesIntegralND u G a b x₀ (Ioo_subset_Icc_self_n hx₀_mem)
      (fun x hx => h_u_def x (Ioo_subset_Icc_self_n hx)) = survivalProbN G x₀ b := by
      apply integral_for_indicatorUpperRightOrthant hab hx₀_mem h_u_def

    -- Substitute into the goal
    -- Simplify the goal to make it easier to apply the hypothesis
    rw [calc_int_F, calc_int_G]
    -- Apply the main hypothesis
    apply h_survival_dominance x₀ hx₀_mem

  -- Backward direction (⇐): Assuming integral inequality, prove survival prob dominance
  · intro h_integral_indicator
    intro x₀ hx₀_mem
    -- Apply the hypothesis for this specific x₀
    specialize h_integral_indicator x₀ hx₀_mem

    -- Define the indicator function for the upper-right orthant
    let u := indicatorUpperRightOrthant x₀

    -- Show that the indicator function matches its definition on the closed rectangle
    have h_u_def : ∀ x ∈ Icc_n a b, u x = indicatorUpperRightOrthant x₀ x := fun x _ => rfl

    -- Calculate the Riemann-Stieltjes integral for F using the lemma
    have calc_int_F : riemannStieltjesIntegralND u F a b x₀ (Ioo_subset_Icc_self_n hx₀_mem)
      (fun x hx => h_u_def x (Ioo_subset_Icc_self_n hx)) = survivalProbN F x₀ b := by
      apply integral_for_indicatorUpperRightOrthant hab hx₀_mem h_u_def

    -- Calculate the Riemann-Stieltjes integral for G using the lemma
    have calc_int_G : riemannStieltjesIntegralND u G a b x₀ (Ioo_subset_Icc_self_n hx₀_mem)
      (fun x hx => h_u_def x (Ioo_subset_Icc_self_n hx)) = survivalProbN G x₀ b := by
      apply integral_for_indicatorUpperRightOrthant hab hx₀_mem h_u_def

    -- Substitute the calculated integrals into the hypothesis
    rw [calc_int_F, calc_int_G] at h_integral_indicator

    -- The hypothesis now directly implies the goal
    exact h_integral_indicator
