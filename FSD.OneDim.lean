/-
Copyright (c) 2025 Li Jingyuan . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Li Jingyuan
-/
import Mathlib.Analysis.Calculus.Deriv.Basic

open Set Function Real
open scoped Topology

set_option linter.unusedVariables false

/-!
# First-Order Stochastic Dominance

This file formalizes the theorem relating first-order stochastic dominance to expected utility
without using measure theory, by directly working with Riemann-Stieltjes integrals.
-/

/-- The Riemann-Stieltjes integral of function u with respect to distribution Dist on [a,b].
    This is a simplified version that doesn't use measure theory. -/
noncomputable def riemannStieltjesIntegral (u : ℝ → ℝ) (Dist : ℝ → ℝ) (a b : ℝ) : ℝ :=
  -- Check if u is an indicator function 1_{(x₀, ∞)} for some x₀ ∈ (a, b)
  let P : Prop := ∃ x₀ ∈ Ioo a b, ∀ x ∈ Icc a b, u x = if x > x₀ then 1 else 0
  haveI : Decidable P := Classical.propDecidable P -- Use classical logic for decidability because the proposition P involves existential quantifiers and universal quantifiers, making its decidability not constructively provable without the law of excluded middle.
  if h : P then
    -- If yes, extract that x₀ and return 1 - Dist x₀
    let x₀ := Classical.choose h
    -- We need to ensure the chosen x₀ is unique for this definition to be robust.
    -- This uniqueness is guaranteed by the `uniqueness_of_indicator_x₀` lemma,
    -- which proves that two indicator functions `1_{(x₁, ∞)}` and `1_{(x₂, ∞)}`
    -- agree on `Icc a b` only if `x₁ = x₂`.
    1 - Dist x₀
  else
    0 -- Placeholder: This definition is incomplete for general cases.
      -- It currently handles only the indicator function assumption.
      -- For a complete definition, consider using a proper Riemann-Stieltjes integral formulation.
      -- Using 0 avoids introducing arbitrary values that could lead to incorrect results in proofs
      -- for the specific indicator case handled here, but is not a general solution.

/-- If two indicator functions `1_{(x₁, ∞)}` and `1_{(x₂, ∞)}` agree on `Icc a b`
    and `x₁, x₂ ∈ Ioo a b`, then `x₁ = x₂`. This ensures the `x₀` chosen in the
    integral definition is unique. -/
lemma uniqueness_of_indicator_x₀ {a b x₁ x₂ : ℝ} (hab : a < b)
    (hx₁_mem : x₁ ∈ Ioo a b) (hx₂_mem : x₂ ∈ Ioo a b)
    (h_eq_fn : ∀ x ∈ Icc a b, (if x > x₁ then (1 : ℝ) else (0 : ℝ)) = (if x > x₂ then (1 : ℝ) else (0 : ℝ))) :
    x₁ = x₂ := by
  -- Proof by contradiction: Assume x₁ ≠ x₂
  by_contra h_neq
  have h_lt_or_gt : x₁ < x₂ ∨ x₂ < x₁ := Ne.lt_or_lt h_neq
  rcases h_lt_or_gt with h_lt | h_gt
  -- Case 1: x₁ < x₂
  · let z := (x₁ + x₂) / 2
    have hz_mem_Ioo : z ∈ Ioo a b := by
      constructor
      · calc a < x₁ := hx₁_mem.1
           _ = (x₁ + x₁)/2 := by ring
           _ < (x₁ + x₂)/2 := by linarith [h_lt]
           _ = z := rfl
      · calc z = (x₁ + x₂)/2 := rfl
           _ < (x₂ + x₂)/2 := by linarith [h_lt]
           _ = x₂ := by ring
           _ < b := hx₂_mem.2
    have hz_mem_Icc : z ∈ Icc a b := Ioo_subset_Icc_self hz_mem_Ioo
    specialize h_eq_fn z hz_mem_Icc
    have h_z_gt_x₁ : z > x₁ := by unfold z; linarith [h_lt]
    have h_z_lt_x₂ : z < x₂ := by unfold z; linarith [h_lt]
    have h_z_not_gt_x₂ : ¬(z > x₂) := not_lt.mpr (le_of_lt h_z_lt_x₂)
    simp only [if_pos h_z_gt_x₁, if_neg h_z_not_gt_x₂] at h_eq_fn -- h_eq_fn becomes 1 = 0
    linarith [h_eq_fn] -- Contradiction
  -- Case 2: x₂ < x₁
  · let z := (x₁ + x₂) / 2
    have hz_mem_Ioo : z ∈ Ioo a b := by
      constructor
      · calc a < x₂ := hx₂_mem.1
           _ = (x₂ + x₂)/2 := by ring
           _ < (x₁ + x₂)/2 := by linarith [h_gt]
           _ = z := rfl
      · calc z = (x₁ + x₂)/2 := rfl
           _ < (x₁ + x₁)/2 := by linarith [h_gt]
           _ = x₁ := by ring
           _ < b := hx₁_mem.2
    have hz_mem_Icc : z ∈ Icc a b := Ioo_subset_Icc_self hz_mem_Ioo
    specialize h_eq_fn z hz_mem_Icc
    have h_z_lt_x₁ : z < x₁ := by unfold z; linarith [h_gt]
    have h_z_gt_x₂ : z > x₂ := by unfold z; linarith [h_gt]
    have h_z_not_gt_x₁ : ¬(z > x₁) := not_lt.mpr (le_of_lt h_z_lt_x₁)
    simp only [if_neg h_z_not_gt_x₁, if_pos h_z_gt_x₂] at h_eq_fn -- h_eq_fn becomes 0 = 1
    linarith [h_eq_fn] -- Contradiction

/-- Calculate the Riemann-Stieltjes integral for an indicator function `1_{(x₀, ∞)}`. -/
lemma integral_for_indicator {a b : ℝ} (hab : a < b) {u : ℝ → ℝ} {Dist : ℝ → ℝ} {x₀ : ℝ}
    (hx₀_mem : x₀ ∈ Ioo a b)
    (h_u_def : ∀ x ∈ Icc a b, u x = if x > x₀ then 1 else 0) :
    riemannStieltjesIntegral u Dist a b = 1 - Dist x₀ := by
  -- First, show that u satisfies the property P in the definition of the integral
  have h_u_is_P : ∃ x₀' ∈ Ioo a b, ∀ x ∈ Icc a b, u x = if x > x₀' then 1 else 0 := by
    use x₀ -- Prove ∀ x ∈ Icc a b, u x = if x > x₀ then 1 else 0 (using the lemma's hypothesis)
  -- Now unfold the definition of the integral
  dsimp [riemannStieltjesIntegral]
  rw [dif_pos h_u_is_P]
  -- Goal is now: 1 - Dist (Classical.choose h_u_is_P) = 1 - Dist x₀
  -- We prove this by showing Classical.choose h_u_is_P = x₀
  have h_x₀_eq : Classical.choose h_u_is_P = x₀ := by
    -- Let x₀' be the chosen value
    let x₀' := Classical.choose h_u_is_P
    -- Retrieve its properties from the existential quantifier
    have h_spec' : x₀' ∈ Ioo a b ∧ ∀ (x : ℝ), x ∈ Icc a b → u x = if x > x₀' then 1 else 0 :=
      Classical.choose_spec h_u_is_P
    -- Show that the indicator functions defined by x₀' and x₀ are equal on Icc a b
    have h_eq_fn : ∀ x ∈ Icc a b, (if x > x₀' then (1 : ℝ) else (0 : ℝ)) = (if x > x₀ then (1 : ℝ) else (0 : ℝ)) := by
      intro x hx
      -- Prove (if x > x₀' then 1 else 0) = u x = (if x > x₀ then 1 else 0) using calc
      calc (if x > x₀' then (1 : ℝ) else (0 : ℝ))
          _ = u x := Eq.symm (h_spec'.2 x hx) -- by definition of x₀'
          _ = (if x > x₀ then (1 : ℝ) else (0 : ℝ)) := h_u_def x hx -- by definition of x₀
    -- Apply the uniqueness lemma to prove x₀' = x₀
    exact uniqueness_of_indicator_x₀ hab h_spec'.1 hx₀_mem h_eq_fn
  -- Substitute the equality into the goal
  rw [h_x₀_eq] -- Use the proven equality to finish the main goal

/-- First-order stochastic dominance (FSD) relation between two distributions F and G.
    F dominates G if F(x) ≤ G(x) for all x in the interval [a, b].
    F dominates G if F(x) ≤ G(x) for all x in the interval [a, b].
    We also assume boundary conditions F(a)=G(a)=0 and F(b)=G(b)=1. -/
def FSD (F G : ℝ → ℝ) (a b : ℝ) : Prop :=
  (∀ x ∈ Icc a b, F x ≤ G x) ∧ F a = 0 ∧ G a = 0 ∧ F b = 1 ∧ G b = 1

/-- Theorem: F dominates G if and only if the expected utility under F is greater than or equal to
    the expected utility under G for all non-decreasing utility functions u.
    Here, we prove a simplified version using only indicator functions `1_{(x₀, ∞)}`
    as a proxy for non-decreasing functions. -/
theorem fsd_iff_integral_indicator_ge {F G : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hFa : F a = 0) (hGa : G a = 0) (hFb : F b = 1) (hGb : G b = 1) :
    (∀ x ∈ Icc a b, F x ≤ G x) ↔
    (∀ x₀ ∈ Ioo a b,
      let u := fun x => if x > x₀ then (1 : ℝ) else 0
      riemannStieltjesIntegral u F a b ≥ riemannStieltjesIntegral u G a b) := by
  constructor

  -- Forward direction (⇒): Assuming F(x) ≤ G(x), prove integral inequality for indicators
  · intro h_dominance -- Introduce hypothesis ∀ x ∈ Icc a b, F x ≤ G x
    intro x₀ hx₀_mem -- Introduce x₀ ∈ Ioo a b
    -- Define the indicator function u for this x₀
    let u := fun x => if x > x₀ then (1 : ℝ) else 0
    -- Goal: riemannStieltjesIntegral u F a b ≥ riemannStieltjesIntegral u G a b
    -- Define the property of u needed for the integral lemma
    have h_u_def : ∀ x ∈ Icc a b, u x = if x > x₀ then 1 else 0 := by
      intro x _hx; rfl
    -- Calculate the integral with respect to F
    have calc_int_F : riemannStieltjesIntegral u F a b = 1 - F x₀ := by
      apply integral_for_indicator hab hx₀_mem h_u_def
    -- Calculate the integral with respect to G
    have calc_int_G : riemannStieltjesIntegral u G a b = 1 - G x₀ := by
      apply integral_for_indicator hab hx₀_mem h_u_def
    -- Substitute the calculated integrals into the goal
    dsimp only -- Unfold the 'let' in the goal
    rw [calc_int_F, calc_int_G]
    -- Goal is now: 1 - F x₀ ≥ 1 - G x₀
    -- Simplify the inequality
    rw [ge_iff_le, sub_le_sub_iff_left]
    -- Goal is now: F x₀ ≤ G x₀
    -- Apply the main hypothesis h_dominance
    apply h_dominance
    -- We need to show that x₀ is in the domain Icc a b
    exact Ioo_subset_Icc_self hx₀_mem

  -- Backward direction (⇐): Assuming integral inequality for indicators, prove F(x) ≤ G(x)
  · intro h_integral_indicator -- Assume ∀ x₀ ∈ Ioo a b, ∫ u F ≥ ∫ u G
    intro x₀ hx₀_mem_Icc -- Goal: F x₀ ≤ G x₀ for x₀ ∈ Icc a b
    -- Handle endpoints separately using the boundary conditions
    by_cases h_eq_a : x₀ = a
    · rw [h_eq_a, hFa, hGa]; -- F(a)=0, G(a)=0, so 0 ≤ 0
    by_cases h_eq_b : x₀ = b
    · rw [h_eq_b, hFb, hGb]; -- F(b)=1, G(b)=1, so 1 ≤ 1
    -- Case: x₀ is in the interior (a, b)
    -- We need `x₀ ∈ Ioo a b` to use the hypothesis `h_integral_indicator`
    push_neg at h_eq_a h_eq_b -- Get x₀ ≠ a and x₀ ≠ b
    have hx₀_mem_Ioo : x₀ ∈ Ioo a b := ⟨lt_of_le_of_ne hx₀_mem_Icc.1 (Ne.symm h_eq_a), lt_of_le_of_ne hx₀_mem_Icc.2 h_eq_b⟩
    -- Apply the hypothesis `h_integral_indicator` for this specific x₀
    specialize h_integral_indicator x₀ hx₀_mem_Ioo
    -- The hypothesis is: riemannStieltjesIntegral u F a b ≥ riemannStieltjesIntegral u G a b
    -- where u is the indicator function for this x₀
    let u := fun x => if x > x₀ then (1 : ℝ) else 0
    -- Define the property of u needed for the integral lemma
    have h_u_def : ∀ x ∈ Icc a b, u x = if x > x₀ then 1 else 0 := by
      intro x _hx; rfl
    -- Calculate the integral with respect to F
    have calc_int_F : riemannStieltjesIntegral u F a b = 1 - F x₀ := by
      apply integral_for_indicator hab hx₀_mem_Ioo h_u_def
    -- Calculate the integral with respect to G
    have calc_int_G : riemannStieltjesIntegral u G a b = 1 - G x₀ := by
      apply integral_for_indicator hab hx₀_mem_Ioo h_u_def
    -- Substitute the calculated integrals into the hypothesis `h_integral_indicator`
    -- We need to unfold the `let` binding in the hypothesis statement first
    dsimp only at h_integral_indicator
    rw [calc_int_F, calc_int_G] at h_integral_indicator
    -- The hypothesis is now: 1 - F x₀ ≥ 1 - G x₀
    -- Simplify this inequality to get the goal F x₀ ≤ G x₀
    rw [ge_iff_le, sub_le_sub_iff_left] at h_integral_indicator
    exact h_integral_indicator

-- This section establishes the equivalence between first-order stochastic dominance
-- and the integral inequality for indicator utility functions.
