import Mathlib

/-!
 Section 3: The Universal Defect Identity
Formalization of the pointwise defect nonnegativity and defect identity.
-/

variable (m : ℕ) [NeZero m]

/-- A moving block [r, s] inside {1, ..., d} where d = m + 1. -/
structure MovingBlock (m : ℕ) where
  r : ℕ
  s : ℕ
  r_ge_one : 1 ≤ r
  s_le_d : s ≤ m + 1
  r_le_s : r ≤ s
  -- Structural constraint of 1 × m templates: block length k ≤ m when s = d
  block_len_le : s = m + 1 → s - r + 1 ≤ m

namespace MovingBlock

variable {m : ℕ} (b : MovingBlock m)

/-- Dimension d = m + 1 -/
def d (m : ℕ) : ℕ := m + 1

/-- Contraction rate δ = d - r = m + 1 - r -/
def delta (b : MovingBlock m) : ℝ :=
  ((m + 1 : ℝ) - (b.r : ℝ))

/-- Block length k = s - r + 1 -/
def k (b : MovingBlock m) : ℝ :=
  (b.s : ℝ) - (b.r : ℝ) + 1

/-- Derivative of top coordinate P'_d -/
noncomputable def P'_d (b : MovingBlock m) : ℝ :=
  if b.s = m + 1 then 1 / b.k else 0

/-- Pointwise defect: e(P, q) = m - δ - m * P'_d -/
noncomputable def defect (b : MovingBlock m) : ℝ :=
  (m : ℝ) - b.delta - (m : ℝ) * b.P'_d

/-! Algebraic reduction for s < d -/

theorem defect_of_s_lt_d (h : b.s < m + 1) :
    b.defect = (b.r : ℝ) - 1 := by
  have hs : b.s ≠ m + 1 := ne_of_lt h
  dsimp [defect, delta, P'_d]
  rw [ite_eq_right hs]
  ring

theorem defect_nonneg_of_s_lt_d (h : b.s < m + 1) :
    0 ≤ b.defect := by
  rw [defect_of_s_lt_d b h]
  have hr : (1 : ℝ) ≤ (b.r : ℝ) := by exact_mod_cast b.r_ge_one
  linarith

/-! Algebraic reduction for s = d -/

theorem defect_of_s_eq_d (h : b.s = m + 1) :
    b.defect = (b.k - 1) * ((m : ℝ) - b.k) / b.k := by
  have hr : (b.r : ℝ) ≤ b.s := Nat.cast_le.mpr b.r_le_s
  have hk : b.k ≠ 0 := by
    dsimp [k]
    linarith
  have hd : (b.s : ℝ) = (m + 1 : ℝ) := by exact_mod_cast h
  have h_delta : b.delta = b.k - 1 := by
    dsimp [delta, k]
    rw [hd]
    ring
  dsimp [defect, P'_d]
  rw [ite_eq_left h, h_delta]
  field_simp
  ring

theorem defect_nonneg_of_s_eq_d (h : b.s = m + 1) :
    0 ≤ b.defect := by
  rw [defect_of_s_eq_d b h]
  have hr : (b.r : ℝ) ≤ b.s := Nat.cast_le.mpr b.r_le_s
  have hk1 : 0 ≤ b.k - 1 := by
    dsimp [k]
    linarith
  have hkm : 0 ≤ (m : ℝ) - b.k := by
    have h_len : ((b.s - b.r + 1 : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr (b.block_len_le h)
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub b.r_le_s] at h_len
    dsimp [k]
    linarith
  have hk_pos : 0 < b.k := by
    dsimp [k]
    linarith
  exact div_nonneg (mul_nonneg hk1 hkm) (le_of_lt hk_pos)

/-- Universal Pointwise Nonnegativity: e(P, q) ≥ 0 -/
theorem defect_nonneg : 0 ≤ b.defect := by
  by_cases h : b.s = m + 1
  · exact defect_nonneg_of_s_eq_d b h
  · have hlt : b.s < m + 1 := Nat.lt_of_le_of_ne b.s_le_d h
    exact defect_nonneg_of_s_lt_d b hlt

end MovingBlock
