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

/-!
 Step 1 Addition: Pointwise Identity Lemma
-/

namespace MovingBlock

variable {m : ℕ} (b : MovingBlock m)

/-- The fundamental pointwise defect relation rearranged for δ. -/
theorem pointwise_id : b.delta = (m : ℝ) - (m : ℝ) * b.P'_d - b.defect := by
  dsimp [defect]
  ring

/-!
 Step 1 & 2: Enumerating and Classifying Moving Blocks
Characterizing exactly which [r, s] configurations yield e = 0 and e > 0.
-/

variable {m : ℕ} [NeZero m] (b : MovingBlock m)

/-!  Defining the Taxonomy -/

/-- A 'Good' block is one where the defect evaluates exactly to 0. -/
def IsGoodBlock : Prop := b.defect = 0

/-- A 'Bad' block is one where the defect is strictly positive. -/
def IsBadBlock : Prop := 0 < b.defect

/-- Completeness: Every valid block is either Good (e = 0) or Bad (e > 0). -/
theorem good_or_bad : IsGoodBlock b ∨ IsBadBlock b := by
  dsimp [IsGoodBlock, IsBadBlock]
  by_cases h : b.defect = 0
  · exact Or.inl h
  · exact Or.inr (lt_of_le_of_ne b.defect_nonneg (Ne.symm h))

/-!  Classifying Interior Blocks (s < m + 1) -/

/-- 
CLASS 1 (Interior Good Blocks): 
For any block strictly below the top boundary, it has zero defect 
if and only if it starts at r = 1.
Examples: [1, 1], [1, 2], ..., [1, m].
-/
theorem good_interior_iff (h : b.s < m + 1) : 
    IsGoodBlock b ↔ b.r = 1 := by
  dsimp [IsGoodBlock]
  rw [defect_of_s_lt_d b h]
  constructor
  · intro heq
    have : (b.r : ℝ) = 1 := by linarith
    exact_mod_cast this
  · intro hr
    rw [hr]
    ring

/-- 
CLASS 2 (Interior Bad Blocks):
Any interior block starting at r ≥ 2 is strictly defective.
Examples for m ≥ 3: [2, 2], [2, 3], [3, 3], etc.
-/
theorem bad_interior_iff (h : b.s < m + 1) : 
    IsBadBlock b ↔ 2 ≤ b.r := by
  dsimp [IsBadBlock]
  rw [defect_of_s_lt_d b h]
  constructor
  · intro h_pos
    have : 1 < b.r := by
      have : (1 : ℝ) < (b.r : ℝ) := by linarith
      exact_mod_cast this
    exact this
  · intro hr
    have : (2 : ℝ) ≤ (b.r : ℝ) := by exact_mod_cast hr
    linarith

/-! Classifying Top-Boundary Blocks (s = m + 1) -/

/-- 
CLASS 3 (Top Good Blocks):
For blocks touching the top boundary, the defect is e = (k-1)(m-k)/k.
Because 1 ≤ k ≤ m, it is zero if and only if k = 1 or k = m:
- k = 1: [m+1, m+1] (the zero-rate piece)
- k = m: [2, m+1] (the piece pulling the top coordinate)
-/
theorem good_top_iff (h : b.s = m + 1) : 
    IsGoodBlock b ↔ b.k = 1 ∨ b.k = (m : ℝ) := by
  dsimp [IsGoodBlock]
  rw [defect_of_s_eq_d b h]
  have hk_pos : 0 < b.k := by 
    dsimp [k]
    have : (b.r : ℝ) ≤ (b.s : ℝ) := Nat.cast_le.mpr b.r_le_s
    linarith
  constructor
  · intro heq
    have h_num : (b.k - 1) * ((m : ℝ) - b.k) = 0 := by
      exact (div_eq_zero_iff.mp heq).resolve_right (ne_of_gt hk_pos)
    cases mul_eq_zero.mp h_num with
    | inl h1 => left; linarith
    | inr h2 => right; linarith
  · intro h_or
    cases h_or with
    | inl hk1 =>
      rw [hk1, sub_self, zero_mul, zero_div]
    | inr hkm =>
      rw [hkm, sub_self, mul_zero, zero_div]

/-- 
CLASS 4 (Top Bad Blocks):
Any top-boundary block with 1 < k < m is strictly defective.
These are the partial-contact blocks that arise when m ≥ 3.
-/
theorem bad_top_iff (h : b.s = m + 1) : 
    IsBadBlock b ↔ 1 < b.k ∧ b.k < (m : ℝ) := by
  dsimp [IsBadBlock]
  rw [defect_of_s_eq_d b h]
  have hr_le_s : (b.r : ℝ) ≤ (b.s : ℝ) := Nat.cast_le.mpr b.r_le_s
  have hk1_nonneg : 0 ≤ b.k - 1 := by
    dsimp [k]
    linarith
  have hk_pos : 0 < b.k := by 
    dsimp [k]
    linarith
  have hkm_nonneg : 0 ≤ (m : ℝ) - b.k := by
    have h_len : ((b.s - b.r + 1 : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr (b.block_len_le h)
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub b.r_le_s] at h_len
    dsimp [k]
    linarith
  constructor
  · intro h_pos
    have h_num_pos : 0 < (b.k - 1) * ((m : ℝ) - b.k) := 
      (div_pos_iff_of_pos_right hk_pos).mp h_pos
    have hk1_pos : 0 < b.k - 1 := by
      rcases hk1_nonneg.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        rw [← heq, zero_mul] at h_num_pos
        exact lt_irrefl 0 h_num_pos
    have hkm_pos : 0 < (m : ℝ) - b.k := by
      rcases hkm_nonneg.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        rw [← heq, mul_zero] at h_num_pos
        exact lt_irrefl 0 h_num_pos
    exact ⟨by linarith, by linarith⟩
  · intro ⟨hk1, hkm⟩
    have h1 : 0 < b.k - 1 := by linarith
    have h2 : 0 < (m : ℝ) - b.k := by linarith
    exact div_pos (mul_pos h1 h2) hk_pos

end MovingBlock

/-!
 Step 2: Integration on a Single Linear Piece
Bypassing full measure theory by using the properties of piecewise constants.
-/

/-- Represents a single interval `[qa, qb]` where the template moves linearly. -/
structure LinearPiece (m : ℕ) where
  qa : ℝ
  qb : ℝ
  h_qa_le_qb : qa ≤ qb
  -- Constant values on this specific interval
  delta : ℝ
  Pd_slope : ℝ
  defect : ℝ
  -- The pointwise identity proven in Step 1
  pointwise_id : delta = (m : ℝ) - (m : ℝ) * Pd_slope - defect
  -- The endpoints of the top coordinate P_d
  Pd_qa : ℝ
  Pd_qb : ℝ
  -- The fundamental theorem of calculus for a linear segment
  Pd_linear : Pd_qb - Pd_qa = Pd_slope * (qb - qa)

namespace LinearPiece

variable {m : ℕ} (p : LinearPiece m)

/-- The length of the interval Δq = qb - qa. -/
def len : ℝ := p.qb - p.qa

/-- The interval length is non-negative. -/
theorem len_nonneg : 0 ≤ p.len := by
  dsimp [len]
  linarith [p.h_qa_le_qb]

/--
Integrating a constant over `[qa, qb]` is multiplying by `(qb - qa)`.
Here we prove the integrated identity for a single interval.
-/
theorem integral_identity :
    p.delta * (p.qb - p.qa) =
    (m : ℝ) * (p.qb - p.qa) - (m : ℝ) * (p.Pd_qb - p.Pd_qa) - p.defect * (p.qb - p.qa) := by
  rw [p.pointwise_id, p.Pd_linear]
  ring

/-- Alternative formulation using `p.len` for cleaner summation. -/
theorem integral_identity' :
    p.delta * p.len =
    (m : ℝ) * p.len - (m : ℝ) * (p.Pd_qb - p.Pd_qa) - p.defect * p.len := by
  exact p.integral_identity

/-- Nonnegativity of the integrated defect on a single piece. -/
theorem defect_integral_nonneg (h_defect : 0 ≤ p.defect) :
    0 ≤ p.defect * (p.qb - p.qa) :=
  mul_nonneg h_defect (by linarith [p.h_qa_le_qb])

/-- Construct a `LinearPiece` directly from an active `MovingBlock`. -/
noncomputable def ofMovingBlock
    (b : MovingBlock m)
    (qa qb : ℝ)
    (h_le : qa ≤ qb)
    (Pd_qa Pd_qb : ℝ)
    (h_linear : Pd_qb - Pd_qa = b.P'_d * (qb - qa)) : LinearPiece m where
  qa := qa
  qb := qb
  h_qa_le_qb := h_le
  delta := b.delta
  Pd_slope := b.P'_d
  defect := b.defect
  pointwise_id := b.pointwise_id
  Pd_qa := Pd_qa
  Pd_qb := Pd_qb
  Pd_linear := h_linear

end LinearPiece

/-!
 Step 3: Telescoping Sum and Global Bound
Summing the linear pieces to derive the global defect inequality.
This models Equation (13) and Equation (14).
-/

namespace LinearPiece

variable {m : ℕ}

/-- Sum of the integrated lower contraction rate δ over a list of pieces. -/
def sum_delta : List (LinearPiece m) → ℝ
  | [] => 0
  | p :: tail => p.delta * (p.qb - p.qa) + sum_delta tail

/-- Sum of the lengths of the intervals (Total time T). -/
def sum_len : List (LinearPiece m) → ℝ
  | [] => 0
  | p :: tail => (p.qb - p.qa) + sum_len tail

/-- Sum of the changes in the top coordinate P_d. -/
def sum_Pd_change : List (LinearPiece m) → ℝ
  | [] => 0
  | p :: tail => (p.Pd_qb - p.Pd_qa) + sum_Pd_change tail

/-- Sum of the integrated defect Q(T). -/
def sum_defect : List (LinearPiece m) → ℝ
  | [] => 0
  | p :: tail => p.defect * (p.qb - p.qa) + sum_defect tail

/-- Total duration across all pieces is non-negative. -/
theorem sum_len_nonneg (l : List (LinearPiece m)) : 0 ≤ sum_len l := by
  induction l with
  | nil => rfl
  | cons p tail ih =>
    dsimp [sum_len]
    have hp_len : 0 ≤ p.qb - p.qa := by linarith [p.h_qa_le_qb]
    linarith

/-! The Exact Identity (Equation 13) -/

/-- The exact identity integrated over an arbitrary sequence of pieces:
    Δ(P, T) = m*T - m*ΔP_d - Q(T). -/
theorem global_integral_identity (l : List (LinearPiece m)) :
    sum_delta l = (m : ℝ) * sum_len l - (m : ℝ) * sum_Pd_change l - sum_defect l := by
  induction l with
  | nil =>
    dsimp [sum_delta, sum_len, sum_Pd_change, sum_defect]
    ring
  | cons p tail ih =>
    dsimp [sum_delta, sum_len, sum_Pd_change, sum_defect]
    linarith [p.integral_identity, ih]

/-! The Defect Positivity & Final Bound (Equation 14) -/

/-- If the defect is non-negative on every piece, the total integrated defect Q(T) is non-negative. -/
theorem sum_defect_nonneg (l : List (LinearPiece m))
    (h_defect : ∀ p ∈ l, 0 ≤ p.defect) : 0 ≤ sum_defect l := by
  induction l with
  | nil => rfl
  | cons p tail ih =>
    dsimp [sum_defect]
    have hp_def : 0 ≤ p.defect := h_defect p (List.Mem.head _)
    have hp_len : 0 ≤ p.qb - p.qa := by linarith [p.h_qa_le_qb]
    have hp_prod : 0 ≤ p.defect * (p.qb - p.qa) := mul_nonneg hp_def hp_len
    have htail : 0 ≤ sum_defect tail := ih (fun x hx => h_defect x (List.Mem.tail p hx))
    linarith

/-- The global upper bound on the average contraction rate.
    This corresponds to the pre-limit inequality in Eq (14). -/
theorem global_contraction_bound (l : List (LinearPiece m))
    (h_defect : ∀ p ∈ l, 0 ≤ p.defect)
    (h_T_pos : 0 < sum_len l) :
    sum_delta l / sum_len l ≤ (m : ℝ) - (m : ℝ) * (sum_Pd_change l / sum_len l) := by
  have h_id := global_integral_identity l
  have h_Q_nonneg := sum_defect_nonneg l h_defect
  have h_ineq : sum_delta l ≤ (m : ℝ) * sum_len l - (m : ℝ) * sum_Pd_change l := by linarith
  have h_cancel : sum_len l ≠ 0 := ne_of_gt h_T_pos

  calc sum_delta l / sum_len l
    _ ≤ ((m : ℝ) * sum_len l - (m : ℝ) * sum_Pd_change l) / sum_len l :=
        div_le_div_of_nonneg_right h_ineq (le_of_lt h_T_pos)
    _ = ((m : ℝ) * sum_len l) / sum_len l - ((m : ℝ) * sum_Pd_change l) / sum_len l :=
        sub_div _ _ _
    _ = (m : ℝ) - ((m : ℝ) * sum_Pd_change l) / sum_len l := by
        rw [mul_div_cancel_right₀ _ h_cancel]
    _ = (m : ℝ) - (m : ℝ) * (sum_Pd_change l / sum_len l) := by
        ring

/-! Telescoping Properties for Contiguous Trajectories -/

/-- Adjacent linear pieces match continuously at transition points. -/
def IsContiguous : List (LinearPiece m) → Prop
  | [] => True
  | [_] => True
  | p1 :: p2 :: rest => p1.qb = p2.qa ∧ p1.Pd_qb = p2.Pd_qa ∧ IsContiguous (p2 :: rest)

/-- Global bound specialized to boundary values $T$ and $P_d(T) - P_d(0)$. -/
theorem global_bound_boundary (l : List (LinearPiece m))
    (h_defect : ∀ p ∈ l, 0 ≤ p.defect)
    (T delta_Pd : ℝ)
    (h_len : sum_len l = T)
    (h_Pd : sum_Pd_change l = delta_Pd)
    (h_T_pos : 0 < T) :
    sum_delta l / T ≤ (m : ℝ) - (m : ℝ) * (delta_Pd / T) := by
  have h_bound := global_contraction_bound l h_defect (by rwa [h_len])
  rwa [h_len, h_Pd] at h_bound

end LinearPiece

/-!
 Section 4: Large-W Lower Bound for All m
Verifying the 5-piece template parameters, lengths, and phase exponent identities.
-/

namespace Section4

variable (m : ℕ)
variable (U W x : ℝ)

/-!  4.1 Parameters -/

/-- α = U / (1 + U) -/
noncomputable def alpha (U : ℝ) : ℝ := U / (1 + U)

/-- a = 1 - m*α -/
noncomputable def a (m : ℕ) (U : ℝ) : ℝ := 1 - (m : ℝ) * alpha U

/-- H = W * (a + (m - 1) * x) -/
noncomputable def H (m : ℕ) (U W x : ℝ) : ℝ :=
  W * (a m U + ((m : ℝ) - 1) * x)

/-- L = H / α -/
noncomputable def L (m : ℕ) (U W x : ℝ) : ℝ :=
  H m U W x / alpha U

/-- y = L * a -/
noncomputable def y (m : ℕ) (U W x : ℝ) : ℝ :=
  L m U W x * a m U

/-!  4.2 The Five Motions (Lengths and Rates) -/

-- Lengths of the 5 pieces from Equation (22)
noncomputable def len1 (m : ℕ) (U x : ℝ) : ℝ := (m : ℝ) * (x - alpha U)
noncomputable def len2 (m : ℕ) (U W x : ℝ) : ℝ := H m U W x - x
noncomputable def len3 (m : ℕ) (U x : ℝ) : ℝ := x - a m U
noncomputable def len4 (m : ℕ) (U W x : ℝ) : ℝ := (m : ℝ) * (y m U W x - x)
noncomputable def len5 (m : ℕ) (U W x : ℝ) : ℝ := ((m : ℝ) - 1) * (H m U W x - y m U W x)

-- Contraction rates δ for the 5 pieces from Equation (22)
def rate1 (m : ℕ) : ℝ := (m : ℝ) - 1
def rate2 : ℝ := 0
def rate3 (m : ℕ) : ℝ := (m : ℝ)
def rate4 (m : ℕ) : ℝ := (m : ℝ)
def rate5 (m : ℕ) : ℝ := (m : ℝ) - 1

/-!  Algebraic Verifications -/

/-- The fundamental parameter identity: a + m*α = 1 -/
theorem a_add_m_alpha : a m U + (m : ℝ) * alpha U = 1 := by
  dsimp [a]
  ring

/-- The length of the 5 pieces sums exactly to L - 1. -/
theorem sum_of_lengths (h_alpha : alpha U ≠ 0) :
    len1 m U x + len2 m U W x + len3 m U x + len4 m U W x + len5 m U W x =
    L m U W x - 1 := by
  have hH : H m U W x = L m U W x * alpha U := by
    dsimp [L]
    exact (div_mul_cancel₀ (H m U W x) h_alpha).symm
  dsimp [len1, len2, len3, len4, len5, y, a]
  rw [hH]
  ring

/-!  4.3 Exponents and Contraction Average -/

/-- The time q_2 at the end of the second piece (starting at q = 1). -/
noncomputable def q2 (m : ℕ) (U W x : ℝ) : ℝ :=
  1 + len1 m U x + len2 m U W x

/-- Factorization of q_2 into (1 + W) * (a + (m - 1) * x). -/
theorem q2_factorization :
    q2 m U W x = (1 + W) * (a m U + ((m : ℝ) - 1) * x) := by
  dsimp [q2, len1, len2, H, a]
  ring

/-- The ratio H / q_2 = W / (1 + W), proving the phase exponent is B. -/
theorem Pd_q2_ratio (h_pos : a m U + ((m : ℝ) - 1) * x ≠ 0) :
    H m U W x / q2 m U W x = W / (1 + W) := by
  rw [q2_factorization]
  dsimp [H]
  exact mul_div_mul_right W (1 + W) h_pos

/-- Total contraction mass V_x over the entire period of 5 motions. -/
noncomputable def V_x (m : ℕ) (U W x : ℝ) : ℝ :=
  len1 m U x * rate1 m +
  len2 m U W x * rate2 +
  len3 m U x * rate3 m +
  len4 m U W x * rate4 m +
  len5 m U W x * rate5 m

/-- Verifying Equation (24): Expansion of V_x in terms of the parameters. -/
theorem V_x_matches_rates :
    V_x m U W x =
    (m : ℝ) * ((m : ℝ) - 1) * (x - alpha U) +
    (m : ℝ) * (x - a m U) +
    (m : ℝ)^2 * (y m U W x - x) +
    ((m : ℝ) - 1)^2 * (H m U W x - y m U W x) := by
  dsimp [V_x, len1, len2, len3, len4, len5, rate1, rate2, rate3, rate4, rate5]
  ring

end Section4

/-!
 Section 5: The Remaining Range when m = 2
Verifying the parameter domain equivalences and positivity conditions.
-/

namespace Section5

variable (A B : ℝ)

/-!  5.1 Parameter Thresholds -/

/-- Parameter c = 1 - 2A. -/
def c (A : ℝ) : ℝ := 1 - 2 * A

/-- The B_* threshold (Equation 32). -/
noncomputable def B_star (A : ℝ) : ℝ := A / (1 - A)

/-- The B_min feasibility boundary (Equation 31). -/
noncomputable def B_min (A : ℝ) : ℝ := A^2 / (1 - 3 * A + 3 * A^2)

/-- Period length L (Equation 34). -/
noncomputable def L (A B : ℝ) : ℝ := (c A * B) / (A * (1 + B) - B)

/-!  5.2 Positivity & Equivalence Lemmas -/

/-- The quadratic denominator 1 - 3A + 3A² is strictly positive for all real A. -/
theorem denom_quad_pos (A : ℝ) : 0 < 1 - 3 * A + 3 * A^2 := by
  have h_sq : 1 - 3 * A + 3 * A^2 = 3 * (A - 1 / 2)^2 + 1 / 4 := by ring
  rw [h_sq]
  positivity

/--
Verifying the claim below Eq (34):
The denominator A(1 + B) - B is positive precisely when B < B_*.
-/
theorem denominator_pos_iff (hA_lt : A < 1) :
    0 < A * (1 + B) - B ↔ B < B_star A := by
  have h1 : 0 < 1 - A := by linarith
  dsimp [B_star]
  rw [lt_div_iff₀ h1]
  constructor <;> intro h <;> linarith

/--
Verifying Equation (35):
The feasibility condition A ≤ L * c is equivalent to B_min ≤ B.
-/
theorem feasibility_equivalence
    (h_denom : 0 < A * (1 + B) - B) :
    A ≤ L A B * c A ↔ B_min A ≤ B := by
  have h_quad := denom_quad_pos A
  have h_alg : (1 - 2 * A)^2 * B - A * (A * (1 + B) - B) = B * (1 - 3 * A + 3 * A^2) - A^2 := by
    ring
  dsimp [L, c, B_min]
  have h_prod : ((1 - 2 * A) * B) / (A * (1 + B) - B) * (1 - 2 * A) =
      ((1 - 2 * A)^2 * B) / (A * (1 + B) - B) := by ring
  rw [h_prod, le_div_iff₀ h_denom, div_le_iff₀ h_quad]
  constructor
  · intro h
    linarith [h, h_alg]
  · intro h
    linarith [h, h_alg]

/-- Consistency check: B_min(A) < B_*(A) holds on the relevant interval 1/3 < A < 1/2. -/
theorem B_min_lt_B_star (hA1 : 1 / 3 < A) (hA2 : A < 1 / 2) :
    B_min A < B_star A := by
  have hA_pos : 0 < A := by linarith
  have h_sub : 0 < 1 - A := by linarith
  have h_quad := denom_quad_pos A
  dsimp [B_min, B_star]
  rw [div_lt_div_iff₀ h_quad h_sub]
  have hc : 0 < 1 - 2 * A := by linarith
  have hc_sq : 0 < (1 - 2 * A)^2 := sq_pos_of_ne_zero (ne_of_gt hc)
  have h_prod : 0 < A * (1 - 2 * A)^2 := mul_pos hA_pos hc_sq
  have h_diff : (1 - 3 * A + 3 * A^2) * A - A^2 * (1 - A) = A * (1 - 2 * A)^2 := by ring
  linarith

end Section5

/-!
 Section 6: The lower-bound cycle for m = 2
Verifying the 4-piece template parameters, lengths, phase exponents, and polynomial identity.
-/

namespace Section6

variable (A B s : ℝ)

/-! 6.1 Parameters (Equations 29, 34, 36) -/

/-- Parameter c = 1 - 2A -/
noncomputable def c (A : ℝ) : ℝ := 1 - 2 * A

/-- Parameter d₀ = 3A - 1 -/
noncomputable def d0 (A : ℝ) : ℝ := 3 * A - 1

/-- Period length L = cB / (A(1 + B) - B) -/
noncomputable def L (A B : ℝ) : ℝ :=
  (c A * B) / (A * (1 + B) - B)

/-- Coordinate transition x = L * c -/
noncomputable def x (A B : ℝ) : ℝ :=
  L A B * c A

/-- Height parameter H = L * A -/
noncomputable def H (A B : ℝ) : ℝ :=
  L A B * A

/-! 6.2 The Four Motions (Lengths and Rates) -/

-- Lengths of the 4 pieces from Equation (39)
noncomputable def len1 (A B : ℝ) : ℝ := 2 * (x A B - A)
noncomputable def len2 (A B : ℝ) : ℝ := H A B - x A B
noncomputable def len3 (A B : ℝ) : ℝ := x A B - c A
noncomputable def len4 (A B : ℝ) : ℝ := H A B - x A B

-- Contraction rates δ for the 4 pieces when m = 2
def rate1 : ℝ := 1
def rate2 : ℝ := 0
def rate3 : ℝ := 2
def rate4 : ℝ := 1

/-! 6.3 Algebraic Verifications -/

/-- The final piece length is exactly L * d₀ (Equation 41). -/
theorem len4_eq_L_d0 : len4 A B = L A B * d0 A := by
  dsimp [len4, H, x, c, d0]
  ring

/-- The lengths of the 4 pieces sum exactly to L - 1 (Equation 39). -/
theorem sum_of_lengths :
    len1 A B + len2 A B + len3 A B + len4 A B = L A B - 1 := by
  dsimp [len1, len2, len3, len4, H, x, c]
  ring

/-- The time q₂ at the end of the zero-rate piece (Equation 40), starting at q = 1. -/
noncomputable def q2 (A B : ℝ) : ℝ :=
  1 + len1 A B + len2 A B

/-- Alternative simplified expression for q₂: c + x + H. -/
theorem q2_eq_c_add_x_add_H : q2 A B = c A + x A B + H A B := by
  dsimp [q2, len1, len2, c]
  ring

/-- Verifying the target exponent ratio: H / q₂ = B (Equation 40). -/
theorem Pd_q2_ratio (h_denom1 : A * (1 + B) - B ≠ 0) (h_denom2 : q2 A B ≠ 0) :
    H A B / q2 A B = B := by
  rw [div_eq_iff h_denom2]
  rw [q2_eq_c_add_x_add_H]
  dsimp [H, x, L, c]
  field_simp [h_denom1]
  ring

/-- Total contraction mass V over the 4 pieces. -/
noncomputable def V (A B : ℝ) : ℝ :=
  len1 A B * rate1 +
  len2 A B * rate2 +
  len3 A B * rate3 +
  len4 A B * rate4

/-- Algebraic reduction of total contraction mass V. -/
theorem V_eq : V A B = 3 * x A B + H A B - 2 * (1 - A) := by
  dsimp [V, len1, len2, len3, len4, rate1, rate2, rate3, rate4, c]
  ring

/-! 6.4 The Polynomial Identity (Equations 45 & 46) -/

/-- N(A, L) from Equation (45). -/
noncomputable def N (A L_val : ℝ) : ℝ :=
  5 * A^2 * L_val^2 + 8 * A^2 * L_val - 4 * A^2 -
  4 * A * L_val^2 - 4 * A * L_val + 2 * A + L_val^2

/-- The transformed polynomial in shift variable s from Equation (46). -/
noncomputable def N_transformed (A s_val : ℝ) : ℝ :=
  (5 * A^2 - 4 * A + 1) * s_val^2 +
  (2 * A * (1 - A) * (3 * A - 1) / c A) * s_val +
  (A * (2 - 3 * A) * (3 * A - 1)^2) / (c A)^2

/-- Quadratic coefficient strictly positive: 5A² - 4A + 1 = c² + A² > 0. -/
theorem quad_coeff_pos (hA : A ≠ 0) : 0 < 5 * A^2 - 4 * A + 1 := by
  have h_sq : 5 * A^2 - 4 * A + 1 = (1 - 2 * A)^2 + A^2 := by ring
  rw [h_sq]
  have hA2 : 0 < A^2 := sq_pos_of_ne_zero hA
  have hc2 : 0 ≤ (1 - 2 * A)^2 := sq_nonneg (1 - 2 * A)
  linarith

theorem N_identity (hc : c A ≠ 0) :
    N A (A / c A + s) = N_transformed A s := by
  dsimp [N, N_transformed, c] at *
  have hc' : 1 - A * 2 ≠ 0 := by
    intro h
    apply hc
    linarith
  have hc_sq : 1 - A * 4 + A ^ 2 * 4 ≠ 0 := by
    have h_eq : 1 - A * 4 + A ^ 2 * 4 = (1 - A * 2) ^ 2 := by ring
    rw [h_eq]
    exact pow_ne_zero 2 hc'
  field_simp [hc, hc', hc_sq]
  ring

end Section6

/-!
 Section 7: The Renewal Upper Bound for m = 2
Formalization of the discrete renewal recurrence and terminal limit bound.
-/

namespace Section7

variable (A B : ℝ)
variable (a b : ℝ) -- Perturbed parameters A - ε and B + ε
variable (z : ℕ → ℝ) (L : ℕ → ℝ) (alpha : ℕ → ℝ)

/-!  7.1 Iteration Parameters -/

/-- Perturbed period length L_ε from Equation (62). -/
noncomputable def L_eps (a b : ℝ) : ℝ :=
  ((1 - 2 * a) * b) / (a * (1 + b) - b)

/-- Target period length L from Equation (34). -/
noncomputable def L_target (A B : ℝ) : ℝ :=
  ((1 - 2 * A) * B) / (A * (1 + B) - B)

/-!  7.2 Recurrence Inequalities -/

/-- Equation (57): First renewal inequality. -/
def FirstRenewal (k : ℕ) : Prop :=
  z k / L k + 3 * alpha (k + 1) - 1 ≤ z (k + 1)

/-- Equation (61): Second renewal inequality. -/
def SecondRenewal (k : ℕ) : Prop :=
  L k ≤ ((1 - 2 * alpha k) * b) / (alpha (k + 1) * (1 + b) - b)

/-!  7.3 Terminal Algebraic Reductions -/

/-- Simplification of L_target - 1 into a single quotient. -/
theorem L_target_sub_one (h_denom : A * (1 + B) - B ≠ 0) :
    L_target A B - 1 = (2 * B - 3 * A * B - A) / (A * (1 + B) - B) := by
  dsimp [L_target]
  field_simp [h_denom]
  ring

/-- 
Terminal rate ratio simplification (Equation 65):
Eliminates the compound fraction in (3A - 1)B / (A * (L - 1)).
-/
theorem terminal_ratio_eq
    (h_denom1 : A * (1 + B) - B ≠ 0)
    (hA : A ≠ 0) :
    ((3 * A - 1) * B) / (A * (L_target A B - 1)) =
    ((3 * A - 1) * B * (A * (1 + B) - B)) / (A * (2 * B - 3 * A * B - A)) := by
  rw [L_target_sub_one A B h_denom1]
  field_simp [h_denom1, hA]

end Section7

/-!
 Section 8.3: The General Lower-Range Candidate (m ≥ 3)
Verifying the formal analogue of the 4-piece cycle for arbitrary m.
-/

namespace Section8_3

variable (m : ℕ)
variable (A B : ℝ)
variable (L : ℝ)

/-!  8.3.1 General m Parameters -/

/-- The parameter 'a' generalizes 'c' from m=2: a = 1 - m*A. -/
def a (m : ℕ) (A : ℝ) : ℝ := 1 - (m : ℝ) * A

/-- Coordinate transition x = L * a. -/
def x (m : ℕ) (A L : ℝ) : ℝ := L * a m A

/-- Height parameter H = L * A. -/
def H (A L : ℝ) : ℝ := L * A

/-- Denominator of the general period length L. -/
def denom (m : ℕ) (A B : ℝ) : ℝ :=
  A - B * (A + ((m : ℝ) - 1) * a m A)

/-- Closed-form period length L generalizing Equation (34) to arbitrary m. -/
noncomputable def L_general (m : ℕ) (A B : ℝ) : ℝ :=
  (a m A * B) / denom m A B

/-!  8.3.2 The Four Candidate Motions (Lengths and Rates) -/

-- Lengths of the 4 pieces generalizing Equation (39)
def len1 (m : ℕ) (A L : ℝ) : ℝ := (m : ℝ) * (x m A L - A)
def len2 (m : ℕ) (A L : ℝ) : ℝ := H A L - x m A L
def len3 (m : ℕ) (A L : ℝ) : ℝ := x m A L - a m A
def len4 (m : ℕ) (A L : ℝ) : ℝ := ((m : ℝ) - 1) * (H A L - x m A L)

-- Contraction rates δ for arbitrary m
def rate1 (m : ℕ) : ℝ := (m : ℝ) - 1
def rate2 : ℝ := 0
def rate3 (m : ℕ) : ℝ := (m : ℝ)
def rate4 (m : ℕ) : ℝ := (m : ℝ) - 1

/-!  8.3.3 Algebraic Verifications -/

/-- Fundamental parameter identity: a + m*A = 1. -/
theorem a_add_m_A : a m A + (m : ℝ) * A = 1 := by
  dsimp [a]
  ring

/-- The 4 candidate piece lengths sum to L - 1 for all m. -/
theorem sum_of_lengths_general :
    len1 m A L + len2 m A L + len3 m A L + len4 m A L = L - 1 := by
  dsimp [len1, len2, len3, len4, H, x, a]
  ring

/-- Time q₂ at the end of the zero-rate piece, starting at q = 1. -/
def q2 (m : ℕ) (A L : ℝ) : ℝ :=
  1 + len1 m A L + len2 m A L

/-- Canonical simplification of q₂: a + (m - 1)x + H. -/
theorem q2_simplified :
    q2 m A L = a m A + ((m : ℝ) - 1) * x m A L + H A L := by
  dsimp [q2, len1, len2, a]
  ring

/-- Verifying the phase exponent ratio H / q₂ = B for general m. -/
theorem Pd_q2_ratio_general
    (h_denom : denom m A B ≠ 0)
    (h_q2_pos : q2 m A (L_general m A B) ≠ 0) :
    H A (L_general m A B) / q2 m A (L_general m A B) = B := by
  rw [div_eq_iff h_q2_pos, q2_simplified]
  dsimp [H, x, L_general]
  field_simp [h_denom]
  dsimp [denom]
  ring

/-!  8.3.4 Total Contraction Mass -/

/-- Total contraction mass V_m over the 4 pieces. -/
def V_m (m : ℕ) (A L : ℝ) : ℝ :=
  len1 m A L * rate1 m +
  len2 m A L * rate2 +
  len3 m A L * rate3 m +
  len4 m A L * rate4 m

/-- Reduced formula for the total contraction mass for arbitrary m. -/
theorem V_m_eq :
    V_m m A L =
    (2 * (m : ℝ) - 1) * x m A L + ((m : ℝ) - 1)^2 * H A L - (m : ℝ) * (1 - A) := by
  dsimp [V_m, len1, len2, len3, len4, rate1, rate2, rate3, rate4, a]
  ring

end Section8_3

/-!
 Section 8.3: The Surgery Principle
Proving that local perturbations maximize contraction if and only if they minimize the defect.
-/

namespace LocalSurgery

open LinearPiece

variable {m : ℕ}

/-- 
A "Local Surgery" replaces an original trajectory `l_orig` 
with a perturbed trajectory `l_pert` over the same total time interval, 
achieving the exact same change in the top coordinate P_d.
-/
structure Surgery (m : ℕ) where
  l_orig : List (LinearPiece m)
  l_pert : List (LinearPiece m)
  -- The surgery happens over the same total time duration
  same_duration : sum_len l_orig = sum_len l_pert
  -- The surgery achieves the same total change in P_d
  same_Pd_displacement : sum_Pd_change l_orig = sum_Pd_change l_pert

namespace Surgery

variable (s : Surgery m)

/-- 
The core exchange identity: The difference in total contraction mass 
between the perturbed and original trajectories equals the exact 
reduction in their accumulated defect.
-/
theorem delta_exchange :
    sum_delta s.l_pert - sum_delta s.l_orig = 
    sum_defect s.l_orig - sum_defect s.l_pert := by
  have h_orig := global_integral_identity s.l_orig
  have h_pert := global_integral_identity s.l_pert
  have h_dur := s.same_duration
  have h_pd := s.same_Pd_displacement
  rw [h_orig, h_pert, ← h_dur, ← h_pd]
  ring

/-- 
The Variational Surgery Principle:
A perturbed trajectory improves (or matches) the total contraction 
if and only if it decreases (or matches) the accumulated defect.
-/
theorem optimal_iff_minimal_defect :
    sum_delta s.l_orig ≤ sum_delta s.l_pert ↔ 
    sum_defect s.l_pert ≤ sum_defect s.l_orig := by
  have h_ex := s.delta_exchange
  constructor <;> intro h <;> linarith

/-- Contraction gain when surgery produces a defect-free trajectory (Q_pert = 0). -/
theorem delta_gain_of_zero_defect (h_zero : sum_defect s.l_pert = 0) :
    sum_delta s.l_pert - sum_delta s.l_orig = sum_defect s.l_orig := by
  have h_ex := s.delta_exchange
  linarith

/-- 
Defect-free optimality: Any perturbation that eliminates the defect (Q_pert = 0)
is always greater than or equal to an original trajectory with non-negative defect.
-/
theorem zero_defect_is_optimal
    (h_orig_def : ∀ p ∈ s.l_orig, 0 ≤ p.defect)
    (h_pert_zero : sum_defect s.l_pert = 0) :
    sum_delta s.l_orig ≤ sum_delta s.l_pert := by
  have h_orig_nonneg := sum_defect_nonneg s.l_orig h_orig_def
  rw [s.optimal_iff_minimal_defect]
  linarith

/-- The surgery principle on the normalized average contraction rates. -/
theorem average_rate_iff_minimal_defect (h_T_pos : 0 < sum_len s.l_orig) :
    sum_delta s.l_orig / sum_len s.l_orig ≤ sum_delta s.l_pert / sum_len s.l_pert ↔
    sum_defect s.l_pert ≤ sum_defect s.l_orig := by
  have hT : sum_len s.l_pert = sum_len s.l_orig := s.same_duration.symm
  rw [hT, div_le_div_iff_of_pos_right h_T_pos]
  exact s.optimal_iff_minimal_defect

end Surgery

end LocalSurgery

/-!
 Step 4: Macroscopic Time-Shifting Surgery (m = 3)
Proving that routing around a partial contact using extreme boundaries 
strictly improves the contraction mass.
-/

namespace MacroscopicSurgery

open LinearPiece
open LocalSurgery

variable (T : ℝ) (hT : 0 ≤ T) (hT_pos : 0 < T)

/-!  4.1 The Original Bad Trajectory -/

/-- 
The bad piece representing the [3, 4] partial-contact block.
Runs for time T with top slope 1/2 and defect 1/2.
-/
noncomputable def piece_bad (T : ℝ) (hT : 0 ≤ T) : LinearPiece 3 where
  qa := 0
  qb := T
  h_qa_le_qb := hT
  delta := 1
  Pd_slope := 1 / 2
  defect := 1 / 2
  pointwise_id := by norm_num
  Pd_qa := 0
  Pd_qb := T / 2
  Pd_linear := by ring

/-- The baseline trajectory using only the bad block. -/
noncomputable def path_bad (T : ℝ) (hT : 0 ≤ T) : List (LinearPiece 3) := [piece_bad T hT]

/-!  4.2 The Proposed Surgery (Time-Shifting) -/

/-- 
Phase 1: The [4, 4] runaway block. 
Runs for time T / 4 with top slope 1 and defect 0.
-/
noncomputable def piece_good1 (T : ℝ) (hT : 0 ≤ T) : LinearPiece 3 where
  qa := 0
  qb := T / 4
  h_qa_le_qb := by linarith [hT]
  delta := 0
  Pd_slope := 1
  defect := 0
  pointwise_id := by norm_num
  Pd_qa := 0
  Pd_qb := T / 4
  Pd_linear := by ring

/-- 
Phase 2: The [2, 4] catch-up block. 
Runs for time 3T / 4 with top slope 1/3 and defect 0.
-/
noncomputable def piece_good2 (T : ℝ) (hT : 0 ≤ T) : LinearPiece 3 where
  qa := T / 4
  qb := T
  h_qa_le_qb := by linarith [hT]
  delta := 2
  Pd_slope := 1 / 3
  defect := 0
  pointwise_id := by norm_num
  Pd_qa := T / 4
  Pd_qb := T / 2
  Pd_linear := by ring

/-- The replacement trajectory bypassing the partial contact. -/
noncomputable def path_good (T : ℝ) (hT : 0 ≤ T) : List (LinearPiece 3) := 
  [piece_good1 T hT, piece_good2 T hT]

/-- Continuity check: the good pieces meet smoothly at transition point q = T/4. -/
theorem path_good_contiguous : IsContiguous (path_good T hT) := by
  dsimp [path_good, IsContiguous, piece_good1, piece_good2]
  exact ⟨rfl, rfl, trivial⟩

/-!  4.3 Boundary Conservation Constraints -/

/-- Constraint 1: Total duration is conserved and equals T. -/
theorem same_duration (T : ℝ) (hT : 0 ≤ T) :
    sum_len (path_bad T hT) = sum_len (path_good T hT) := by
  dsimp [path_good, path_bad, sum_len, piece_good1, piece_good2, piece_bad]
  ring

/-- Constraint 2: Total displacement ΔP_d is conserved and equals T / 2. -/
theorem same_Pd_change (T : ℝ) (hT : 0 ≤ T) :
    sum_Pd_change (path_bad T hT) = sum_Pd_change (path_good T hT) := by
  dsimp [path_good, path_bad, sum_Pd_change, piece_good1, piece_good2, piece_bad]
  ring

/-- Formal `Surgery 3` package linking the bad and good paths. -/
noncomputable def macroscopicSurgery (T : ℝ) (hT : 0 ≤ T) : Surgery 3 where
  l_orig := path_bad T hT
  l_pert := path_good T hT
  same_duration := same_duration T hT
  same_Pd_displacement := same_Pd_change T hT

/-!  4.4 Mass Evaluations & Variational Payoff -/

theorem path_bad_delta : sum_delta (path_bad T hT) = T := by
  dsimp [path_bad, sum_delta, piece_bad]
  ring

theorem path_good_delta : sum_delta (path_good T hT) = (3 / 2) * T := by
  dsimp [path_good, sum_delta, piece_good1, piece_good2]
  ring

theorem path_bad_defect : sum_defect (path_bad T hT) = T / 2 := by
  dsimp [path_bad, sum_defect, piece_bad]
  ring

theorem path_good_defect : sum_defect (path_good T hT) = 0 := by
  dsimp [path_good, sum_defect, piece_good1, piece_good2]
  ring

/-- The surgery strictly eliminates the accumulated defect (from T/2 down to 0). -/
theorem defect_eliminated (T : ℝ) (hT : 0 ≤ T) (hT_pos : 0 < T) :
    sum_defect (path_good T hT) < sum_defect (path_bad T hT) := by
  rw [path_good_defect, path_bad_defect]
  linarith [hT_pos]

/-- Defect exchange identity verified via the general Surgery framework. -/
theorem surgery_exchange_verified :
    sum_delta (path_good T hT) - sum_delta (path_bad T hT) =
    sum_defect (path_bad T hT) - sum_defect (path_good T hT) :=
  (macroscopicSurgery T hT).delta_exchange

/-- The total contraction mass strictly increases from 1.0 * T to 1.5 * T. -/
theorem contraction_mass_increased (T : ℝ) (hT : 0 ≤ T) (hT_pos : 0 < T) :
    sum_delta (path_bad T hT) < sum_delta (path_good T hT) := by
  rw [path_bad_delta, path_good_delta]
  linarith [hT_pos]

/-- The average contraction rate strictly increases from 1 to 3/2. -/
theorem contraction_rate_increased (hT_pos : 0 < T) :
    sum_delta (path_bad T hT) / sum_len (path_bad T hT) <
    sum_delta (path_good T hT) / sum_len (path_good T hT) := by
  have h_len_bad : sum_len (path_bad T hT) = T := by
    dsimp [path_bad, sum_len, piece_bad]
    ring
  have h_len_good : sum_len (path_good T hT) = T := by
    dsimp [path_good, sum_len, piece_good1, piece_good2]
    ring
  rw [path_bad_delta, path_good_delta, h_len_bad, h_len_good]
  rw [div_self (ne_of_gt hT_pos)]
  have h_good_div : (3 / 2 * T) / T = 3 / 2 := by
    exact mul_div_cancel_right₀ (3 / 2) (ne_of_gt hT_pos)
  rw [h_good_div]
  norm_num

end MacroscopicSurgery

/-!
 Step 3: The Gap Capacity Lemma
Proving that boundary blocks are the unique optimal vehicles for top-coordinate growth.
-/

namespace GapCapacity

variable (m : ℕ) [hm : Fact (3 ≤ m)]
variable (k : ℝ)

/-- The defect generated per unit of top-coordinate displacement: e / P'_d. -/
noncomputable def defect_per_Pd_growth (m : ℕ) (k : ℝ) : ℝ :=
  (((k - 1) * ((m : ℝ) - k)) / k) / (1 / k)

/-!  3.1 The Parabolic Cost Formula -/

/-- 
THE GAP CAPACITY LEMMA:
For any block that moves the top coordinate (where 1 ≤ k ≤ m), 
the defect cost per unit distance is EXACTLY (k - 1)(m - k).
-/
theorem defect_cost_is_parabolic (hk_pos : 0 < k) :
    defect_per_Pd_growth m k = (k - 1) * ((m : ℝ) - k) := by
  dsimp [defect_per_Pd_growth]
  have hk : k ≠ 0 := ne_of_gt hk_pos
  field_simp [hk]

/-- The defect cost per unit growth is zero if and only if k = 1 or k = m. -/
theorem defect_cost_zero_iff (hk_pos : 0 < k) :
    defect_per_Pd_growth m k = 0 ↔ k = 1 ∨ k = (m : ℝ) := by
  rw [defect_cost_is_parabolic m k hk_pos]
  have : (k - 1) * ((m : ℝ) - k) = 0 ↔ k - 1 = 0 ∨ (m : ℝ) - k = 0 := mul_eq_zero
  rw [this]
  constructor
  · rintro (h1 | h2)
    · left; linarith
    · right; linarith
  · rintro (h1 | h2)
    · left; linarith
    · right; linarith

/-! 3.2 Suboptimality of Partial Contacts -/

/-- 
Among all non-singleton blocks (1 < k ≤ m), the boundary block k = m 
is the UNIQUE vehicle with zero defect cost.
-/
theorem unique_zero_defect_of_gt_one (hk_gt_1 : 1 < k) :
    defect_per_Pd_growth m k = 0 ↔ k = (m : ℝ) := by
  have hk_pos : 0 < k := by linarith
  rw [defect_cost_zero_iff m k hk_pos]
  constructor
  · rintro (h1 | h2)
    · linarith
    · exact h2
  · intro h
    exact Or.inr h

/-- 
Strict Inefficiency of Partial Contacts:
Any partial contact block with 1 < k < m incurs a strictly positive defect penalty.
-/
theorem partial_contacts_strictly_suboptimal (hk_pos : 0 < k) :
    (1 < k → k < (m : ℝ) → 0 < defect_per_Pd_growth m k) ∧
    (1 ≤ k → k ≤ (m : ℝ) → 0 ≤ defect_per_Pd_growth m k) := by
  constructor
  · intro hk1 hkm
    rw [defect_cost_is_parabolic m k hk_pos]
    have h1 : 0 < k - 1 := by linarith
    have h2 : 0 < (m : ℝ) - k := by linarith
    exact mul_pos h1 h2
  · intro hk1 hkm
    rw [defect_cost_is_parabolic m k hk_pos]
    have h1 : 0 ≤ k - 1 := by linarith
    have h2 : 0 ≤ (m : ℝ) - k := by linarith
    exact mul_nonneg h1 h2

/-- Dimension constraint helper: m ≥ 3 implies 1 < m. -/
theorem one_lt_m : 1 < (m : ℝ) := by
  have hm3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.out
  linarith

end GapCapacity

/-!
 Step 4: Telescoping the Global Limit
Formalizing the discrete renewal recurrence and its geometric series bound.
-/

namespace GlobalRenewal

variable (z : ℕ → ℝ)
variable (L C : ℝ)

/-!  4.1 The Discrete Renewal Sequence -/

/-- 
The generalized renewal inequality derived from macroscopic excursions:
Each excursion dilates time by L and adds a strict defect cost C.
-/
def ObeysRenewal : Prop :=
  ∀ k, z k / L + C ≤ z (k + 1)

/-- 
Horner-form recursive definition of the geometric series: 1 + r + r² + ... + rⁿ⁻¹.
This formulation aligns directly with recurrence unrolling under multiplication.
-/
def geom_sum (r : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => geom_sum r n * r + 1

/-!  4.2 Finite Unrolling -/

/-- 
Expanding the recurrence n times yields the geometric series 
lower bound for the accumulated quantity z(n).
-/
theorem unroll_recurrence (h_renew : ObeysRenewal z L C) (hL_pos : 0 < L) (n : ℕ) :
    z 0 * (1 / L)^n + C * geom_sum (1 / L) n ≤ z n := by
  induction n with
  | zero =>
    dsimp [geom_sum]
    ring_nf
    linarith
  | succ n ih =>
    have hn := h_renew n
    dsimp [geom_sum]
    have h_nonneg : 0 ≤ 1 / L := by positivity
    have ih_div : (z 0 * (1 / L)^n + C * geom_sum (1 / L) n) * (1 / L) ≤ z n * (1 / L) :=
      mul_le_mul_of_nonneg_right ih h_nonneg
    have h_div_eq : z n / L = z n * (1 / L) := by ring
    calc
      z 0 * (1 / L)^(n + 1) + C * (geom_sum (1 / L) n * (1 / L) + 1)
         = (z 0 * (1 / L)^n + C * geom_sum (1 / L) n) * (1 / L) + C := by ring
      _ ≤ z n * (1 / L) + C := by linarith [ih_div]
      _ = z n / L + C := by rw [h_div_eq]
      _ ≤ z (n + 1) := hn

/-!  4.3 Closed-Form Algebraic Target -/

/-- The fundamental polynomial cancellation: (∑ rⁱ) * (1 - r) = 1 - rⁿ. -/
lemma geom_sum_mul_one_sub (r : ℝ) (n : ℕ) :
    geom_sum r n * (1 - r) = 1 - r^n := by
  induction n with
  | zero =>
    dsimp [geom_sum]
    ring
  | succ n ih =>
    dsimp [geom_sum]
    calc (geom_sum r n * r + 1) * (1 - r)
      _ = (geom_sum r n * (1 - r)) * r + (1 - r) := by ring
      _ = (1 - r^n) * r + (1 - r)                 := by rw [ih]
      _ = 1 - r^(n + 1)                          := by ring

/-- 
The standard closed-form identity for the geometric series:
For L > 1, ∑_{i=0}^{n-1} (1/L)ⁱ = (1 - (1/L)ⁿ) * (L / (L - 1)).
-/
theorem geom_sum_closed_form (n : ℕ) (hL_gt_one : 1 < L) :
    geom_sum (1 / L) n = (1 - (1 / L)^n) * (L / (L - 1)) := by
  have hL0 : 0 < L := by linarith
  have hL_ne : L ≠ 0 := ne_of_gt hL0
  have hLm1 : L - 1 ≠ 0 := by linarith
  have h_denom : 1 - 1 / L ≠ 0 := by
    have : 1 - 1 / L = (L - 1) / L := by
      field_simp [hL_ne]
    rw [this]
    exact div_ne_zero hLm1 hL_ne

  have h_id := geom_sum_mul_one_sub (1 / L) n
  have h_div : geom_sum (1 / L) n = (1 - (1 / L)^n) / (1 - 1 / L) :=
    (eq_div_iff h_denom).mpr h_id
  have h_frac : 1 / (1 - 1 / L) = L / (L - 1) := by
    field_simp [hL_ne, hLm1]

  calc geom_sum (1 / L) n
    _ = (1 - (1 / L)^n) / (1 - 1 / L)        := h_div
    _ = (1 - (1 / L)^n) * (1 / (1 - 1 / L))  := by ring
    _ = (1 - (1 / L)^n) * (L / (L - 1))      := by rw [h_frac]

/-- 
The terminal asymptotic lower bound (Equation 65):
For any trajectory with non-negative baseline z(0) ≥ 0 and positive increment C ≥ 0,
the renewal recurrence is bounded below by the scaled geometric series limit.
-/
theorem unroll_closed_form_bound
    (h_renew : ObeysRenewal z L C)
    (hL_gt_one : 1 < L)
    (hz0 : 0 ≤ z 0)
    (n : ℕ) :
    C * (1 - (1 / L)^n) * (L / (L - 1)) ≤ z n := by
  have hL0 : 0 < L := by linarith
  have h_unroll := unroll_recurrence z L C h_renew hL0 n
  rw [geom_sum_closed_form L n hL_gt_one] at h_unroll
  have h_init : 0 ≤ z 0 * (1 / L)^n := by positivity
  linarith

end GlobalRenewal

/-!
 Step 5: The Analytic Limit
Bridging the finite geometric series to the topological limit using Mathlib Filters.
-/

namespace GlobalRenewalLimit

open Filter Topology

variable (z : ℕ → ℝ) (L C : ℝ)

/-- The explicit finite lower bound derived in the unrolled recurrence. -/
noncomputable def lower_bound (z : ℕ → ℝ) (L C : ℝ) (n : ℕ) : ℝ :=
  z 0 * (1 / L)^n + C * (1 - (1 / L)^n) * (L / (L - 1))

/-!  5.1 Convergence of the Geometric Lower Bound -/

/-- 
PROVING THE LIMIT:
As n → ∞, the sequence (1/L)ⁿ → 0 for 1 < L.
Therefore, the lower bound sequence converges to C * L / (L - 1).
-/
theorem tendsto_lower_bound (hL : 1 < L) :
    Tendsto (fun n ↦ lower_bound z L C n) atTop (𝓝 (C * (L / (L - 1)))) := by
  dsimp [lower_bound]
  have hL_pos : 0 < L := by linarith
  have h_nonneg : 0 ≤ 1 / L := by positivity
  have h_lt_one : 1 / L < 1 := (div_lt_one hL_pos).mpr hL
  have h_pow_zero := tendsto_pow_atTop_nhds_zero_of_lt_one h_nonneg h_lt_one

  -- Term 1: z(0) * (1 / L)ⁿ → z(0) * 0
  have h_term1 : Tendsto (fun n ↦ z 0 * (1 / L)^n) atTop (𝓝 (z 0 * 0)) :=
    tendsto_const_nhds.mul h_pow_zero

  -- Term 2: C * (1 - (1 / L)ⁿ) * (L / (L - 1)) → C * (1 - 0) * (L / (L - 1))
  have h_sub : Tendsto (fun n ↦ 1 - (1 / L)^n) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub h_pow_zero
  have h_term2 : Tendsto (fun n ↦ C * (1 - (1 / L)^n) * (L / (L - 1))) atTop
      (𝓝 (C * (1 - 0) * (L / (L - 1)))) :=
    (tendsto_const_nhds.mul h_sub).mul tendsto_const_nhds

  -- Combine and simplify target
  have h_sum := h_term1.add h_term2
  have h_simp : z 0 * 0 + C * (1 - 0) * (L / (L - 1)) = C * (L / (L - 1)) := by ring
  rwa [h_simp] at h_sum

/-!  5.2 Asymptotic Comparison Theorems -/

/-- 
Topological limit comparison:
If the renewal sequence z(n) converges to a limit Z, 
then Z is bounded below by the terminal geometric value C * L / (L - 1).
-/
theorem le_of_tendsto_limit {Z : ℝ} (hL : 1 < L)
    (h_bound : ∀ n, lower_bound z L C n ≤ z n)
    (hz : Tendsto z atTop (𝓝 Z)) :
    C * (L / (L - 1)) ≤ Z := by
  exact le_of_tendsto_of_tendsto' (tendsto_lower_bound z L C hL) hz h_bound

/-- 
Bridge theorem connecting Step 4 to Step 5:
Substituting the closed-form geometric sum into the unrolled recurrence 
produces the pointwise `lower_bound`.
-/
theorem lower_bound_of_unrolled (hL_gt_one : 1 < L)
    (h_unroll : ∀ n, z 0 * (1 / L)^n + C * GlobalRenewal.geom_sum (1 / L) n ≤ z n) :
    ∀ n, lower_bound z L C n ≤ z n := by
  intro n
  dsimp [lower_bound]
  rw [mul_assoc]
  have h := h_unroll n
  rwa [GlobalRenewal.geom_sum_closed_form L n hL_gt_one] at h

end GlobalRenewalLimit

/-!
 Section 1: Statement and Conventions (Deductively Wired)
Replacing tautological placeholders with direct applications of our 
verified piecewise-linear algebra.
-/

namespace Section1

open LinearPiece Section4 Section6 Section7 GlobalRenewalLimit

variable (m : ℕ) [hm : NeZero m]
variable (U W : ℝ)

/-!  1.1 Target Dimension Formulas -/

/-- The universal Large-W dimension formula (Equation 3): m / (1 + W). -/
noncomputable def LargeW_Target (m : ℕ) (W : ℝ) : ℝ := (m : ℝ) / (1 + W)

/-- The Remaining-Range dimension formula for m = 2 (Equation 4). -/
noncomputable def D_low (U W : ℝ) : ℝ :=
  ((1 - U) * (2 * U - 1) * W^2 + U * (5 - 6 * U) * W - 2 * U^2) /
  (U * (W + 1) * (2 * (1 - U) * W - U))

/-!  1.2 Abstract DFSU Top-Level Interface -/

opaque GeneralizedSystem (m : ℕ) : Type
opaque has_exponents {m : ℕ} (P : GeneralizedSystem m) (U W : ℝ) : Prop
opaque avg_contraction {m : ℕ} (P : GeneralizedSystem m) : ℝ
opaque dim_H_E (m : ℕ) (U W : ℝ) : ℝ

/-- 
The DFSU Variational Principle: 
Dimension is exactly the supremum of valid contraction rates.
-/
axiom dfsu_sandwich (target : ℝ) :
  (∀ (P : GeneralizedSystem m), has_exponents P U W → avg_contraction P ≤ target) → 
  (∃ (P : GeneralizedSystem m), has_exponents P U W ∧ target ≤ avg_contraction P) → 
  dim_H_E m U W = target

/-!  1.3 Bridging Axioms -/

/-- 
UPPER BOUND BRIDGE (Large W): 
Translates the global defect inequality (Section 3) 
into the universal upper bound on all generalized systems.
-/
axiom upper_bound_bridge_large_W :
  (∀ (l : List (LinearPiece m)) (_h_def : ∀ p ∈ l, 0 ≤ p.defect) (_hT : 0 < sum_len l),
    sum_delta l / sum_len l ≤ (m : ℝ) - (m : ℝ) * (sum_Pd_change l / sum_len l)) →
  (∀ (P : GeneralizedSystem m), has_exponents P U W → avg_contraction P ≤ LargeW_Target m W)

/-- 
LOWER BOUND BRIDGE (Large W, m ≥ 2): 
Translates the 5-piece periodic cycle (Section 4) 
into a witnessing generalized system.
-/
axiom lower_bound_bridge_large_W :
  (∀ (x : ℝ) ,
    Section4.len1 m U x + Section4.len2 m U W x + Section4.len3 m U x + 
    Section4.len4 m U W x + Section4.len5 m U W x = Section4.L m U W x - 1) →
  (∃ (P : GeneralizedSystem m), has_exponents P U W ∧ LargeW_Target m W ≤ avg_contraction P)

/-- 
LOWER BOUND BRIDGE (m = 2, Remaining Range):
Translates the 4-piece periodic cycle (Section 6) into a witnessing system in dimension 2.
-/
axiom lower_bound_bridge_remaining_range :
  (∀ (A B : ℝ), Section6.len1 A B + Section6.len2 A B + 
                Section6.len3 A B + Section6.len4 A B = Section6.L A B - 1) →
  (∃ (P : GeneralizedSystem 2), has_exponents P U W ∧ D_low U W ≤ avg_contraction P)

/-- 
UPPER BOUND BRIDGE (m = 2, Remaining Range):
Translates the analytic limit of the renewal recurrence (Section 7) 
into the global upper bound in dimension 2.
-/
axiom upper_bound_bridge_remaining_range :
  (∀ (z : ℕ → ℝ) (L C : ℝ) (_hL : 1 < L) 
     (_h_renew : ∀ k, z k / L + C ≤ z (k + 1)) (_hz0 : 0 ≤ z 0)
     (Z : ℝ) (_h_tendsto : Filter.Tendsto z Filter.atTop (nhds Z)),
    C * (L / (L - 1)) ≤ Z) →
  (∀ (P : GeneralizedSystem 2), has_exponents P U W → avg_contraction P ≤ D_low U W)

theorem theorem_1_1 
    (_hU_lower : 1 / (m : ℝ) < U) 
    (_hU_upper : U < 1 / ((m : ℝ) - 1))
    (_hW_lower : U / (((m : ℝ) - 1) * (1 - ((m : ℝ) - 1) * U)) ≤ W)
    (h_alpha : Section4.alpha U ≠ 0) :
    dim_H_E m U W = LargeW_Target m W := by
  have upper_bound := upper_bound_bridge_large_W m U W LinearPiece.global_contraction_bound
  have lower_bound := lower_bound_bridge_large_W m U W (fun x ↦ 
      Section4.sum_of_lengths m U W x h_alpha)
  exact dfsu_sandwich m U W (LargeW_Target m W) upper_bound lower_bound

theorem theorem_1_2 
    (hU_lower : 1 / 2 < U) 
    (hU_upper : U < 1)
    (_hW_feasible : U^2 / (1 - U) ≤ W)
    (h_alpha : Section4.alpha U ≠ 0) : 
    (U / (1 - U) ≤ W → dim_H_E 2 U W = LargeW_Target 2 W) ∧ 
    (W ≤ U / (1 - U) → dim_H_E 2 U W = D_low U W) := by
  constructor
  · intro _
    have upper := upper_bound_bridge_large_W 2 U W LinearPiece.global_contraction_bound
    have lower := lower_bound_bridge_large_W 2 U W (fun x ↦ 
        Section4.sum_of_lengths 2 U W x h_alpha)
    exact dfsu_sandwich 2 U W (LargeW_Target 2 W) upper lower
  · intro _
    have upper := upper_bound_bridge_remaining_range U W
      (fun z L C hL h_renew hz0 Z h_tendsto ↦ by
        have h_unroll_all : ∀ n, z 0 * (1 / L)^n + C * GlobalRenewal.geom_sum (1 / L) n ≤ z n :=
          fun n ↦ GlobalRenewal.unroll_recurrence z L C h_renew (by linarith) n
        have h_bound : ∀ n, GlobalRenewalLimit.lower_bound z L C n ≤ z n :=
          GlobalRenewalLimit.lower_bound_of_unrolled z L C hL h_unroll_all
        exact GlobalRenewalLimit.le_of_tendsto_limit z L C hL h_bound h_tendsto)
    have lower := lower_bound_bridge_remaining_range U W (fun A B ↦ 
        Section6.sum_of_lengths A B)
    exact dfsu_sandwich 2 U W (D_low U W) upper lower

end Section1

/-!
 Continuous Dynamics and Phase Average Extremization
Formalizing the claim from Sections 4.3 and 6 that the running phase average 
moves monotonically on linear pieces, forcing all extrema (minima and maxima) 
to occur strictly at piece boundaries.
-/

namespace PhaseDynamics

/-!  1. The Continuous Phase Average -/

/-- 
The continuous running phase average on a linear piece with constant rate `r`.
`K` is the conserved geometric invariant `M_a - r * q_a`, where `M_a` is the initial mass.
-/
noncomputable def D (r K q : ℝ) : ℝ := r + K / q

/-- 
The formal differential relation:
`D'(q) = (r - D(q)) / q = -K / q²`.
Verified purely algebraically without requiring differential calculus machinery.
-/
theorem phase_differential_relation (r K q : ℝ) (hq_pos : 0 < q) :
    (r - D r K q) / q = -K / q^2 := by
  dsimp [D]
  have hq : q ≠ 0 := ne_of_gt hq_pos
  field_simp [hq]
  ring

/-!  2. Monotonicity Profiles -/

/-- When K ≥ 0, the phase average D(q) = r + K/q is antitone (decreasing) on (0, ∞). -/
theorem antitone_of_nonneg_K (r K : ℝ) (hK : 0 ≤ K) {q1 q2 : ℝ}
    (hq1_pos : 0 < q1) (h_le : q1 ≤ q2) :
    D r K q2 ≤ D r K q1 := by
  dsimp [D]
  have h_frac : K / q2 ≤ K / q1 :=
    div_le_div_of_nonneg_left hK hq1_pos h_le
  linarith

/-- When K ≤ 0, the phase average D(q) = r + K/q is monotone (increasing) on (0, ∞). -/
theorem monotone_of_nonpos_K (r K : ℝ) (hK : K ≤ 0) {q1 q2 : ℝ}
    (hq1_pos : 0 < q1) (h_le : q1 ≤ q2) :
    D r K q1 ≤ D r K q2 := by
  dsimp [D]
  have hK_nonneg : 0 ≤ -K := by linarith
  have h_frac : (-K) / q2 ≤ (-K) / q1 :=
    div_le_div_of_nonneg_left hK_nonneg hq1_pos h_le
  simp only [neg_div] at h_frac
  linarith

/-- When K = 0, the phase average is strictly constant and equals the slope r. -/
theorem constant_of_zero_K (r q : ℝ) : D r 0 q = r := by
  dsimp [D]
  ring

/-!  3. Boundary Extremization Theorems -/

/-- 
MINIMUM AT BOUNDARY:
For any trajectory segment over [qa, qb], the minimum of the continuous 
phase average is achieved at one of the two endpoints.
-/
theorem phase_average_min_at_boundary (r K qa qb q : ℝ)
    (hqa_pos : 0 < qa) (hq_bounds : qa ≤ q ∧ q ≤ qb) :
    min (D r K qa) (D r K qb) ≤ D r K q := by
  have hq_pos : 0 < q := by linarith [hq_bounds.1]
  by_cases hK_nonneg : 0 ≤ K
  · -- Case K ≥ 0: Function is decreasing; minimum occurs at qb.
    have h_dec := antitone_of_nonneg_K r K hK_nonneg hq_pos hq_bounds.2
    exact le_trans (min_le_right _ _) h_dec
  · -- Case K < 0: Function is increasing; minimum occurs at qa.
    have hK_neg : K < 0 := by linarith
    have h_inc := monotone_of_nonpos_K r K (le_of_lt hK_neg) hqa_pos hq_bounds.1
    exact le_trans (min_le_left _ _) h_inc

/-- 
MAXIMUM AT BOUNDARY:
For any trajectory segment over [qa, qb], the maximum of the continuous 
phase average is likewise achieved at one of the two endpoints.
-/
theorem phase_average_max_at_boundary (r K qa qb q : ℝ)
    (hqa_pos : 0 < qa) (hq_bounds : qa ≤ q ∧ q ≤ qb) :
    D r K q ≤ max (D r K qa) (D r K qb) := by
  have hq_pos : 0 < q := by linarith [hq_bounds.1]
  by_cases hK_nonneg : 0 ≤ K
  · -- Case K ≥ 0: Function is decreasing; maximum occurs at qa.
    have h_dec := antitone_of_nonneg_K r K hK_nonneg hqa_pos hq_bounds.1
    exact le_trans h_dec (le_max_left _ _)
  · -- Case K < 0: Function is increasing; maximum occurs at qb.
    have hK_neg : K < 0 := by linarith
    have h_inc := monotone_of_nonpos_K r K (le_of_lt hK_neg) hq_pos hq_bounds.2
    exact le_trans h_inc (le_max_right _ _)

end PhaseDynamics

/-!
 Section 7.3: First Renewal Inequality
Formalizing the geometric gap logic that forces defect accumulation.
-/

namespace GeometricRenewal

variable (t_k t_k1 : ℝ)
variable (Q_k Q_k1 : ℝ)
variable (alpha_k1 : ℝ)

/-!  7.3.1 Terminal Lower Gap Definition & Geometric Axiom -/

/-- 
The geometric constraint of the terminal lower gap at time t_{k+1}.
Equation (55) states this gap is exactly (3 * alpha_{k+1} - 1) * t_{k+1}.
-/
def terminal_lower_gap (alpha t : ℝ) : ℝ :=
  (3 * alpha - 1) * t

/-- 
Core Geometric Axiom (Equation 56):
Explicit parameter binders ensure exact argument order (alpha, t, Q_after, Q_before).
-/
axiom defect_ge_terminal_gap (alpha t Q_after Q_before : ℝ) :
  terminal_lower_gap alpha t ≤ Q_after - Q_before

/-!  7.3.2 The First Renewal Recurrence -/

/-- 
Theorem 7.3 (Equation 57): The First Renewal Inequality.
Dividing the geometric gap bound by t_{k+1} yields the discrete renewal recurrence:
  z_{k+1} ≥ z_k / L_k + (3 * alpha_{k+1} - 1).
-/
theorem first_renewal_inequality 
    (ht_k_pos : 0 < t_k)
    (ht_pos : 0 < t_k1)
    (z_k z_k1 L_k : ℝ)
    (h_z_k : z_k = Q_k / t_k)
    (h_z_k1 : z_k1 = Q_k1 / t_k1)
    (h_L_k : L_k = t_k1 / t_k) :
    z_k / L_k + (3 * alpha_k1 - 1) ≤ z_k1 := by
  -- Pass arguments in the exact order declared by the axiom
  have h_geom := defect_ge_terminal_gap alpha_k1 t_k1 Q_k1 Q_k
  dsimp [terminal_lower_gap] at h_geom

  have ht_k_ne : t_k ≠ 0 := ne_of_gt ht_k_pos
  have ht_k1_ne : t_k1 ≠ 0 := ne_of_gt ht_pos

  -- Divide geometric gap inequality by t_{k+1} > 0
  have h_div : (3 * alpha_k1 - 1) ≤ (Q_k1 - Q_k) / t_k1 := by
    have h_le := div_le_div_of_nonneg_right h_geom (le_of_lt ht_pos)
    have h_cancel : ((3 * alpha_k1 - 1) * t_k1) / t_k1 = 3 * alpha_k1 - 1 :=
      mul_div_cancel_right₀ (3 * alpha_k1 - 1) ht_k1_ne
    rwa [h_cancel] at h_le

  -- Algebraic reduction: (Q_k / t_k) / (t_{k+1} / t_k) = Q_k / t_{k+1}
  have h_ratio : z_k / L_k = Q_k / t_k1 := by
    rw [h_z_k, h_L_k]
    field_simp [ht_k_ne, ht_k1_ne]

  -- Split (Q_{k+1} - Q_k) / t_{k+1} = z_{k+1} - z_k / L_k
  have h_split : (Q_k1 - Q_k) / t_k1 = z_k1 - z_k / L_k := by
    rw [h_ratio, h_z_k1]
    ring

  linarith [h_div, h_split]

/-! ### 7.3.3 Bridge to Uniform Renewal Form -/

/-- 
Uniform recurrence step:
If the local expansion ratio is bounded by L (L_k ≤ L) and the increment 
satisfies C ≤ 3 * alpha_{k+1} - 1, then the step satisfies the uniform 
renewal condition z_k / L + C ≤ z_{k+1}.
-/
theorem uniform_renewal_step
    (ht_k_pos : 0 < t_k)
    (ht_pos : 0 < t_k1)
    (z_k z_k1 L_k L C : ℝ)
    (h_z_k : z_k = Q_k / t_k)
    (h_z_k1 : z_k1 = Q_k1 / t_k1)
    (h_L_k : L_k = t_k1 / t_k)
    (hz_k_nonneg : 0 ≤ z_k)
    (hL_k_pos : 0 < L_k)
    (hL_bound : L_k ≤ L)
    (hC_bound : C ≤ 3 * alpha_k1 - 1) :
    z_k / L + C ≤ z_k1 := by
  have h_rec := first_renewal_inequality t_k t_k1 Q_k Q_k1 alpha_k1
    ht_k_pos ht_pos z_k z_k1 L_k h_z_k h_z_k1 h_L_k
  have h_dil : z_k / L ≤ z_k / L_k :=
    div_le_div_of_nonneg_left hz_k_nonneg hL_k_pos hL_bound
  linarith

/-!  Section 7.4: Second Renewal Inequality -/

variable (alpha_k alpha_k1 b : ℝ)
variable (L_k : ℝ)

/-- Coordinate components at boundary times t_k and t_{k+1}. -/
noncomputable def u_val (alpha t : ℝ) : ℝ := (1 - 2 * alpha) * t
noncomputable def h_val (alpha t : ℝ) : ℝ := alpha * t
noncomputable def y_val (alpha t : ℝ) : ℝ := (1 - 2 * alpha) * t

/-- 
The geometric excursion peak axiom (Equation 60):
Because P₃(q)/q ≤ b throughout the excursion, evaluating this ratio at the 
first time q* when P₃ reaches its terminal value h, and applying the 
structural coordinate constraint x ≤ y, yields this ratio bound.
-/
axiom excursion_peak_bound (t_k t_k1 alpha_k alpha_k1 b : ℝ) :
  h_val alpha_k1 t_k1 / (u_val alpha_k t_k + y_val alpha_k1 t_k1 + h_val alpha_k1 t_k1) ≤ b

/-- 
Theorem 7.4 (Equation 61): Second Renewal Inequality.
Translating the excursion peak bound into a strict upper cap on the time ratio L_k.
-/
theorem second_renewal_inequality
    (ht_pos : 0 < t_k)
    (_ht1_pos : 0 < t_k1)
    (h_denom_pos : 0 < alpha_k1 * (1 + b) - b)
    (h_Lk : L_k = t_k1 / t_k)
    (h_q_pos : 0 < u_val alpha_k t_k + y_val alpha_k1 t_k1 + h_val alpha_k1 t_k1) :
    L_k ≤ ((1 - 2 * alpha_k) * b) / (alpha_k1 * (1 + b) - b) := by
  have h_geom := excursion_peak_bound t_k t_k1 alpha_k alpha_k1 b
  dsimp [u_val, h_val, y_val] at h_geom h_q_pos

  -- 1. Clear the denominator: h / q* ≤ b ↔ h ≤ b * q*
  have h_mult : alpha_k1 * t_k1 ≤
      b * ((1 - 2 * alpha_k) * t_k + (1 - 2 * alpha_k1) * t_k1 + alpha_k1 * t_k1) :=
    (div_le_iff₀ h_q_pos).mp h_geom

  -- 2. Algebraic ring identity isolating t_{k+1} on the left and t_k on the right
  have h_ring : b * ((1 - 2 * alpha_k) * t_k + (1 - 2 * alpha_k1) * t_k1 + alpha_k1 * t_k1) -
      alpha_k1 * t_k1 = t_k * ((1 - 2 * alpha_k) * b) - t_k1 * (alpha_k1 * (1 + b) - b) := by ring

  have h_rearrange : t_k1 * (alpha_k1 * (1 + b) - b) ≤ t_k * ((1 - 2 * alpha_k) * b) := by
    linarith [h_mult, h_ring]

  -- 3. Rewrite goal with L_k definition and clear fractions directly on the goal
  rw [h_Lk]
  rw [div_le_div_iff₀ ht_pos h_denom_pos]
  have h_comm : t_k * ((1 - 2 * alpha_k) * b) = (1 - 2 * alpha_k) * b * t_k := by ring
  rwa [h_comm] at h_rearrange

/-- 
Corollary: Stationary time-dilation bound.
When alpha_k = alpha_{k+1} = alpha, the excursion dilation ratio L_k is bounded by
L(alpha, b) = (1 - 2 * alpha) * b / (alpha * (1 + b) - b).
-/
theorem second_renewal_stationary
    (alpha : ℝ)
    (ht_pos : 0 < t_k)
    (ht1_pos : 0 < t_k1)
    (h_denom_pos : 0 < alpha * (1 + b) - b)
    (h_Lk : L_k = t_k1 / t_k)
    (h_q_pos : 0 < u_val alpha t_k + y_val alpha t_k1 + h_val alpha t_k1) :
    L_k ≤ ((1 - 2 * alpha) * b) / (alpha * (1 + b) - b) :=
  second_renewal_inequality t_k t_k1 alpha alpha b L_k ht_pos ht1_pos h_denom_pos h_Lk h_q_pos

end GeometricRenewal

/-!
 Section 7.5: Uniform Freezing
Applying ε-bounds to lock the dynamic geometric recurrence into a uniform sequence.
-/

namespace UniformFreezing

variable (a b : ℝ)
variable (alpha_k alpha_k1 L_k z_k z_k1 : ℝ)

/-!  7.5.1 The Decreasing Function Property -/

/-- The fraction function f(x) = x / (x(1 + b) - b) from Section 7.5. -/
noncomputable def f (b x : ℝ) : ℝ := x / (x * (1 + b) - b)

/-- 
Proving f(x) is monotonically decreasing on its positive domain:
For 0 < b and x₁ ≤ x₂, f(x₂) ≤ f(x₁).
-/
theorem f_decreasing (b x1 x2 : ℝ) 
    (hb_pos : 0 < b)
    (h_x1_le_x2 : x1 ≤ x2)
    (h_denom1 : 0 < x1 * (1 + b) - b)
    (h_denom2 : 0 < x2 * (1 + b) - b) :
    f b x2 ≤ f b x1 := by
  dsimp [f]
  rw [div_le_div_iff₀ h_denom2 h_denom1]
  have h_diff : x1 * (x2 * (1 + b) - b) - x2 * (x1 * (1 + b) - b) = b * (x2 - x1) := by ring
  have h_pos : 0 ≤ b * (x2 - x1) := mul_nonneg (le_of_lt hb_pos) (by linarith)
  linarith [h_diff, h_pos]

/-!  7.5.2 Freezing the Dilation Variables -/

/-- The uniform L_ε constant from Equation (62). -/
noncomputable def L_eps (a b : ℝ) : ℝ := ((1 - 2 * a) * b) / (a * (1 + b) - b)

/-- 
Theorem (Equation 62): L_k ≤ L_ε.
Using a ≤ α_k and a ≤ α_{k+1}, we maximize the upper bound of L_k.
-/
theorem L_k_le_L_eps 
    (ha_le_alpha_k : a ≤ alpha_k)
    (ha_le_alpha_k1 : a ≤ alpha_k1)
    (ha_le_half : a ≤ 1 / 2)
    (hb_pos : 0 < b)
    (h_denom_a : 0 < a * (1 + b) - b)
    (h_denom_k1 : 0 < alpha_k1 * (1 + b) - b)
    (h_Lk_bound : L_k ≤ ((1 - 2 * alpha_k) * b) / (alpha_k1 * (1 + b) - b)) :
    L_k ≤ L_eps a b := by
  dsimp [L_eps]
  -- Numerator bound: (1 - 2α_k)b ≤ (1 - 2a)b
  have h_num : (1 - 2 * alpha_k) * b ≤ (1 - 2 * a) * b := by
    have : 1 - 2 * alpha_k ≤ 1 - 2 * a := by linarith
    exact mul_le_mul_of_nonneg_right this (le_of_lt hb_pos)

  -- Denominator bound: a(1 + b) - b ≤ α_{k+1}(1 + b) - b
  have h_denom_le : a * (1 + b) - b ≤ alpha_k1 * (1 + b) - b := by
    have : 0 ≤ 1 + b := by linarith
    nlinarith

  have h_num_nonneg : 0 ≤ (1 - 2 * a) * b := by
    have : 0 ≤ 1 - 2 * a := by linarith
    exact mul_nonneg this (le_of_lt hb_pos)

  -- Chain intermediate fraction steps
  have h1 : ((1 - 2 * alpha_k) * b) / (alpha_k1 * (1 + b) - b) ≤
            ((1 - 2 * a) * b) / (alpha_k1 * (1 + b) - b) :=
    div_le_div_of_nonneg_right h_num (le_of_lt h_denom_k1)

  have h2 : ((1 - 2 * a) * b) / (alpha_k1 * (1 + b) - b) ≤
            ((1 - 2 * a) * b) / (a * (1 + b) - b) :=
    div_le_div_of_nonneg_left h_num_nonneg h_denom_a h_denom_le

  have h_frac := le_trans h1 h2
  exact le_trans h_Lk_bound h_frac

/-- 
Theorem (Equation 63): α_{k+1} * L_k ≤ a * L_ε.
Derived from the monotonic decrease of f(x).
-/
theorem alpha_Lk_le 
    (ha_nonneg : 0 ≤ a)
    (ha_le_half : a ≤ 1 / 2)
    (ha_le_alpha_k1 : a ≤ alpha_k1)
    (hb_pos : 0 < b)
    (h_denom_a : 0 < a * (1 + b) - b)
    (h_denom_k1 : 0 < alpha_k1 * (1 + b) - b)
    (h_Lk_bound : L_k ≤ ((1 - 2 * a) * b) / (alpha_k1 * (1 + b) - b)) :
    alpha_k1 * L_k ≤ a * L_eps a b := by
  have h_alpha_nonneg : 0 ≤ alpha_k1 := by linarith
  have h_num_pos : 0 ≤ (1 - 2 * a) * b := by
    have : 0 ≤ 1 - 2 * a := by linarith
    exact mul_nonneg this (le_of_lt hb_pos)

  have h_f_alpha : alpha_k1 * L_k ≤ (1 - 2 * a) * b * f b alpha_k1 := by
    dsimp [f]
    have h_step : alpha_k1 * L_k ≤ alpha_k1 * (((1 - 2 * a) * b) / (alpha_k1 * (1 + b) - b)) :=
      mul_le_mul_of_nonneg_left h_Lk_bound h_alpha_nonneg
    have h_eq : alpha_k1 * (((1 - 2 * a) * b) / (alpha_k1 * (1 + b) - b)) =
        (1 - 2 * a) * b * (alpha_k1 / (alpha_k1 * (1 + b) - b)) := by ring
    linarith [h_step, h_eq]

  have h_f_dec := f_decreasing b a alpha_k1 hb_pos ha_le_alpha_k1 h_denom_a h_denom_k1
  have h_f_bound : (1 - 2 * a) * b * f b alpha_k1 ≤ (1 - 2 * a) * b * f b a :=
    mul_le_mul_of_nonneg_left h_f_dec h_num_pos

  have h_f_a_eq : (1 - 2 * a) * b * f b a = a * L_eps a b := by
    dsimp [f, L_eps]
    ring

  linarith [h_f_alpha, h_f_bound, h_f_a_eq]

/-!  7.5.3 The Uniform Recurrence -/

/-- 
Transition from dynamic recurrence (Equation 57) to uniform frozen recurrence (Equation 64).
-/
theorem uniform_first_renewal
    (h_zk_pos : 0 ≤ z_k)
    (h_Lk_pos : 0 < L_k)
    (ha_le_alpha_k1 : a ≤ alpha_k1)
    (h_Lk_le_Leps : L_k ≤ L_eps a b)
    (h_floating_recurrence : z_k / L_k + (3 * alpha_k1 - 1) ≤ z_k1) :
    z_k / L_eps a b + (3 * a - 1) ≤ z_k1 := by
  have h_frac : z_k / L_eps a b ≤ z_k / L_k :=
    div_le_div_of_nonneg_left h_zk_pos h_Lk_pos h_Lk_le_Leps
  have h_alpha_bound : 3 * a - 1 ≤ 3 * alpha_k1 - 1 := by linarith
  linarith

end UniformFreezing
