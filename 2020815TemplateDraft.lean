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
