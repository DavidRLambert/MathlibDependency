import Mathlib


/-- Parameters for Schmidt's (α, β)-game on a metric space. -/
structure SchmidtParams where
  α : ℝ
  β : ℝ
  hα_pos : 0 < α
  hα_lt  : α < 1
  hβ_pos : 0 < β
  hβ_lt  : β < 1

-- Example instantiation: α = 0.5, β = 0.5
noncomputable def standardParams : SchmidtParams where
  α := 1/2
  β := 1/2
  hα_pos := by norm_num
  hα_lt  := by norm_num
  hβ_pos := by norm_num
  hβ_lt  := by norm_num

variable {X : Type*} [MetricSpace X]

/-- A move in Schmidt's game consists of a center point in space X and a positive radius. -/
structure GameBall (X : Type*) [MetricSpace X] where
  center : X
  radius : ℝ
  r_pos  : 0 < radius

/-- Convert a GameBall object into an actual set of points in the metric space. -/
def GameBall.toSet (b : GameBall X) : Set X :=
  Metric.closedBall b.center b.radius

/-- Ball inclusion proposition: b2 is completely contained in b1 -/
def IsSubBall (b2 b1 : GameBall X) : Prop :=
  b2.toSet ⊆ b1.toSet

/-- Alice's Move Rule: Given Bob's ball B, Alice must choose A such that:
    1. A ⊆ B (Inclusion constraint)
    2. radius(A) = α * radius(B) (Scaling constraint) -/
structure AliceMove (params : SchmidtParams) (B : GameBall X) where
  A : GameBall X
  sub : IsSubBall A B
  r_eq : A.radius = params.α * B.radius

/-- Bob's Move Rule: Given Alice's ball A, Bob must choose B' such that:
    1. B' ⊆ A (Inclusion constraint)
    2. radius(B') = β * radius(A) (Scaling constraint) -/
structure BobMove (params : SchmidtParams) (A : GameBall X) where
  B' : GameBall X
  sub : IsSubBall B' A
  r_eq : B'.radius = params.β * A.radius

/-- Lemma 1: Alice's ball has a strictly smaller radius than Bob's ball. -/
theorem alice_radius_lt (params : SchmidtParams) (B : GameBall X) (moveA : AliceMove params B) :
    moveA.A.radius < B.radius := by
  -- Substitute moveA.A.radius with α * B.radius
  rw [moveA.r_eq]
  -- Use non-linear arithmetic solver using α < 1 and r(B) > 0
  nlinarith [params.hα_lt, B.r_pos]

/-- Lemma 2: After one full round (Bob -> Alice -> Bob), the radius shrinks strictly. -/
--theorem round_radius_lt (params : SchmidtParams) (B : GameBall X)
--    (moveA : AliceMove params B) (moveB : BobMove params moveA.A) :
--    moveB.B'.radius < B.radius := by
--  -- Expand radius definitions: r(B') = β * (α * r(B))
--  rw [moveB.r_eq, moveA.r_eq]
--  -- Solve inequality given 0 < α < 1, 0 < β < 1, and r(B) > 0
--  nlinarith [params.hα_pos, params.hα_lt, params.hβ_pos, params.hβ_lt, B.r_pos]
theorem round_radius_lt (params : SchmidtParams) (B : GameBall X)
    (moveA : AliceMove params B) (moveB : BobMove params moveA.A) :
    moveB.B'.radius < B.radius := by
  have hB' : moveB.B'.radius = params.β * moveA.A.radius := moveB.r_eq
  have hA : moveA.A.radius = params.α * B.radius := moveA.r_eq
  have hq : params.β * params.α < 1 := by
    nlinarith [params.hα_pos, params.hα_lt, params.hβ_pos, params.hβ_lt]
  calc
    moveB.B'.radius
        = params.β * moveA.A.radius := hB'
    _ = params.β * (params.α * B.radius) := by rw [hA]
    _ = (params.β * params.α) * B.radius := by ring
    _ < 1 * B.radius := by nlinarith [hq, B.r_pos]
    _ = B.radius := by ring


/-- The combined contraction parameter q = α * β -/
def contractionParam (params : SchmidtParams) : ℝ :=
  params.α * params.β

/-- Proof that 0 < α * β < 1 -/
lemma contraction_in_bounds (params : SchmidtParams) :
    0 < contractionParam params ∧ contractionParam params < 1 := by
  constructor
  · unfold contractionParam
    nlinarith [params.hα_pos, params.hβ_pos]
  · unfold contractionParam
    nlinarith [params.hα_pos, params.hα_lt, params.hβ_pos, params.hβ_lt]

/-- Main Convergence Theorem: The sequence of radii r_0 * (α * β)^n tends to 0 as n -> ∞ -/
theorem radius_sequence_tendsto_zero (params : SchmidtParams) (r0 : ℝ) :
    Filter.Tendsto (fun (n : ℕ) => r0 * (contractionParam params) ^ n)
    Filter.atTop (nhds 0) := by
  have h_bounds := contraction_in_bounds params
  -- Apply Mathlib's theorem that q^n -> 0 when |q| < 1, then multiply by constant r0
  have h_pow : Filter.Tendsto (fun (n : ℕ) => (contractionParam params) ^ n) Filter.atTop (nhds 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_lt_one
    · linarith [h_bounds.1]
    · exact h_bounds.2
  -- Multiplying a sequence tending to 0 by a constant r0 still yields 0
  simpa using Filter.Tendsto.const_mul r0 h_pow


variable {X : Type*} [MetricSpace X] [CompleteSpace X]

/-- A valid infinite nested sequence of closed balls whose radii decay to zero. -/
structure NestedBallSeq (X : Type*) [MetricSpace X] where
  ball : ℕ → GameBall X
  nested : ∀ n, (ball (n + 1)).toSet ⊆ (ball n).toSet
  radii_tendsto : Filter.Tendsto (fun n => (ball n).radius) Filter.atTop (nhds 0)

/-- Cantor's Intersection Theorem for closed balls:
    An infinite sequence of nested closed balls with vanishing radii
    has a UNIQUE point of intersection x*. -/
--theorem nested_balls_intersection_unique (seq : NestedBallSeq X) :
--    ∃! x : X, ∀ n : ℕ, x ∈ (seq.ball n).toSet := by
--  sorry
  -- Proof strategy in Lean:
  -- 1. Show the sequence of ball centers c_n is a Cauchy sequence.
  -- 2. Use [CompleteSpace X] to get the limit point x*.
  -- 3. Show x* is in every ball B_n (since balls are closed).
  -- 4. Prove uniqueness using r_n -> 0.
-- Target set S is a subset of space X (e.g., Badly Approximable Numbers in ℝ). -/

-- (Assuming NestedBallSeq is defined as before)

theorem nested_balls_intersection_unique (seq : NestedBallSeq X) :
    ∃! x : X, ∀ n : ℕ, x ∈ (seq.ball n).toSet := by

  -- STEP 1: Define our sequences for centers and radii to make the math cleaner
  let c := fun n => (seq.ball n).center
  let r := fun n => (seq.ball n).radius

  -- STEP 2: Prove the sequence of centers is a Cauchy sequence
-- STEP 2: Prove the sequence of centers is a Cauchy sequence
  have hCauchy : CauchySeq c := by
    -- Use the alternative metric characterization for Cauchy sequences
    apply Metric.cauchySeq_iff'.mpr
    intro ε hε

    -- From seq.radii_tendsto, the radii eventually become smaller than ε
    have h_tendsto := Metric.tendsto_atTop.mp seq.radii_tendsto ε hε
    rcases h_tendsto with ⟨N, hN⟩

    -- Provide this N as the Cauchy bound
    use N
    intro m hm

    -- Prove that since m ≥ N, ball m is entirely nested inside ball N
    have h_subset : (seq.ball m).toSet ⊆ (seq.ball N).toSet := by
      induction hm with
      | refl => exact subset_rfl
      | step hm' ih => exact Set.Subset.trans (seq.nested _) ih

    -- The center of ball m is inside ball m (distance is 0 ≤ r_m)
    have h_cm_in_Bm : c m ∈ (seq.ball m).toSet :=
      Metric.mem_closedBall_self (le_of_lt (seq.ball m).r_pos)

    -- Therefore, by our nesting property, the center of ball m is also in ball N
    have h_cm_in_BN : c m ∈ (seq.ball N).toSet := h_subset h_cm_in_Bm

    -- By definition of a closed ball, this bounds the distance between centers by r_N
    have h_dist_centers : dist (c N) (c m) ≤ r N := h_cm_in_BN

    -- From the radii limit, the distance from r_N to 0 is less than ε
    have h_limit_N : dist (r N) 0 < ε := hN N (le_refl N)

    -- Convert the metric distance on ℝ to a strict inequality r_N < ε
--    have h_rN_lt_ε : r N < ε := by
--      calc
--        r N ≤ |r N| := le_abs_self (r N)
--        _ = norm(r N) := (Real.norm_eq_abs (r N)).symm
--        _ = dist (r N) 0 := (dist_zero_right (r N)).symm
--        _ < ε := h_limit_N
-- Convert the metric distance on ℝ to a strict inequality r N < ε
    have h_rN_lt_ε : r N < ε := by
      calc
        r N ≤ |r N| := le_abs_self (r N)
        _ = |r N - 0| := by rw [sub_zero]
        _ = dist (r N) 0 := (Real.dist_eq (r N) 0).symm
        _ < ε := h_limit_N

    -- Conclude that dist (c m) (c N) < ε by combining the bounds
--    rw [dist_comm]
--    exact lt_of_le_of_lt h_dist_centers h_rN_lt_ε
-- Flip the arguments of the distance function using symmetry
    rw [dist_comm (c m) (c N)]
    -- Chain the ≤ and < inequalities together
    exact lt_of_le_of_lt h_dist_centers h_rN_lt_ε

  -- STEP 3: Because X is a [CompleteSpace], we can extract the limit point x*
  -- `cauchySeq_tendsto_of_complete` is the Mathlib theorem that bridges
  -- Cauchy sequences to topological limits.
  rcases cauchySeq_tendsto_of_complete hCauchy with ⟨x_star, hx_lim⟩

  -- STEP 4: Tell Lean to use x_star to satisfy the "Exists" part of the theorem
  use x_star

  -- STEP 5: The `constructor` tactic splits the remaining goal into Existence and Uniqueness
  constructor

  · -- SUB-GOAL 1: EXISTENCE (Prove x_star is in every ball B_n)
    intro n
    -- Proof Strategy: B_n is a closed ball. The sequence of centers c_m
    -- eventually lives entirely inside B_n. Because closed sets contain all
    -- their limit points, the limit x_star must also be in B_n.
    -- (Implemented using Mathlib's `IsClosed.mem_of_tendsto`)
    sorry

  · -- SUB-GOAL 2: UNIQUENESS (Prove any other point y in all balls equals x_star)
    intro y hy
    -- In a metric space, two points are equal if the distance between them is 0.
    apply Metric.eq_of_dist_eq_zero

    -- Proof Strategy: For any n, dist(x_star, y) ≤ dist(x_star, c_n) + dist(c_n, y).
    -- Because both points are in B_n, the distance between them is bounded by 2 * r_n.
    -- Since r_n limits to 0, the distance must be exactly 0.
    -- (Implemented using `tendsto_nhds_unique` and the Squeeze Theorem)
    sorry
def TargetSet (X : Type*) := Set X

/-- Alice wins a played sequence of balls if the unique intersection point lies inside S. -/
def AliceWinsSequence (S : TargetSet X) (seq : NestedBallSeq X) : Prop :=
  ∀ x : X, (∀ n : ℕ, x ∈ (seq.ball n).toSet) → x ∈ S

/-- Bob wins a played sequence if the unique intersection point falls outside S. -/
def BobWinsSequence (S : TargetSet X) (seq : NestedBallSeq X) : Prop :=
  ¬ AliceWinsSequence S seq
variable {X : Type*} [MetricSpace X]

/-- A strategy for Alice is a function that provides a valid AliceMove
    for any possible ball B chosen by Bob. -/
def AliceStrategy (params : SchmidtParams) :=
  (B : GameBall X) → AliceMove params B
/-- A sequence of Bob's balls constitutes a valid play against Alice's strategy if
    every subsequent ball B_{n+1} is a valid BobMove inside Alice's response to B_n. -/
def isValidPlay (params : SchmidtParams) (fA : AliceStrategy params)
    (B_seq : ℕ → GameBall X) : Prop :=
  ∀ n, ∃ (moveB : BobMove params (fA (B_seq n))), moveB.B' = B_seq (n + 1)
/-- Alice's strategy is winning if every valid sequence of plays against it
    results in the limit point being in the target set S. -/
def isWinningStrategy (params : SchmidtParams) (S : Set X)
    (fA : AliceStrategy params) : Prop :=
  ∀ (B_seq : ℕ → GameBall X),
    isValidPlay params fA B_seq →
    ∀ (x : X), (∀ n, x ∈ (B_seq n).toSet) → x ∈ S
