import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Linarith.Frontend

inductive ArithExpr : Type
| literal : Nat → ArithExpr
| add : ArithExpr → ArithExpr → ArithExpr
| mul : ArithExpr → ArithExpr → ArithExpr
open ArithExpr

instance : Repr ArithExpr where
  reprPrec : ArithExpr → Nat → Std.Format :=
    let rec impl
    | (literal n), _ => s!"{n}"
    | (add e1 e2), _ => s!"({impl e1 0} + {impl e2 0})"
    | (mul e1 e2), _ => s!"({impl e1 1} * {impl e2 1})"
    impl

namespace ArithExpr

abbrev isLiteral : ArithExpr → Bool
| (literal _) => true
| _ => false

lemma isLiteral_extract (e : ArithExpr) :
    e.isLiteral = true → ∃ n : Nat, e = literal n := by
  intro h
  cases e with
  | literal n => exact ⟨n, rfl⟩
  | add e1 e2 => contradiction
  | mul e1 e2 => contradiction

def evalOneStep : ArithExpr → ArithExpr
| (literal n) => literal n
| (add e1 e2) =>
  match e1 with
  | (literal n1) =>
    match e2 with
    | (literal n2) => literal (n1 + n2)
    | _ => add (literal n1) (evalOneStep e2)
  | _ => add (evalOneStep e1) e2
| (mul e1 e2) =>
  match e1 with
  | (literal n1) =>
    match e2 with
    | (literal n2) => literal (n1 * n2)
    | _ => mul (literal n1) (evalOneStep e2)
  | _ => mul (evalOneStep e1) e2

abbrev opsCount : ArithExpr → Nat
| (literal _) => 0
| (add e1 e2) => 1 + e1.opsCount + e2.opsCount
| (mul e1 e2) => 1 + e1.opsCount + e2.opsCount

lemma opsCount_zero_then_literal (e : ArithExpr) :
    e.opsCount = 0 → ∃ n : Nat, e = literal n := by
  intro h
  cases e with
  | literal n => simp [h]
  | add e1 e2 => simp at h -- contradiction
  | mul e1 e2 => simp at h -- contradiction

lemma opsCount_nonzero_if_not_literal (e : ArithExpr) (h : e.isLiteral = false) : e.opsCount > 0 := by
  cases e with
  | literal n => contradiction
  | add e1 e2 => simp
  | mul e1 e2 => simp

lemma evalOneStep_lit_add_nonlit (lLit : Nat) (rNonlit : ArithExpr) (ev : rNonlit.isLiteral = false) :
    ((literal lLit).add rNonlit).evalOneStep = (literal lLit).add (rNonlit.evalOneStep) := by
  cases h : rNonlit with
  | literal n => rw [h] at ev; contradiction
  | add e1 e2 => simp [evalOneStep]
  | mul e1 e2 => simp [evalOneStep]

lemma evalOneStep_lit_mul_nonlit (lLit : Nat) (rNonlit : ArithExpr) (ev : rNonlit.isLiteral = false) :
    ((literal lLit).mul rNonlit).evalOneStep = (literal lLit).mul (rNonlit.evalOneStep) := by
  cases h : rNonlit with
  | literal n => rw [h] at ev; contradiction
  | add e1 e2 => simp [evalOneStep]
  | mul e1 e2 => simp [evalOneStep]

lemma evalOneStep_nonlit_add (lNonlit : ArithExpr) (r : ArithExpr) (ev : lNonlit.isLiteral = false) :
    (lNonlit.add r).evalOneStep = lNonlit.evalOneStep.add r := by
  cases h : lNonlit with
  | literal n => rw [h] at ev; contradiction
  | add e1 e2 => simp [evalOneStep]
  | mul e1 e2 => simp [evalOneStep]

lemma evalOneStep_nonlit_mul (lNonlit : ArithExpr) (r : ArithExpr) (ev : lNonlit.isLiteral = false) :
    (lNonlit.mul r).evalOneStep = lNonlit.evalOneStep.mul r := by
  cases h : lNonlit with
  | literal n => rw [h] at ev; contradiction
  | add e1 e2 => simp [evalOneStep]
  | mul e1 e2 => simp [evalOneStep]

theorem evalOneStep_progress (e : ArithExpr) : (evalOneStep e).opsCount = e.opsCount - 1 := by
  induction e with
  | literal n => -- e is already a literal, so no reduction happens
    simp [evalOneStep]

  | add e1 e2 ih1 ih2 =>
    by_cases h : e1.isLiteral = true
    · -- e1 is a literal
      rcases isLiteral_extract e1 h with ⟨n1, rfl⟩
      cases h : e2 with
      | literal n2 => -- both e1 and e2 are literals. Reduction actually happens in this branch
        simp [evalOneStep]
      | add e21 e22 => -- e1 is a literal but e2 is not, so use induction hypothesis
        rw [←h, evalOneStep_lit_add_nonlit _ _ (by simp [h]), opsCount]
        simp only [ih2]
        simp +arith [opsCount, h]
      | mul e21 e22 => -- exactly the same as add case
        rw [←h, evalOneStep_lit_add_nonlit _ _ (by simp [h]), opsCount]
        simp only [ih2]
        simp +arith [opsCount, h]
    · -- e1 is not a literal, so use induction hypothesis
      rw [evalOneStep_nonlit_add _ _ (by simp [h])]
      have e1opsCount_nonzero : 1 ≤ e1.opsCount := by exact opsCount_nonzero_if_not_literal _ (by simp [h])
      simp +arith [opsCount, ih1, h, e1opsCount_nonzero]

  | mul e1 e2 ih1 ih2 => -- Similar to the add case
    by_cases h : e1.isLiteral = true
    · rcases isLiteral_extract e1 h with ⟨n1, rfl⟩
      cases h : e2 with
      | literal n2 =>
        simp [evalOneStep]
      | add e21 e22 =>
        rw [←h, evalOneStep_lit_mul_nonlit _ _ (by simp [h]), opsCount]
        simp only [ih2]
        simp +arith [opsCount, h]
      | mul e21 e22 =>
        rw [←h, evalOneStep_lit_mul_nonlit _ _ (by simp [h]), opsCount]
        simp only [ih2]
        simp +arith [opsCount, h]
    · rw [evalOneStep_nonlit_mul _ _ (by simp [h])]
      have e1opsCount_nonzero : 1 ≤ e1.opsCount := by exact opsCount_nonzero_if_not_literal _ (by simp [h])
      simp +arith [opsCount, ih1, h, e1opsCount_nonzero]

lemma evalOneStep_iterated_progress (e : ArithExpr) (n : Nat) :
    (evalOneStep^[n] e).opsCount = e.opsCount - n := by
  induction n generalizing e with
  | zero      => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih e.evalOneStep, evalOneStep_progress e]
    simp +arith [Nat.sub_sub]

def evalViaSteps (expr: ArithExpr): Nat :=
  match evalOneStep^[expr.opsCount] expr with
  | (literal n) => n
  | _           => 0 -- this is impossible; evalViaSteps_result will prove this

lemma evalViaSteps_result (expr: ArithExpr) : evalOneStep^[expr.opsCount] expr = literal (evalViaSteps expr) := by
  dsimp only [evalViaSteps]
  have resultHasNoOps : (evalOneStep^[expr.opsCount] expr).opsCount = 0 := by
    simp [evalOneStep_iterated_progress _ _]
  rcases opsCount_zero_then_literal _ resultHasNoOps with ⟨_, eq⟩
  rw [eq]

end ArithExpr

inductive ArithEvalFrame : Type
| thenEvalRightAdd : ArithExpr → ArithEvalFrame -- [HOLE + e]
| thenAddLitLeft : Nat → ArithEvalFrame -- [n + HOLE]
| thenEvalRightMul : ArithExpr → ArithEvalFrame -- [HOLE * e]
| thenMulLitLeft : Nat → ArithEvalFrame -- [n * HOLE]
open ArithEvalFrame

namespace ArithEvalFrame

instance : Repr ArithEvalFrame where
  reprPrec
  | (thenEvalRightAdd e), _ => s!"# + ({repr e})"
  | (thenAddLitLeft n), _ => s!"{n} + #"
  | (thenEvalRightMul e), _ => s!"# * ({repr e})"
  | (thenMulLitLeft n), _ => s!"{n} * #"

def frameOpCount : ArithEvalFrame → Nat
| (thenEvalRightAdd e) => 1 + e.opsCount
| (thenEvalRightMul e) => 1 + e.opsCount
| (thenAddLitLeft _) => 1
| (thenMulLitLeft _) => 1

end ArithEvalFrame

structure ArithmeticCKMachine : Type where
  controlString: ArithExpr
  frames : List ArithEvalFrame
deriving Repr

namespace ArithmeticCKMachine
open ArithExpr
open ArithEvalFrame

abbrev init (e : ArithExpr) : ArithmeticCKMachine := ⟨e, []⟩

def machineStateOpCount (machine : ArithmeticCKMachine): Nat :=
  machine.controlString.opsCount + (machine.frames.map frameOpCount).sum

def step : ArithmeticCKMachine → ArithmeticCKMachine
| ⟨add e1 e2, frames⟩ => ⟨e1, thenEvalRightAdd e2 :: frames⟩
| ⟨mul e1 e2, frames⟩ => ⟨e1, thenEvalRightMul e2 :: frames⟩
| ⟨literal n, frames⟩ =>
    match frames with
    | (thenEvalRightAdd e1) :: frames' => ⟨e1, thenAddLitLeft n :: frames'⟩
    | (thenAddLitLeft n1)   :: frames' => ⟨literal (n1 + n), frames'⟩
    | (thenEvalRightMul e1) :: frames' => ⟨e1, thenMulLitLeft n :: frames'⟩
    | (thenMulLitLeft n1)   :: frames' => ⟨literal (n1 * n), frames'⟩
    | [] => ⟨literal n, []⟩

/--
This function calculates the "cost" of evaluating an expression using the CK machine.

To evaluate (1 + 2) for example, the CK machine needs to perform 3 steps, transitioning through:
 - ⟨1 + 2, []⟩
 - ⟨1, [# + (2)]⟩
 - ⟨2, [1 + #]⟩
 - ⟨3, []⟩

By inspection, we would like to assign
 - cost 3 to the state ⟨1 + 2, []⟩
 - cost 2 to the state ⟨1, [# + (2)]⟩
 - cost 1 to the state ⟨2, [1 + #]⟩
 - cost 0 to the state ⟨literal 0, []⟩.
-/
def evalCost (machine : ArithmeticCKMachine): Nat :=
  let ⟨control, frames⟩ := machine
  let frameCosts := frames.map (fun f =>
    match f with
    | thenEvalRightAdd e => e.opsCount * 3 + 2
    | thenAddLitLeft _   => 1
    | thenEvalRightMul e => e.opsCount * 3 + 2
    | thenMulLitLeft _   => 1
  )
  control.opsCount * 3 + frameCosts.sum

lemma evalCost_zero_then_halt_state (machine : ArithmeticCKMachine) :
    machine.evalCost = 0 → ∃n : Nat, machine = ⟨literal n, []⟩ := by
  intro h
  rcases machine with ⟨control, frames⟩
  cases hc : control with
  | literal n =>
    cases hf : frames with
    | nil => exact ⟨n, rfl⟩
    | cons head tail =>
      cases head with
      | thenEvalRightAdd _ => simp [hf, evalCost] at h -- contradiction
      | thenAddLitLeft _   => simp [hf, evalCost] at h -- contradiction
      | thenEvalRightMul _ => simp [hf, evalCost] at h -- contradiction
      | thenMulLitLeft _   => simp [hf, evalCost] at h -- contradiction
  | add e1 e2 => simp [hc, evalCost] at h -- contradiction
  | mul e1 e2 => simp [hc, evalCost] at h -- contradiction

lemma evalCost_progress (machine : ArithmeticCKMachine) :
    machine.step.evalCost = machine.evalCost - 1 := by
  dsimp only [step]
  rcases machine with ⟨control, frames⟩
  cases hc : control with
  | literal n =>
    dsimp only
    cases hf : frames with
    | nil => simp [evalCost]
    | cons head tail =>
      cases head with
      | thenEvalRightAdd _ => simp +arith [evalCost]
      | thenAddLitLeft _   => simp +arith [evalCost]
      | thenEvalRightMul _ => simp +arith [evalCost]
      | thenMulLitLeft _   => simp +arith [evalCost]
  | add e1 e2 =>
    simp +arith [evalCost, List.map_cons, List.sum_cons, opsCount]
  | mul e1 e2 =>
    simp +arith [evalCost, List.map_cons, List.sum_cons, opsCount]

lemma evalCost_iterated_progress (machine : ArithmeticCKMachine) (n : Nat) :
    (step^[n] machine).evalCost = machine.evalCost - n := by
  induction n generalizing machine with
  | zero => simp [evalCost]
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih machine.step, evalCost_progress machine]
    simp +arith [Nat.sub_sub]

def evalViaCKMachine (initExpr : ArithExpr) : Nat :=
  let result := step^[initExpr.opsCount * 3] (init initExpr)
  match result.controlString with
  | literal n => n
  | _ => 0 -- this is impossible; evalViaCKMachine_result will prove this

lemma evalViaCKMachine_result (initExpr : ArithExpr) :
    step^[initExpr.opsCount * 3] (init initExpr) = ⟨literal (evalViaCKMachine initExpr), []⟩ := by
  simp [evalViaCKMachine]
  let result := step^[initExpr.opsCount * 3] (init initExpr)
  have resultCost_eq_zero : result.evalCost = 0 := by
    unfold result
    simp only [evalCost_iterated_progress _ _]
    simp [evalCost]
  rcases evalCost_zero_then_halt_state result resultCost_eq_zero with ⟨n, eq⟩
  unfold result at eq; rw [eq]

end ArithmeticCKMachine

namespace ArithmeticCKMachine
open ArithExpr
open ArithEvalFrame

-- Reconstruct the "current whole expression" from the CK machine state
def stitchUp : (term : ArithExpr) → (contStack : List ArithEvalFrame) → ArithExpr
| e, [] => e
| e, (thenEvalRightAdd e1) :: frames => stitchUp (add e e1) frames
| e, (thenAddLitLeft n) :: frames    => stitchUp (add (literal n) e) frames
| e, (thenEvalRightMul e1) :: frames => stitchUp (mul e e1) frames
| e, (thenMulLitLeft n) :: frames    => stitchUp (mul (literal n) e) frames

def reductionCountUptoIndex (initExpr : ArithExpr) (idx : Nat) : Nat :=
  (List.range idx)
    |>.filter (isReducingTransition initExpr)
    |>.length
  where
    isReducingTransition (expr : ArithExpr) i :=
      let ⟨control, frames⟩ := step^[i] (init expr)
      match control with
      | literal _ =>
        match frames with
        | (thenAddLitLeft _) :: _ => true
        | (thenMulLitLeft _) :: _ => true
        | _ => false
      | _ => false

lemma reductionCountUptoIndex_nondecreasing (initExpr : ArithExpr) (idx : Nat) :
    let prev := reductionCountUptoIndex initExpr idx
    let next := reductionCountUptoIndex initExpr (idx + 1)
    prev = next ∨ prev.succ = next := by
  by_cases h : reductionCountUptoIndex.isReducingTransition initExpr idx
  · simp [reductionCountUptoIndex, List.range_succ, h]
  · simp [reductionCountUptoIndex, List.range_succ, h]

private lemma iterate_succ_apply_outer {α : Type} {f : α → α} (n : ℕ) (x : α) : f^[n.succ] x = f (f^[n] x) := by
  rw [Nat.succ_eq_add_one, Nat.add_comm, Function.iterate_add_apply (α := α) f 1 n, Function.iterate_one]

-- TODO: simplify?
lemma machineStateOpCount_plus_reductionCountUptoIndex_preserved (expr : ArithExpr) (n : Nat) :
    (step^[n.succ] (init expr)).machineStateOpCount + (reductionCountUptoIndex expr n.succ) =
    (step^[n] (init expr)).machineStateOpCount + (reductionCountUptoIndex expr n) := by
  rw [iterate_succ_apply_outer]
  rcases h : step^[n] (init expr) with ⟨control, frames⟩
  cases hc : control with
  | literal _ =>
    cases hf : frames with
    | nil => simp [step, reductionCountUptoIndex, List.range_succ, reductionCountUptoIndex.isReducingTransition, h, hc, hf]
    | cons head tail =>
      cases head with
      | thenEvalRightAdd e =>
        simp +arith [
          step, machineStateOpCount, frameOpCount, reductionCountUptoIndex, List.range_succ,
          reductionCountUptoIndex.isReducingTransition, h, hc, hf
        ]
      | thenEvalRightMul e => -- same as previous branch
        simp +arith [
          step, machineStateOpCount, frameOpCount, reductionCountUptoIndex, List.range_succ,
          reductionCountUptoIndex.isReducingTransition, h, hc, hf
        ]
      | thenAddLitLeft n' =>
        have : reductionCountUptoIndex.isReducingTransition expr n = true := by
          simp [reductionCountUptoIndex.isReducingTransition, h, hc, hf]
        simp +arith [
          step, machineStateOpCount, frameOpCount, reductionCountUptoIndex,
          List.range_succ, List.filter_cons_of_pos this
        ]
      | thenMulLitLeft n' => -- same as previous branch
        have : reductionCountUptoIndex.isReducingTransition expr n = true := by
          simp [reductionCountUptoIndex.isReducingTransition, h, hc, hf]
        simp +arith [
          step, machineStateOpCount, frameOpCount, reductionCountUptoIndex,
          List.range_succ, List.filter_cons_of_pos this
        ]
  | add e1 e2 =>
    simp +arith [
      step, opsCount, machineStateOpCount, frameOpCount, reductionCountUptoIndex, List.range_succ,
      reductionCountUptoIndex.isReducingTransition, h, hc
    ]
  | mul e1 e2 =>
    simp +arith [
      step, opsCount, machineStateOpCount, frameOpCount, reductionCountUptoIndex, List.range_succ,
      reductionCountUptoIndex.isReducingTransition, h, hc
    ]

lemma machineStateOpCount_plus_reductionCountUptoIndex_constant (expr : ArithExpr) (n : Nat) :
    (step^[n] (init expr)).machineStateOpCount + (reductionCountUptoIndex expr n) = expr.opsCount := by
  induction n with
  | zero      => simp [machineStateOpCount, reductionCountUptoIndex]
  | succ n ih => rw [machineStateOpCount_plus_reductionCountUptoIndex_preserved expr n, ih]

-- TODO: simplify?
lemma stitchUp_nonlit_evalOneStep
    (e : ArithExpr) (fs : List ArithEvalFrame)
    (h : e.isLiteral = false) :
    (stitchUp e fs).evalOneStep = stitchUp (evalOneStep e) fs := by
  induction fs generalizing e with
  | nil => simp [stitchUp]
  | cons f fs ih =>
    cases f with
    | thenEvalRightAdd e1 =>
      nth_rw 2 [stitchUp]
      rw [←evalOneStep_nonlit_add e e1 h, ←ih (e.add e1) (by simp)]
      apply congrArg evalOneStep
      simp [stitchUp]
    | thenEvalRightMul e1 =>
      nth_rw 2 [stitchUp]
      rw [←evalOneStep_nonlit_mul e e1 h, ←ih (e.mul e1) (by simp)]
      apply congrArg evalOneStep
      simp [stitchUp]
    | thenAddLitLeft n =>
      nth_rw 2 [stitchUp]
      rw [←evalOneStep_lit_add_nonlit n e h, ←ih (add (literal n) e) (by simp)]
      apply congrArg evalOneStep
      simp [stitchUp]
    | thenMulLitLeft n =>
      nth_rw 2 [stitchUp]
      rw [←evalOneStep_lit_mul_nonlit n e h, ←ih (mul (literal n) e) (by simp)]
      apply congrArg evalOneStep
      simp [stitchUp]

lemma stitchUp_lit_thenAddLitLeft_evalOneStep (n m : Nat) :
    (stitchUp (literal n) (thenAddLitLeft m :: fs)).evalOneStep = stitchUp (literal (m + n)) fs := by
  rw [
    stitchUp,
    stitchUp_nonlit_evalOneStep _ fs (by simp),
    evalOneStep
  ]

lemma stitchUp_lit_thenMulLitLeft_evalOneStep (n m : Nat) :
    (stitchUp (literal n) (thenMulLitLeft m :: fs)).evalOneStep = stitchUp (literal (m * n)) fs := by
  rw [
    stitchUp,
    stitchUp_nonlit_evalOneStep _ fs (by simp),
    evalOneStep
  ]

-- TODO: simplify?
theorem stitchUp_traces_evalOneStep (initExpr : ArithExpr) (idx : Nat) :
    let ⟨t, s⟩ := step^[idx] (init initExpr)
    stitchUp t s = evalOneStep^[reductionCountUptoIndex initExpr idx] initExpr := by
  induction idx with
  | zero => simp [stitchUp, reductionCountUptoIndex]
  | succ idx ih =>
    rcases machineAtIdx : (step^[idx] (init initExpr)) with ⟨t, s⟩
    simp [machineAtIdx] at ih
    cases t with
    | literal n =>
        cases s with
        | nil => -- halted: no reduction happens
          simp [iterate_succ_apply_outer, machineAtIdx, step, stitchUp]
          cases reductionCountUptoIndex_nondecreasing initExpr idx with
          | inl h' => rw [←h', ←ih, stitchUp]
          | inr h' => rw [←h', iterate_succ_apply_outer, ←ih, stitchUp, evalOneStep]
        | cons f fs =>
          cases f with
          | thenAddLitLeft m => -- an actual reduction happens here
            rw [iterate_succ_apply_outer, machineAtIdx]
            simp only [step]
            have : reductionCountUptoIndex initExpr (idx.succ) = reductionCountUptoIndex initExpr idx + 1 := by
              have : reductionCountUptoIndex.isReducingTransition initExpr idx = true := by simp [reductionCountUptoIndex.isReducingTransition, machineAtIdx]
              simp [reductionCountUptoIndex, List.range_succ, List.filter_cons_of_pos this]
            rw [this, iterate_succ_apply_outer, ←ih, stitchUp_lit_thenAddLitLeft_evalOneStep]
          | thenMulLitLeft m => -- same as previous branch
            rw [iterate_succ_apply_outer, machineAtIdx]
            simp only [step]
            have : reductionCountUptoIndex initExpr (idx.succ) = reductionCountUptoIndex initExpr idx + 1 := by
              have : reductionCountUptoIndex.isReducingTransition initExpr idx = true := by simp [reductionCountUptoIndex.isReducingTransition, machineAtIdx]
              simp [reductionCountUptoIndex, List.range_succ, List.filter_cons_of_pos this]
            rw [this, iterate_succ_apply_outer, ←ih, stitchUp_lit_thenMulLitLeft_evalOneStep]
          | thenEvalRightAdd e₂ => -- no reduction happens here, stitchUp must be preserved
            have : reductionCountUptoIndex initExpr (idx.succ) = reductionCountUptoIndex initExpr idx := by
              have : reductionCountUptoIndex.isReducingTransition initExpr idx = false := by simp [reductionCountUptoIndex.isReducingTransition, machineAtIdx]
              simp [reductionCountUptoIndex, List.range_succ, this]
            rw [this, iterate_succ_apply_outer, machineAtIdx, step, ←ih]
            simp [stitchUp]
          | thenEvalRightMul e₂ => -- same as previous branch
            have : reductionCountUptoIndex initExpr (idx.succ) = reductionCountUptoIndex initExpr idx := by
              have : reductionCountUptoIndex.isReducingTransition initExpr idx = false := by simp [reductionCountUptoIndex.isReducingTransition, machineAtIdx]
              simp [reductionCountUptoIndex, List.range_succ, this]
            rw [this, iterate_succ_apply_outer, machineAtIdx, step, ←ih]
            simp [stitchUp]
    | add e₁ e₂ =>
      have : reductionCountUptoIndex initExpr (idx.succ) = reductionCountUptoIndex initExpr idx := by
        have : reductionCountUptoIndex.isReducingTransition initExpr idx = false := by simp [reductionCountUptoIndex.isReducingTransition, machineAtIdx]
        simp [reductionCountUptoIndex, List.range_succ, this]
      rw [this, iterate_succ_apply_outer, machineAtIdx, step, ←ih]
      simp [stitchUp]
    | mul e₁ e₂ =>
      have : reductionCountUptoIndex initExpr (idx.succ) = reductionCountUptoIndex initExpr idx := by
        have : reductionCountUptoIndex.isReducingTransition initExpr idx = false := by simp [reductionCountUptoIndex.isReducingTransition, machineAtIdx]
        simp [reductionCountUptoIndex, List.range_succ, this]
      rw [this, iterate_succ_apply_outer, machineAtIdx, step, ←ih]
      simp [stitchUp]

lemma totalReductionCount (expr : ArithExpr) :
    reductionCountUptoIndex expr (expr.opsCount * 3) = expr.opsCount := by
  nth_rw 2 [←machineStateOpCount_plus_reductionCountUptoIndex_constant expr (expr.opsCount * 3)]
  simp [evalViaCKMachine_result, machineStateOpCount]

theorem evalViaCKMachine_evalViaSteps (expr : ArithExpr) : evalViaCKMachine expr = evalViaSteps expr := by
  apply ArithExpr.literal.inj
  rw [
    ←evalViaSteps_result,
    ←totalReductionCount expr,
    ←stitchUp_traces_evalOneStep expr (expr.opsCount * 3),
    evalViaCKMachine_result expr
  ]
  dsimp only [stitchUp]

end ArithmeticCKMachine
