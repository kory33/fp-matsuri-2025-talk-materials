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

def isLiteral : ArithExpr → Bool
| (literal _) => true
| _ => false

lemma isLiteral_extract (e : ArithExpr) :
    e.isLiteral = true → ∃ n : Nat, e = literal n := by
  intro h
  cases e with
  | literal n => exact ⟨n, rfl⟩
  | add e1 e2 => simp [isLiteral] at h -- contradiction
  | mul e1 e2 => simp [isLiteral] at h -- contradiction

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

-- The size of an expression is defined as the number of operations in it.
def size : ArithExpr → Nat
| (literal _) => 0
| (add e1 e2) => 1 + size e1 + size e2
| (mul e1 e2) => 1 + size e1 + size e2

lemma size_zero_then_literal (e : ArithExpr) :
    e.size = 0 → ∃ n : Nat, e = literal n := by
  intro h
  cases e with
  | literal n => simp [h, isLiteral]
  | add e1 e2 => simp [size] at h -- contradiction
  | mul e1 e2 => simp [size] at h -- contradiction

lemma size_nonzero_if_add (e1 e2 : ArithExpr) : (add e1 e2).size > 0 := by
  simp only [size, gt_iff_lt]
  rw [Nat.add_assoc, Nat.add_comm]
  simp only [Nat.zero_lt_succ]

lemma size_nonzero_if_mul (e1 e2 : ArithExpr) : (mul e1 e2).size > 0 := by
  simp only [size, gt_iff_lt]
  rw [Nat.add_assoc, Nat.add_comm]
  simp only [Nat.zero_lt_succ]

lemma size_nonzero_if_not_literal (e : ArithExpr) : e.isLiteral = false → e.size > 0 := by
  intro h
  cases e with
  | literal n => simp [isLiteral] at h -- contradiction
  | add e1 e2 => exact size_nonzero_if_add e1 e2
  | mul e1 e2 => exact size_nonzero_if_mul e1 e2

lemma evalOneStep_lit_add_nonlit (lLit : Nat) (rNonlit : ArithExpr) (ev : rNonlit.isLiteral = false) :
    evalOneStep ((literal lLit).add rNonlit) = (literal lLit).add (evalOneStep rNonlit) := by
  cases h : rNonlit with
  | literal n => rw [h] at ev; contradiction
  | add e1 e2 => simp [evalOneStep]
  | mul e1 e2 => simp [evalOneStep]

lemma evalOneStep_lit_mul_nonlit (lLit : Nat) (rNonlit : ArithExpr) (ev : rNonlit.isLiteral = false) :
    evalOneStep ((literal lLit).mul rNonlit) = (literal lLit).mul (evalOneStep rNonlit) := by
  cases h : rNonlit with
  | literal n => rw [h] at ev; contradiction
  | add e1 e2 => simp [evalOneStep]
  | mul e1 e2 => simp [evalOneStep]

lemma evalOneStep_nonlit_add (lNonlit : ArithExpr) (r : ArithExpr) (ev : lNonlit.isLiteral = false) :
    evalOneStep (lNonlit.add r) = (evalOneStep lNonlit).add r := by
  cases h : lNonlit with
  | literal n => rw [h] at ev; contradiction
  | add e1 e2 => simp [evalOneStep]
  | mul e1 e2 => simp [evalOneStep]

lemma evalOneStep_nonlit_mul (lNonlit : ArithExpr) (r : ArithExpr) (ev : lNonlit.isLiteral = false) :
    evalOneStep (lNonlit.mul r) = (evalOneStep lNonlit).mul r := by
  cases h : lNonlit with
  | literal n => rw [h] at ev; contradiction
  | add e1 e2 => simp [evalOneStep]
  | mul e1 e2 => simp [evalOneStep]

theorem evalOneStep_progress (e : ArithExpr) : (evalOneStep e).size = e.size - 1 := by
  induction e with
  | literal n => -- e is already a literal, so no reduction happens
    exact by simp [evalOneStep, size]

  | add e1 e2 ih1 ih2 =>
    by_cases h : e1.isLiteral = true
    · -- e1 is a literal
      rcases isLiteral_extract e1 h with ⟨n1, rfl⟩
      cases h : e2 with
      | literal n2 => -- both e1 and e2 are literals. Reduction actually happens in this branch
        simp [evalOneStep, size]
      | add e21 e22 => -- e1 is a literal but e2 is not, so use induction hypothesis
        rw [←h, evalOneStep_lit_add_nonlit _ _ (by simp [h, isLiteral])]
        simp only [size, add_zero, ih2, add_tsub_cancel_left]
        have e2size_nonzero : 0 < e2.size := by rw [h]; exact size_nonzero_if_add e21 e22
        exact Nat.add_sub_of_le (Nat.succ_le_of_lt e2size_nonzero)
      | mul e21 e22 => -- exactly the same as add case
        rw [←h, evalOneStep_lit_add_nonlit _ _ (by simp [h, isLiteral])]
        simp only [size, add_zero, ih2, add_tsub_cancel_left]
        have e2size_nonzero : 0 < e2.size := by rw [h]; exact size_nonzero_if_add e21 e22
        exact Nat.add_sub_of_le (Nat.succ_le_of_lt e2size_nonzero)
    · -- e1 is not a literal, so use induction hypothesis
      rw [evalOneStep_nonlit_add _ _ (by simp [h])]
      simp only [size, ih1]
      have e1size_nonzero : 1 ≤ e1.size := by exact size_nonzero_if_not_literal _ (by simp [h])
      rw [Nat.add_sub_of_le e1size_nonzero, Nat.add_assoc, Nat.add_sub_self_left]

  | mul e1 e2 ih1 ih2 => -- Similar to the add case
    by_cases h : e1.isLiteral = true
    · rcases isLiteral_extract e1 h with ⟨n1, rfl⟩
      cases h : e2 with
      | literal n2 =>
        simp [evalOneStep, size]
      | add e21 e22 =>
        rw [←h, evalOneStep_lit_mul_nonlit _ _ (by simp [h, isLiteral])]
        simp only [size, add_zero, ih2, add_tsub_cancel_left]
        have e2size_nonzero : 0 < e2.size := by rw [h]; exact size_nonzero_if_add e21 e22
        exact Nat.add_sub_of_le (Nat.succ_le_of_lt e2size_nonzero)
      | mul e21 e22 =>
        rw [←h, evalOneStep_lit_mul_nonlit _ _ (by simp [h, isLiteral])]
        simp only [size, add_zero, ih2, add_tsub_cancel_left]
        have e2size_nonzero : 0 < e2.size := by rw [h]; exact size_nonzero_if_add e21 e22
        exact Nat.add_sub_of_le (Nat.succ_le_of_lt e2size_nonzero)
    · rw [evalOneStep_nonlit_mul _ _ (by simp [h])]
      simp only [size, ih1]
      have e1size_nonzero : 1 ≤ e1.size := by exact size_nonzero_if_not_literal _ (by simp [h])
      rw [Nat.add_sub_of_le e1size_nonzero, Nat.add_assoc, Nat.add_sub_self_left]

lemma evalOneStep_iterated_progress (e : ArithExpr) (n : Nat) :
    (evalOneStep^[n] e).size = e.size - n := by
  induction n generalizing e with
  | zero => simp
  | succ n ih =>
    simp [ih e.evalOneStep, evalOneStep_progress e, Nat.add_comm, Nat.sub_sub]

def evalViaSteps (expr: ArithExpr): Nat :=
  let result := evalOneStep^[expr.size] expr
  match result with
  | (literal n) => n
  | _           => 0 -- this is impossible

lemma evalViaSteps_result (expr: ArithExpr) : evalOneStep^[expr.size] expr = literal (evalViaSteps expr) := by
  simp [evalViaSteps]
  have h : (evalOneStep^[expr.size] expr).size = 0 := by
    rw [evalOneStep_iterated_progress expr expr.size, tsub_self]
  rcases size_zero_then_literal (evalOneStep^[expr.size] expr) h with ⟨_, eq⟩
  rw [eq]

end ArithExpr

inductive ArithEvalFrame : Type
| thenEvalRightAdd : ArithExpr → ArithEvalFrame -- [HOLE + e]
| thenAddLitLeft : Nat → ArithEvalFrame -- [n + HOLE]
| thenEvalRightMul : ArithExpr → ArithEvalFrame -- [HOLE * e]
| thenMulLitLeft : Nat → ArithEvalFrame -- [n * HOLE]
open ArithEvalFrame

instance : Repr ArithEvalFrame where
  reprPrec
  | (thenEvalRightAdd e), _ => s!"# + ({repr e})"
  | (thenAddLitLeft n), _ => s!"{n} + #"
  | (thenEvalRightMul e), _ => s!"# * ({repr e})"
  | (thenMulLitLeft n), _ => s!"{n} * #"

structure ArithmeticCKMachine : Type where
  controlString: ArithExpr
  frames : List ArithEvalFrame
deriving Repr

namespace ArithmeticCKMachine
open ArithExpr
open ArithEvalFrame

def init (e : ArithExpr) : ArithmeticCKMachine := ⟨e, []⟩

def step : ArithmeticCKMachine → ArithmeticCKMachine
| ⟨add e1 e2, frames⟩ => ⟨e1, thenEvalRightAdd e2 :: frames⟩
| ⟨mul e1 e2, frames⟩ => ⟨e1, thenEvalRightMul e2 :: frames⟩
| ⟨literal n, frames⟩ =>
    match frames with
    | (thenEvalRightAdd e1) :: frames' => ⟨e1, thenAddLitLeft n :: frames'⟩
    | (thenAddLitLeft n1) :: frames'   => ⟨literal (n + n1), frames'⟩
    | (thenEvalRightMul e1) :: frames' => ⟨e1, thenMulLitLeft n :: frames'⟩
    | (thenMulLitLeft n1) :: frames'   => ⟨literal (n * n1), frames'⟩
    | [] => ⟨literal n, []⟩

/--
This function calculates the cost of evaluating an expression using the CK machine.

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
    | thenEvalRightAdd e => e.size * 3 + 2
    | thenAddLitLeft _   => 1
    | thenEvalRightMul e => e.size * 3 + 2
    | thenMulLitLeft _   => 1
  )
  control.size * 3 + frameCosts.sum

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
  | add e1 e2 => simp [hc, evalCost, size] at h -- contradiction
  | mul e1 e2 => simp [hc, evalCost, size] at h -- contradiction

lemma evalCost_progress (machine : ArithmeticCKMachine) :
    machine.step.evalCost = machine.evalCost - 1 := by
  dsimp only [step]
  rcases machine with ⟨control, frames⟩
  cases hc : control with
  | literal n =>
    simp only
    cases hf : frames with
    | nil => simp [evalCost, size]
    | cons head tail =>
      cases head with
      | thenEvalRightAdd _ => simp [evalCost, size, ←Nat.add_assoc]
      | thenAddLitLeft _   => simp [evalCost, size]
      | thenEvalRightMul _ => simp [evalCost, size, ←Nat.add_assoc]
      | thenMulLitLeft _   => simp [evalCost, size]
  | add e1 e2 =>
    simp only [evalCost, List.map_cons, List.sum_cons, size]
    simp +arith
  | mul e1 e2 =>
    simp only [evalCost, List.map_cons, List.sum_cons, size]
    simp +arith

lemma evalCost_iterated_progress (machine : ArithmeticCKMachine) (n : Nat) :
    (step^[n] machine).evalCost = machine.evalCost - n := by
  induction n generalizing machine with
  | zero => simp [evalCost]
  | succ n ih =>
    simp [ih machine.step, evalCost_progress machine, Nat.add_comm, Nat.sub_sub]

def evalViaCKMachine (initExpr : ArithExpr) : Nat :=
  let result := step^[initExpr.size * 3] (init initExpr)
  match result.controlString with
  | literal n => n
  | _ => 0 -- this is impossible

lemma evalViaCKMachine_result (initExpr : ArithExpr) :
    step^[initExpr.size * 3] (init initExpr) = ⟨literal (evalViaCKMachine initExpr), []⟩ := by
  simp [evalViaCKMachine]
  let result := step^[initExpr.size * 3] (init initExpr)
  have resultCost_eq_zero : result.evalCost = 0 := by
    unfold result
    simp only [evalCost_iterated_progress (init initExpr) (initExpr.size * 3)]
    apply Nat.sub_self
  rcases evalCost_zero_then_halt_state result resultCost_eq_zero with ⟨n, eq⟩
  unfold result at eq; rw [eq]

end ArithmeticCKMachine

namespace ArithmeticCKMachine
open ArithExpr
open ArithEvalFrame

-- Reconstruct the "current whole expression" from the control string and the frames.
def stitchUp : (term : ArithExpr) → (contStack : List ArithEvalFrame) → ArithExpr
| e, [] => e
| e, (thenEvalRightAdd e1) :: frames => stitchUp (add e e1) frames
| e, (thenAddLitLeft n) :: frames    => stitchUp (add (literal n) e) frames
| e, (thenEvalRightMul e1) :: frames => stitchUp (mul e e1) frames
| e, (thenMulLitLeft n) :: frames    => stitchUp (mul (literal n) e) frames

def reductionCountUptoIndex (initExpr : ArithExpr) (idx : Nat) : Nat :=
  (List.range idx)
    |> List.filter (fun i =>
      let ⟨control, frames⟩ := step^[i] (init initExpr)
      match control with
      | literal _ =>
        match frames with
        | (thenAddLitLeft _) :: _ => true
        | (thenMulLitLeft _) :: _ => true
        | _ => false
      | _ => false
    )
    |> List.length

private lemma iterate_succ_apply_outer {α : Type} {f : α → α} (n : ℕ) (x : α) : f^[n.succ] x = f (f^[n] x) := by
  rw [Nat.succ_eq_add_one, Nat.add_comm, Function.iterate_add_apply (α := α) f 1 n]
  simp

theorem stitchUp_traces_evalOneStep
    (initExpr : ArithExpr) (idx : Nat) :
    let ⟨t, s⟩ := step^[idx] (init initExpr)
    stitchUp t s =
      evalOneStep^[reductionCountUptoIndex initExpr idx] initExpr := by
  sorry

lemma totalReductionCount (initExpr : ArithExpr) :
    reductionCountUptoIndex initExpr (initExpr.size * 3) = initExpr.size := by
  sorry

theorem evalViaCKMachine_evalViaSteps (initExpr : ArithExpr) :
    evalViaCKMachine initExpr = evalViaSteps initExpr := by
  apply ArithExpr.literal.inj
  rw [
    ←evalViaSteps_result,
    ←totalReductionCount initExpr,
    ←stitchUp_traces_evalOneStep initExpr (initExpr.size * 3),
    evalViaCKMachine_result initExpr
  ]
  dsimp only [stitchUp]

end ArithmeticCKMachine
