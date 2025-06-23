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

@[simp] def IsLiteral : ArithExpr → Prop
| (literal _) => True
| _           => False

@[simp] def evalOneStep : ArithExpr → ArithExpr
| (literal n) => literal n
| (add (literal n1) (literal n2)) => literal (n1 + n2)
| (add (literal n1) e2)           => add (literal n1) (evalOneStep e2)
| (add e1 e2)                     => add (evalOneStep e1) e2
| (mul (literal n1) (literal n2)) => literal (n1 * n2)
| (mul (literal n1) e2)           => mul (literal n1) (evalOneStep e2)
| (mul e1 e2)                     => mul (evalOneStep e1) e2

@[simp] def opsCount : ArithExpr → Nat
| (literal _) => 0
| (add e1 e2) => 1 + e1.opsCount + e2.opsCount
| (mul e1 e2) => 1 + e1.opsCount + e2.opsCount

lemma opsCount_zero_then_literal (e : ArithExpr)
                                 (h : e.opsCount = 0)
    : ∃ n : Nat, e = literal n :=
  by cases e <;> simp_all

@[simp] lemma evalOneStep_lit_add_nonlit (lLit : Nat) (rNonlit : ArithExpr)
                                         (ev : ¬rNonlit.IsLiteral)
    : ((literal lLit).add rNonlit).evalOneStep = (literal lLit).add (rNonlit.evalOneStep) :=
  by cases rNonlit <;> simp_all

@[simp] lemma evalOneStep_lit_mul_nonlit (lLit : Nat) (rNonlit : ArithExpr)
                                         (ev : ¬rNonlit.IsLiteral)
    : ((literal lLit).mul rNonlit).evalOneStep = (literal lLit).mul (rNonlit.evalOneStep) :=
  by cases rNonlit <;> simp_all

@[simp] lemma evalOneStep_nonlit_add (lNonlit : ArithExpr) (r : ArithExpr)
                                     (ev : ¬lNonlit.IsLiteral)
    : (lNonlit.add r).evalOneStep = lNonlit.evalOneStep.add r :=
  by cases lNonlit <;> simp_all

@[simp] lemma evalOneStep_nonlit_mul (lNonlit : ArithExpr) (r : ArithExpr)
                                     (ev : ¬lNonlit.IsLiteral)
    : (lNonlit.mul r).evalOneStep = lNonlit.evalOneStep.mul r :=
  by cases lNonlit <;> simp_all

@[simp] theorem evalOneStep_progress (e : ArithExpr) : (evalOneStep e).opsCount = e.opsCount - 1 := by
  induction e with
  | literal n         => simp
  | add e1 e2 ih1 ih2 => cases e1 <;> cases e2 <;> simp_all +arith
  | mul e1 e2 ih1 ih2 => cases e1 <;> cases e2 <;> simp_all +arith

@[simp] lemma evalOneStep_iterated_progress (e : ArithExpr) (n : Nat) :
    (evalOneStep^[n] e).opsCount = e.opsCount - n := by
  induction n generalizing e with
  | zero      => simp
  | succ n ih => simp +arith [*, Nat.sub_sub]

@[simp] def evalViaSteps (expr: ArithExpr): Nat :=
  match evalOneStep^[expr.opsCount] expr with
  | (literal n) => n
  | _           => 0 -- this is impossible; evalViaSteps_result will prove this

lemma evalViaSteps_result (expr: ArithExpr) : evalOneStep^[expr.opsCount] expr = literal (evalViaSteps expr) := by
  rcases opsCount_zero_then_literal (evalOneStep^[expr.opsCount] expr) (by simp) with ⟨_, eq⟩
  simp [*]

end ArithExpr

inductive ArithEvalFrame : Type
| thenEvalRightAdd : ArithExpr → ArithEvalFrame -- [HOLE + e]
| thenAddLitLeft   :    Nat    → ArithEvalFrame -- [n + HOLE]
| thenEvalRightMul : ArithExpr → ArithEvalFrame -- [HOLE * e]
| thenMulLitLeft   :    Nat    → ArithEvalFrame -- [n * HOLE]
open ArithEvalFrame

namespace ArithEvalFrame

instance : Repr ArithEvalFrame where
  reprPrec
  | (thenEvalRightAdd e), _ => s!"# + ({repr e})"
  | (thenAddLitLeft n),   _ => s!"{n} + #"
  | (thenEvalRightMul e), _ => s!"# * ({repr e})"
  | (thenMulLitLeft n),   _ => s!"{n} * #"

@[simp] def frameOpCount : ArithEvalFrame → Nat
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

@[simp] def machineStateOpCount (machine : ArithmeticCKMachine): Nat :=
  machine.controlString.opsCount + (machine.frames.map frameOpCount).sum

@[simp] def step : ArithmeticCKMachine → ArithmeticCKMachine
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
@[simp] def evalCost (machine : ArithmeticCKMachine): Nat :=
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
    | cons head tail => cases head <;> simp [hf] at h -- contradiction
  | add e1 e2 => simp [hc] at h -- contradiction
  | mul e1 e2 => simp [hc] at h -- contradiction

lemma evalCost_progress (machine : ArithmeticCKMachine) :
    machine.step.evalCost = machine.evalCost - 1 := by
  dsimp only [step]
  rcases machine with ⟨control, frames⟩
  cases hc : control with
  | literal n =>
    dsimp only
    cases hf : frames with
    | nil => simp
    | cons head tail => cases head <;> simp +arith
  | add e1 e2 => simp +arith
  | mul e1 e2 => simp +arith

lemma evalCost_iterated_progress (machine : ArithmeticCKMachine) (n : Nat) :
    (step^[n] machine).evalCost = machine.evalCost - n := by
  induction n generalizing machine with
  | zero => simp
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
    rw [evalCost_iterated_progress _ _]
    simp [evalCost]
  rcases evalCost_zero_then_halt_state result resultCost_eq_zero with ⟨n, eq⟩
  unfold result at eq; rw [eq]

end ArithmeticCKMachine

namespace ArithmeticCKMachine
open ArithExpr
open ArithEvalFrame

-- Reconstruct the "current whole expression" from the CK machine state
@[simp] abbrev stitchUp : (term : ArithExpr) → (contStack : List ArithEvalFrame) → ArithExpr
| e, [] => e
| e, (thenEvalRightAdd e1) :: frames => stitchUp (add e e1) frames
| e, (thenAddLitLeft n) :: frames    => stitchUp (add (literal n) e) frames
| e, (thenEvalRightMul e1) :: frames => stitchUp (mul e e1) frames
| e, (thenMulLitLeft n) :: frames    => stitchUp (mul (literal n) e) frames

@[simp] def isReducingTransitionAt (expr : ArithExpr) i :=
  let ⟨control, frames⟩ := step^[i] (init expr)
  match control with
  | literal _ =>
    match frames with
    | (thenAddLitLeft _) :: _ => true
    | (thenMulLitLeft _) :: _ => true
    | _ => false
  | _ => false

@[simp] def reductionCountUptoIndex (initExpr : ArithExpr) (idx : Nat) : Nat :=
  (List.range idx).countP (isReducingTransitionAt initExpr)

@[simp] private lemma range_countP_succ {p : Nat → Bool} {n : Nat} :
    (List.range (n + 1)).countP p = if p n then (List.range n).countP p + 1 else (List.range n).countP p := by
  by_cases p n <;> simp_all [List.range_succ]

lemma stitchUp_nonlit_evalOneStep
    (e : ArithExpr) (fs : List ArithEvalFrame)
    (eNonlit : ¬e.IsLiteral) :
    (stitchUp e fs).evalOneStep = stitchUp e.evalOneStep fs := by
  induction fs generalizing e with
  | nil          => simp
  | cons f fs ih => cases f <;> simp_all [-evalOneStep]

lemma stitchUp_lit_thenAddLitLeft_evalOneStep (fs : List ArithEvalFrame) (n m : Nat) :
    stitchUp (literal (m + n)) fs = (stitchUp (literal n) (thenAddLitLeft m :: fs)).evalOneStep :=
  by simp [stitchUp_nonlit_evalOneStep]

lemma stitchUp_lit_thenMulLitLeft_evalOneStep (fs : List ArithEvalFrame) (n m : Nat) :
    stitchUp (literal (m * n)) fs = (stitchUp (literal n) (thenMulLitLeft m :: fs)).evalOneStep :=
  by simp [stitchUp_nonlit_evalOneStep]

theorem stitchUp_traces_evalOneStep (initExpr : ArithExpr) (idx : Nat) :
    let ⟨t, s⟩ := step^[idx] (init initExpr)
    stitchUp t s = evalOneStep^[reductionCountUptoIndex initExpr idx] initExpr := by
  induction idx with
  | zero => simp
  | succ idx ih =>
    rcases machineAtIdx : (step^[idx] (init initExpr)) with ⟨t, s⟩
    simp only [machineAtIdx, reductionCountUptoIndex] at ih
    cases t with
    | literal n =>
      cases s with
      | nil =>
        -- machine halted: no reduction happens
        simp [-Function.iterate_succ, Function.iterate_succ_apply', machineAtIdx, ←ih]
      | cons f fs =>
        -- reduction may or may not happen but overall the reconstructed expression remains the same
        cases f <;> simp [
          *,
          -Function.iterate_succ, Function.iterate_succ_apply',
          stitchUp_lit_thenAddLitLeft_evalOneStep, stitchUp_lit_thenMulLitLeft_evalOneStep
        ]
    | add e₁ e₂ => simp [*, -Function.iterate_succ, Function.iterate_succ_apply']
    | mul e₁ e₂ => simp [*, -Function.iterate_succ, Function.iterate_succ_apply']

lemma machineStateOpCount_plus_reductionCountUptoIndex_preserved (expr : ArithExpr) (n : Nat) :
    (step^[n.succ] (init expr)).machineStateOpCount + (reductionCountUptoIndex expr n.succ) =
    (step^[n] (init expr)).machineStateOpCount + (reductionCountUptoIndex expr n) := by
  rw [Function.iterate_succ_apply']
  rcases h : step^[n] (init expr) with ⟨control, frames⟩
  cases hc : control with
  | literal _ =>
    cases hf : frames with
    | nil => simp [*]
    | cons head tail =>
      cases head <;> simp +arith [*]
  | add e1 e2 =>
    simp +arith [*]
  | mul e1 e2 =>
    simp +arith [*]

lemma machineStateOpCount_plus_reductionCountUptoIndex_constant (expr : ArithExpr) (n : Nat) :
    (step^[n] (init expr)).machineStateOpCount + (reductionCountUptoIndex expr n) = expr.opsCount := by
  induction n with
  | zero      => simp
  | succ n ih => rw [machineStateOpCount_plus_reductionCountUptoIndex_preserved expr n, ih]

lemma totalReductionCount (expr : ArithExpr) :
    reductionCountUptoIndex expr (expr.opsCount * 3) = expr.opsCount := by
  nth_rw 2 [←machineStateOpCount_plus_reductionCountUptoIndex_constant expr (expr.opsCount * 3)]
  simp [evalViaCKMachine_result]

theorem evalViaCKMachine_evalViaSteps (expr : ArithExpr) : evalViaCKMachine expr = evalViaSteps expr := by
  apply ArithExpr.literal.inj
  rw [
    ←evalViaSteps_result,
    ←totalReductionCount expr,
    ←stitchUp_traces_evalOneStep expr (expr.opsCount * 3),
    evalViaCKMachine_result expr
  ]

end ArithmeticCKMachine
