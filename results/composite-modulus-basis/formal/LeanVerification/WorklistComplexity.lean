import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-!
# Work-list complexity of timestamped p-adic insertion

This is the ghost-token argument behind the implementation. Each of the at
most `k` initial power rows owns one non-branching token. A queue pop either
terminates the token or requeues exactly one successor. `remaining` is the
number of columns not yet crossed by that token; requeueing consumes a positive
number of columns. Queue ordering is deliberately abstracted by `List.Perm`.
-/

namespace CompositeModulusBasis.WorklistComplexity

/-- A complete work-list execution, instrumented by column visits and queue pops. -/
inductive Run : List Nat → Nat → Nat → Prop where
  | done : Run [] 0 0
  | stop {remaining : Nat} {rest : List Nat} {visited tailVisits tailPops : Nat}
      (visited_le : visited ≤ remaining)
      (tail : Run rest tailVisits tailPops) :
      Run (remaining :: rest) (visited + tailVisits) (tailPops + 1)
  | requeue {remaining : Nat} {rest next : List Nat}
      {visited tailVisits tailPops : Nat}
      (visited_pos : 0 < visited)
      (visited_le : visited ≤ remaining)
      (queue_order_only : next.Perm ((remaining - visited) :: rest))
      (tail : Run next tailVisits tailPops) :
      Run (remaining :: rest) (visited + tailVisits) (tailPops + 1)

/-- Every queue occurring recursively inside a run respects one common size
bound.  This makes the `≤ k` pending-task claim explicit, rather than deriving
only the final operation count. -/
inductive QueueLengthsLe (bound : Nat) :
    {queue : List Nat} → {visits pops : Nat} → Run queue visits pops → Prop where
  | done : QueueLengthsLe bound Run.done
  | stop {remaining rest visited tailVisits tailPops}
      {visited_le : visited ≤ remaining}
      {tail : Run rest tailVisits tailPops}
      (current_le : (remaining :: rest).length ≤ bound)
      (tail_le : QueueLengthsLe bound tail) :
      QueueLengthsLe bound (Run.stop visited_le tail)
  | requeue {remaining rest next visited tailVisits tailPops}
      {visited_pos : 0 < visited} {visited_le : visited ≤ remaining}
      {queue_order_only : next.Perm ((remaining - visited) :: rest)}
      {tail : Run next tailVisits tailPops}
      (current_le : (remaining :: rest).length ≤ bound)
      (tail_le : QueueLengthsLe bound tail) :
      QueueLengthsLe bound
        (Run.requeue visited_pos visited_le queue_order_only tail)

theorem Run.queueLengthsLe {queue : List Nat} {visits pops bound : Nat}
    (run : Run queue visits pops) (hbound : queue.length ≤ bound) :
    QueueLengthsLe bound run := by
  induction run with
  | done => exact .done
  | @stop remaining rest visited tailVisits tailPops visited_le tail ih =>
      apply QueueLengthsLe.stop (visited_le := visited_le) (tail := tail) hbound
      exact ih (by
        simp only [List.length_cons] at hbound ⊢
        omega)
  | @requeue remaining rest next visited tailVisits tailPops
      visited_pos visited_le queue_order_only tail ih =>
      apply QueueLengthsLe.requeue (visited_pos := visited_pos)
        (visited_le := visited_le) (queue_order_only := queue_order_only)
        (tail := tail) hbound
      exact ih (by
        have hlength : next.length = (remaining :: rest).length := by
          simpa using queue_order_only.length_eq
        rw [hlength]
        exact hbound)

/-- Reordering the priority queue changes neither the number nor budgets of tokens. -/
theorem perm_length_and_sum {xs ys : List Nat} (h : xs.Perm ys) :
    xs.length = ys.length ∧ xs.sum = ys.sum := ⟨h.length_eq, h.sum_eq⟩

/-- Across a complete execution, column visits cannot exceed initial column budget. -/
theorem visits_le_sum {queue : List Nat} {visits pops : Nat}
    (run : Run queue visits pops) : visits ≤ queue.sum := by
  induction run with
  | done => simp
  | stop visited_le tail ih =>
      simp only [List.sum_cons]
      omega
  | @requeue remaining rest next visited tailVisits tailPops
      visited_pos visited_le queue_order_only tail ih =>
      have hsum : next.sum = (remaining - visited) + rest.sum := by
        simpa using queue_order_only.sum_eq
      simp only [List.sum_cons]
      omega

/-- `length + remaining-column budget` drops by at least one on every pop. -/
theorem pops_le_potential {queue : List Nat} {visits pops : Nat}
    (run : Run queue visits pops) : pops ≤ queue.length + queue.sum := by
  induction run with
  | done => simp
  | @stop remaining rest visited tailVisits tailPops visited_le tail ih =>
      simp only [List.length_cons, List.sum_cons]
      omega
  | @requeue remaining rest next visited tailVisits tailPops
      visited_pos visited_le queue_order_only tail ih =>
      have hlen : next.length = rest.length + 1 := by
        simpa using queue_order_only.length_eq
      have hsum : next.sum = (remaining - visited) + rest.sum := by
        simpa using queue_order_only.sum_eq
      simp only [List.length_cons, List.sum_cons]
      omega

def initialBudgets (k d : Nat) : List Nat := List.replicate k d

@[simp] theorem initialBudgets_length (k d : Nat) : (initialBudgets k d).length = k := by
  simp [initialBudgets]

@[simp] theorem initialBudgets_sum (k d : Nat) : (initialBudgets k d).sum = k * d := by
  simp [initialBudgets]

/-- The state-machine theorem yielding the `kd` column-visit bound. -/
theorem insertion_visits_le {k d visits pops : Nat}
    (run : Run (initialBudgets k d) visits pops) : visits ≤ k * d := by
  simpa using visits_le_sum run

/-- The state-machine theorem yielding the `k(d+1)` heap-pop bound. -/
theorem insertion_pops_le {k d visits pops : Nat}
    (run : Run (initialBudgets k d) visits pops) : pops ≤ k * (d + 1) := by
  have h := pops_le_potential run
  simpa [Nat.mul_add, Nat.add_comm] using h

/-- Every intermediate priority queue contains at most the original `k`
non-branching tokens. -/
theorem insertion_queue_lengths_le {k d visits pops : Nat}
    (run : Run (initialBudgets k d) visits pops) : QueueLengthsLe k run :=
  run.queueLengthsLe (by simp)

/-- If one row operation touches at most `d` cells per visit, insertion uses at most `kd²`. -/
theorem insertion_cells_le {k d visits pops : Nat}
    (run : Run (initialBudgets k d) visits pops) : visits * d ≤ k * d * d := by
  exact Nat.mul_le_mul_right d (insertion_visits_le run)

/-- Heap bookkeeping bound under an explicit implementation contract: one pop
and at most one push per recursive step, each costing at most
`perOperationCost` comparisons. -/
theorem insertion_heap_comparisons_le {k d visits pops comparisons : Nat}
    (run : Run (initialBudgets k d) visits pops) (perOperationCost : Nat)
    (himplementation : comparisons ≤ 2 * pops * perOperationCost) :
    comparisons ≤ 2 * (k * (d + 1)) * perOperationCost := by
  exact himplementation.trans
    (Nat.mul_le_mul_right perOperationCost
      (Nat.mul_le_mul_left 2 (insertion_pops_le run)))

end CompositeModulusBasis.WorklistComplexity
