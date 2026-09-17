import LeanVerification.SettledTimestamp
import LeanVerification.WorklistComplexity
import Mathlib.Tactic

/-!
# Refinement from certified heap pops to the ghost-token cost model

Each task owns the number of columns it can still cross.  A certified scan
either terminates that token or returns exactly one displaced successor whose
budget is the unused suffix.  Queue reordering is represented by permutation,
matching a priority heap without depending on its array implementation.
-/

namespace CompositeModulusBasis.WorklistRefinement

open PadicEchelon SettledTimestamp TimestampedBasis

structure WorkItem (p k d : Nat) where
  entry : TaggedVector p k d
  startColumn : Nat
  remaining : Nat
  remaining_eq : remaining = d - startColumn
  zerosBefore : ∀ column : Fin d, (column : Nat) < startColumn → entry.row column = 0

def tableRows {p k d : Nat} (table : List (TaggedPivot p k d)) :
    List (TaggedVector p k d) := table.map TaggedPivot.asVector

def queueRows {p k d : Nat} (queue : List (WorkItem p k d)) :
    List (TaggedVector p k d) := queue.map WorkItem.entry

def activeRows {p k d : Nat} (table : List (TaggedPivot p k d))
    (queue : List (WorkItem p k d)) : List (TaggedVector p k d) :=
  tableRows table ++ queueRows queue

def queueBudgets {p k d : Nat} (queue : List (WorkItem p k d)) : List Nat :=
  queue.map WorkItem.remaining

/-- The semantic and budget certificate produced by one complete `scanTask`
call after popping its head task. -/
structure PopCertificate {p k d : Nat} (task : WorkItem p k d)
    (before after : List (TaggedPivot p k d))
    (replacement : Option (WorkItem p k d)) (visits : Nat) : Prop where
  visits_le : visits ≤ task.remaining
  semantics : ThresholdEquivalent
    (tableRows before ++ [task.entry])
    (tableRows after ++ replacement.toList.map WorkItem.entry)
  replacement_budget : ∀ next, replacement = some next →
    0 < visits ∧ next.remaining = task.remaining - visits

theorem tableRows_perm {p k d : Nat}
    {a b : List (TaggedPivot p k d)} (h : a.Perm b) :
    (tableRows a).Perm (tableRows b) := h.map TaggedPivot.asVector

theorem pop_zero {p k d : Nat} (task : WorkItem p k d)
    (table : List (TaggedPivot p k d)) (visits : Nat)
    (hvisits : visits ≤ task.remaining) (hzero : task.entry.row = 0) :
    PopCertificate task table table none visits := by
  refine ⟨hvisits, ?_, ?_⟩
  · simpa using (zero_entry_equivalent task.entry hzero).append_left (tableRows table)
  · intro next hnone
    simp at hnone

theorem pop_store {p k d : Nat} (task : WorkItem p k d)
    (before after : List (TaggedPivot p k d)) (stored : TaggedPivot p k d)
    (unit : (Ring p k)ˣ) (visits : Nat)
    (hvisits : visits ≤ task.remaining)
    (hstored : stored.asVector =
      task.entry.withRow ((unit : Ring p k) • task.entry.row))
    (hafter : after.Perm (stored :: before)) :
    PopCertificate task before after none visits := by
  refine ⟨hvisits, ?_, ?_⟩
  · have hfront : ThresholdEquivalent
        (tableRows before ++ [task.entry]) (task.entry :: tableRows before) :=
      ThresholdEquivalent.of_perm (List.perm_append_comm)
    have hscale := unit_scale_equivalent task.entry unit (tableRows before)
    have hrows : (tableRows after).Perm (stored.asVector :: tableRows before) :=
      tableRows_perm hafter
    have hout : ThresholdEquivalent
        (task.entry.withRow ((unit : Ring p k) • task.entry.row) :: tableRows before)
        (tableRows after) := by
      rw [← hstored]
      exact ThresholdEquivalent.of_perm hrows.symm
    simpa using hfront.trans (hscale.trans hout)
  · intro next hnone
    simp at hnone

theorem pop_replace {p k d : Nat}
    (task replacement : WorkItem p k d)
    (before after : List (TaggedPivot p k d))
    (old stored : TaggedPivot p k d) (others : List (TaggedPivot p k d))
    (unit : (Ring p k)ˣ) (factor : Ring p k) (visits : Nat)
    (hvisitsPos : 0 < visits) (hvisits : visits ≤ task.remaining)
    (htime : old.timestamp ≤ task.entry.timestamp)
    (hbefore : before.Perm (old :: others))
    (hafter : after.Perm (stored :: others))
    (hstored : stored.asVector =
      task.entry.withRow ((unit : Ring p k) • task.entry.row))
    (hreplacement : replacement.entry =
      old.asVector.withRow
        (old.pivot.row - factor • ((unit : Ring p k) • task.entry.row)))
    (hbudget : replacement.remaining = task.remaining - visits) :
    PopCertificate task before after (some replacement) visits := by
  let oldVector := old.asVector
  let otherVectors := tableRows others
  have hbeforeRows : (tableRows before).Perm (oldVector :: otherVectors) :=
    tableRows_perm hbefore
  have hafterRows : (tableRows after).Perm (stored.asVector :: otherVectors) :=
    tableRows_perm hafter
  have hin : ThresholdEquivalent
      (tableRows before ++ [task.entry])
      (task.entry :: oldVector :: otherVectors) := by
    apply ThresholdEquivalent.of_perm
    exact (hbeforeRows.append_right [task.entry]).trans List.perm_append_comm
  have hlocal := replace_older_equivalent task.entry oldVector otherVectors unit factor htime
  have houtPerm :
      (task.entry.withRow ((unit : Ring p k) • task.entry.row) ::
        oldVector.withRow
          (old.pivot.row - factor • ((unit : Ring p k) • task.entry.row)) ::
            otherVectors).Perm
      (tableRows after ++ [replacement.entry]) := by
    have hrotate :
        (oldVector.withRow
            (old.pivot.row - factor • ((unit : Ring p k) • task.entry.row)) :: otherVectors).Perm
        (otherVectors ++ [replacement.entry]) := by
      rw [hreplacement]
      simpa using (List.perm_append_comm
        (l₁ := [oldVector.withRow
          (old.pivot.row - factor • ((unit : Ring p k) • task.entry.row))])
        (l₂ := otherVectors))
    have hfirst := hrotate.cons
      (task.entry.withRow ((unit : Ring p k) • task.entry.row))
    have htail := hafterRows.append_right [replacement.entry]
    rw [hstored] at htail
    exact hfirst.trans htail.symm
  refine ⟨hvisits, hin.trans (hlocal.trans (ThresholdEquivalent.of_perm houtPerm)), ?_⟩
  intro next hnext
  simp only [Option.some.injEq] at hnext
  subst next
  exact ⟨hvisitsPos, hbudget⟩

theorem pop_replace_zero {p k d : Nat}
    (task : WorkItem p k d)
    (before after : List (TaggedPivot p k d))
    (old stored : TaggedPivot p k d) (others : List (TaggedPivot p k d))
    (unit : (Ring p k)ˣ) (factor : Ring p k) (visits : Nat)
    (hvisits : visits ≤ task.remaining)
    (htime : old.timestamp ≤ task.entry.timestamp)
    (hbefore : before.Perm (old :: others))
    (hafter : after.Perm (stored :: others))
    (hstored : stored.asVector =
      task.entry.withRow ((unit : Ring p k) • task.entry.row))
    (hzero : old.pivot.row - factor • ((unit : Ring p k) • task.entry.row) = 0) :
    PopCertificate task before after none visits := by
  let oldVector := old.asVector
  let otherVectors := tableRows others
  have hbeforeRows : (tableRows before).Perm (oldVector :: otherVectors) :=
    tableRows_perm hbefore
  have hafterRows : (tableRows after).Perm (stored.asVector :: otherVectors) :=
    tableRows_perm hafter
  have hin : ThresholdEquivalent
      (tableRows before ++ [task.entry])
      (task.entry :: oldVector :: otherVectors) := by
    apply ThresholdEquivalent.of_perm
    exact (hbeforeRows.append_right [task.entry]).trans List.perm_append_comm
  have hlocal := replace_older_zero_equivalent task.entry oldVector otherVectors
    unit factor htime hzero
  have hout : ThresholdEquivalent
      (task.entry.withRow ((unit : Ring p k) • task.entry.row) :: otherVectors)
      (tableRows after) := by
    rw [← hstored]
    exact ThresholdEquivalent.of_perm hafterRows.symm
  refine ⟨hvisits, ?_, ?_⟩
  · simpa using hin.trans (hlocal.trans hout)
  intro next hnone
  simp at hnone

/-- Prefixing one reduction by a newer stored pivot composes with the remaining
scan certificate and consumes one positive portion of the column budget. -/
theorem PopCertificate.prependReduction {p k d : Nat}
    (task residual : WorkItem p k d)
    (stored : TaggedPivot p k d) (others : List (TaggedPivot p k d))
    (before after : List (TaggedPivot p k d))
    (replacement : Option (WorkItem p k d))
    (factor : Ring p k) (tailVisits stepVisits : Nat)
    (hbefore : before.Perm (stored :: others))
    (htime : task.entry.timestamp ≤ stored.timestamp)
    (hresidual : residual.entry = task.entry.withRow
      (task.entry.row - factor • stored.pivot.row))
    (hremaining : residual.remaining = task.remaining - stepVisits)
    (hstepPos : 0 < stepVisits) (hstepLe : stepVisits ≤ task.remaining)
    (tail : PopCertificate residual before after replacement tailVisits) :
    PopCertificate task before after replacement (stepVisits + tailVisits) := by
  have hbeforeRows : (tableRows before).Perm
      (stored.asVector :: tableRows others) := tableRows_perm hbefore
  have hin : ThresholdEquivalent
      (tableRows before ++ [task.entry])
      (task.entry :: stored.asVector :: tableRows others) := by
    apply ThresholdEquivalent.of_perm
    exact (hbeforeRows.append_right [task.entry]).trans List.perm_append_comm
  have hlocal := reduce_by_newer_equivalent task.entry stored.asVector
    (tableRows others) factor htime
  have hlocal' : ThresholdEquivalent
      (task.entry :: stored.asVector :: tableRows others)
      (residual.entry :: stored.asVector :: tableRows others) := by
    rw [hresidual]
    simpa [TaggedPivot.asVector] using hlocal
  have hout : ThresholdEquivalent
      (residual.entry :: stored.asVector :: tableRows others)
      (tableRows before ++ [residual.entry]) := by
    apply ThresholdEquivalent.of_perm
    have hrotate := List.perm_append_comm
      (l₁ := [residual.entry]) (l₂ := stored.asVector :: tableRows others)
    exact hrotate.trans (hbeforeRows.append_right [residual.entry]).symm
  refine ⟨?_, (hin.trans (hlocal'.trans hout)).trans tail.semantics, ?_⟩
  · have := tail.visits_le
    omega
  · intro next hnext
    rcases tail.replacement_budget next hnext with ⟨htailPos, hnextBudget⟩
    constructor
    · omega
    · omega

/-- A complete priority work-list execution.  `next.Perm (replacement :: rest)`
allows any heap representation/order while forbidding branching. -/
inductive CertifiedDrain {p k d : Nat} :
    List (WorkItem p k d) → List (TaggedPivot p k d) →
      List (TaggedPivot p k d) → Nat → Nat → Prop where
  | done (table) : CertifiedDrain [] table table 0 0
  | stop {task rest before middle after visits tailVisits tailPops}
      (pop : PopCertificate task before middle none visits)
      (tail : CertifiedDrain rest middle after tailVisits tailPops) :
      CertifiedDrain (task :: rest) before after
        (visits + tailVisits) (tailPops + 1)
  | requeue {task rest before middle after replacement next
      visits tailVisits tailPops}
      (pop : PopCertificate task before middle (some replacement) visits)
      (queue_order_only : next.Perm (replacement :: rest))
      (tail : CertifiedDrain next middle after tailVisits tailPops) :
      CertifiedDrain (task :: rest) before after
        (visits + tailVisits) (tailPops + 1)

theorem queueBudgets_perm {p k d : Nat}
    {a b : List (WorkItem p k d)} (h : a.Perm b) :
    (queueBudgets a).Perm (queueBudgets b) := h.map WorkItem.remaining

/-- Erasing rows and retaining only remaining-column budgets yields exactly the
previously proved ghost-token `Run`. -/
theorem CertifiedDrain.toComplexityRun {p k d : Nat}
    {queue : List (WorkItem p k d)} {before after : List (TaggedPivot p k d)}
    {visits pops : Nat} (run : CertifiedDrain queue before after visits pops) :
    WorklistComplexity.Run (queueBudgets queue) visits pops := by
  induction run with
  | done table => exact .done
  | @stop task rest before middle after visits tailVisits tailPops pop tail ih =>
      change WorklistComplexity.Run
        (task.remaining :: queueBudgets rest) (visits + tailVisits) (tailPops + 1)
      exact .stop pop.visits_le ih
  | @requeue task rest before middle after replacement next
      visits tailVisits tailPops pop queue_order_only tail ih =>
      have hbudget := pop.replacement_budget replacement rfl
      change WorklistComplexity.Run
        (task.remaining :: queueBudgets rest) (visits + tailVisits) (tailPops + 1)
      apply WorklistComplexity.Run.requeue hbudget.1 pop.visits_le
        (next := queueBudgets next) (tail := ih)
      have hperm := queueBudgets_perm queue_order_only
      simpa [queueBudgets, hbudget.2] using hperm

theorem activeRows_requeue_perm {p k d : Nat}
    (table : List (TaggedPivot p k d))
    {next replacement rest : List (WorkItem p k d)}
    (h : next.Perm (replacement ++ rest)) :
    (activeRows table next).Perm
      (tableRows table ++ queueRows replacement ++ queueRows rest) := by
  unfold activeRows
  have hrows : (queueRows next).Perm (queueRows replacement ++ queueRows rest) := by
    simpa [queueRows] using h.map WorkItem.entry
  simpa [List.append_assoc] using List.Perm.append_left (tableRows table) hrows

/-- All heap pops together preserve the span visible at every timestamp
threshold. -/
theorem CertifiedDrain.thresholdEquivalent {p k d : Nat}
    {queue : List (WorkItem p k d)} {before after : List (TaggedPivot p k d)}
    {visits pops : Nat} (run : CertifiedDrain queue before after visits pops) :
    ThresholdEquivalent (activeRows before queue) (tableRows after) := by
  induction run with
  | done table =>
      simpa [activeRows, queueRows] using
        (ThresholdEquivalent.refl (tableRows table))
  | @stop task rest before middle after visits tailVisits tailPops pop tail ih =>
      have hpop := pop.semantics.append_right (queueRows rest)
      have hpop' : ThresholdEquivalent
          (activeRows before (task :: rest)) (activeRows middle rest) := by
        simpa [activeRows, queueRows, List.append_assoc] using hpop
      exact hpop'.trans ih
  | @requeue task rest before middle after replacement next
      visits tailVisits tailPops pop queue_order_only tail ih =>
      have hpop := pop.semantics.append_right (queueRows rest)
      have hpop' : ThresholdEquivalent
          (activeRows before (task :: rest))
          (activeRows middle (replacement :: rest)) := by
        simpa [activeRows, queueRows, List.append_assoc] using hpop
      have hqueue : ThresholdEquivalent
          (activeRows middle (replacement :: rest))
          (activeRows middle next) := by
        apply ThresholdEquivalent.of_perm
        unfold activeRows
        exact List.Perm.append_left (tableRows middle)
          (queue_order_only.symm.map WorkItem.entry)
      exact hpop'.trans (hqueue.trans ih)

def initialQueue {p k d : Nat} (entries : Fin k → TaggedVector p k d) :
    List (WorkItem p k d) :=
  List.ofFn fun index =>
    { entry := entries index
      startColumn := 0
      remaining := d
      remaining_eq := by simp
      zerosBefore := by intro column hcolumn; omega }

@[simp] theorem initialQueue_budgets {p k d : Nat}
    (entries : Fin k → TaggedVector p k d) :
    queueBudgets (initialQueue entries) = WorklistComplexity.initialBudgets k d := by
  simp [queueBudgets, initialQueue, WorklistComplexity.initialBudgets,
    List.map_ofFn, Function.comp_def]

/-- A certified concrete drain from the `k` initial power rows inherits the
`kd`, `k(d+1)`, and `kd²` bounds. -/
theorem certified_insertion_bounds {p k d : Nat}
    (entries : Fin k → TaggedVector p k d)
    {before after : List (TaggedPivot p k d)} {visits pops : Nat}
    (run : CertifiedDrain (initialQueue entries) before after visits pops) :
    visits ≤ k * d ∧ pops ≤ k * (d + 1) ∧ visits * d ≤ k * d * d := by
  have hrun := run.toComplexityRun
  rw [initialQueue_budgets] at hrun
  exact ⟨WorklistComplexity.insertion_visits_le hrun,
    WorklistComplexity.insertion_pops_le hrun,
    WorklistComplexity.insertion_cells_le hrun⟩

end CompositeModulusBasis.WorklistRefinement
