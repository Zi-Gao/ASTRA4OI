import LeanVerification.PrioritySafety
import Mathlib.Tactic

/-!
# Totality of the priority work list

This module constructs a legal scan for every maximal-timestamp task and then
uses the strictly decreasing queue potential to construct a complete drain.
-/

namespace CompositeModulusBasis.Totality

open BasisQuery FastAppend FastInvariant PadicEchelon PrioritySafety
  SettledTimestamp TerminalExtraction TimestampedBasis
  TimestampLayerInvariant VerifiedScan WorklistRefinement

def QueueDescending {p k d : Nat} (queue : List (WorkItem p k d)) : Prop :=
  queue.Pairwise fun earlier later => later.entry.timestamp ≤ earlier.entry.timestamp

theorem QueueDescending.tail {p k d : Nat}
    {head : WorkItem p k d} {tail : List (WorkItem p k d)}
    (h : QueueDescending (head :: tail)) : QueueDescending tail :=
  (List.pairwise_cons.1 h).2

theorem QueueDescending.head_maximal {p k d : Nat}
    {head : WorkItem p k d} {tail : List (WorkItem p k d)}
    (h : QueueDescending (head :: tail)) :
    NoNewerPending head.entry.timestamp (head :: tail) := by
  intro task htask
  rcases List.mem_cons.mp htask with rfl | htail
  · exact le_rfl
  · exact (List.pairwise_cons.1 h).1 task htail

def insertDescending {p k d : Nat} (item : WorkItem p k d) :
    List (WorkItem p k d) → List (WorkItem p k d)
  | [] => [item]
  | head :: tail =>
      if head.entry.timestamp ≤ item.entry.timestamp then item :: head :: tail
      else head :: insertDescending item tail

theorem insertDescending_perm {p k d : Nat} (item : WorkItem p k d)
    (queue : List (WorkItem p k d)) :
    (insertDescending item queue).Perm (item :: queue) := by
  induction queue with
  | nil => simp [insertDescending]
  | cons head tail ih =>
      simp only [insertDescending]
      split_ifs
      · exact List.Perm.refl _
      · exact (ih.cons head).trans (List.Perm.swap head item tail).symm

theorem insertDescending_ordered {p k d : Nat} (item : WorkItem p k d)
    {queue : List (WorkItem p k d)} (hqueue : QueueDescending queue) :
    QueueDescending (insertDescending item queue) := by
  induction queue with
  | nil => simp [insertDescending, QueueDescending]
  | cons head tail ih =>
      rw [QueueDescending] at hqueue ⊢
      cases hqueue with
      | cons hhead htail =>
        simp only [insertDescending]
        split_ifs with hbefore
        · rw [List.pairwise_cons]
          exact ⟨by
            intro current hcurrent
            rcases List.mem_cons.mp hcurrent with rfl | hcurrent
            · exact hbefore
            · exact le_trans (hhead current hcurrent) hbefore,
            List.Pairwise.cons hhead htail⟩
        · rw [List.pairwise_cons]
          constructor
          · intro current hcurrent
            have hitem : item ∈ insertDescending item tail := by
              exact (insertDescending_perm item tail).mem_iff.mpr (by simp)
            have hmem := (insertDescending_perm item tail).mem_iff.mp hcurrent
            rcases List.mem_cons.mp hmem with heq | hcurrent
            · subst current
              exact Nat.le_of_not_ge hbefore
            · exact hhead current hcurrent
          · exact ih htail

theorem ordered_insertTagged {p k d : Nat}
    (stored : TaggedPivot p k d) {table : List (TaggedPivot p k d)}
    (hordered : Ordered (table.map TaggedPivot.pivot))
    (hfresh : ∀ old ∈ table, old.pivot.slot ≠ stored.pivot.slot) :
    Ordered ((insertTagged stored table).map TaggedPivot.pivot) := by
  rw [map_insertTagged]
  exact OrderedInsertion.ordered_insertPivot stored.pivot _ hordered
    (by intro pivot hpivot
        rcases List.mem_map.mp hpivot with ⟨entry, hentry, rfl⟩
        exact hfresh entry hentry)

theorem perm_extract {α : Type*} {value : α} {list : List α}
    (hvalue : value ∈ list) :
    ∃ front back,
      list = front ++ value :: back ∧
      list.Perm (value :: (front ++ back)) := by
  rcases List.eq_append_cons_of_mem hvalue with ⟨front, back, heq, hnot⟩
  refine ⟨front, back, heq, ?_⟩
  rw [heq]
  have hswap := (List.perm_append_comm (l₁ := front) (l₂ := [value])).append_right back
  simp

theorem ordered_replace_same_slot {p k d : Nat}
    (front back : List (TaggedPivot p k d)) (old stored : TaggedPivot p k d)
    (hordered : Ordered ((front ++ old :: back).map TaggedPivot.pivot))
    (hslot : stored.pivot.slot = old.pivot.slot) :
    Ordered ((front ++ stored :: back).map TaggedPivot.pivot) := by
  induction front with
  | nil =>
      rw [List.nil_append, List.map_cons, Ordered] at hordered ⊢
      cases hordered with
      | cons hhead htail =>
        constructor
        · intro pivot hpivot
          rw [hslot]
          exact hhead pivot hpivot
        · exact htail
  | cons head tail ih =>
      simp only [List.cons_append, List.map_cons, Ordered] at hordered ⊢
      cases hordered with
      | cons hhead htail =>
        constructor
        · intro pivot hpivot
          rcases List.mem_map.mp hpivot with ⟨entry, hentry, rfl⟩
          rcases List.mem_append.mp hentry with htailMem | hentry
          · exact hhead entry.pivot (by
              apply List.mem_map.mpr
              exact ⟨entry, by simp [htailMem], rfl⟩)
          · rcases List.mem_cons.mp hentry with rfl | hbackMem
            · rw [hslot]
              exact hhead old.pivot (by simp)
            · exact hhead entry.pivot (by
                apply List.mem_map.mpr
                exact ⟨entry, by simp [hbackMem], rfl⟩)
        · exact ih htail

def advanceAt {p k d : Nat} (task : WorkItem p k d) (slot : Slot d k)
    (row : Vector p k d)
    (hzero : ∀ column : Fin d, column ≤ slot.1 → row column = 0) :
    WorkItem p k d where
  entry := task.entry.withRow row
  startColumn := (slot.1 : Nat) + 1
  remaining := d - ((slot.1 : Nat) + 1)
  remaining_eq := rfl
  zerosBefore := by
    intro column hcolumn
    exact hzero column (by omega)

@[simp] theorem advanceAt_entry {p k d : Nat} (task : WorkItem p k d)
    (slot : Slot d k) (row : Vector p k d) (hzero) :
    (advanceAt task slot row hzero).entry = task.entry.withRow row := rfl

@[simp] theorem advanceAt_start {p k d : Nat} (task : WorkItem p k d)
    (slot : Slot d k) (row : Vector p k d) (hzero) :
    (advanceAt task slot row hzero).startColumn = (slot.1 : Nat) + 1 := rfl

theorem advanceAt_remaining_lt {p k d : Nat} (task : WorkItem p k d)
    (slot : Slot d k) (row : Vector p k d) (hzero)
    (hstart : task.startColumn ≤ (slot.1 : Nat)) :
    (advanceAt task slot row hzero).remaining < task.remaining := by
  rw [task.remaining_eq]
  change d - ((slot.1 : Nat) + 1) < d - task.startColumn
  have := slot.1.isLt
  omega

def requeueAt {p k d : Nat} (old : TaggedPivot p k d) (slot : Slot d k)
    (row : Vector p k d)
    (hzero : ∀ column : Fin d, column ≤ slot.1 → row column = 0) :
    WorkItem p k d where
  entry := old.asVector.withRow row
  startColumn := (slot.1 : Nat) + 1
  remaining := d - ((slot.1 : Nat) + 1)
  remaining_eq := rfl
  zerosBefore := by
    intro column hcolumn
    exact hzero column (by omega)

@[simp] theorem requeueAt_entry {p k d : Nat} (old : TaggedPivot p k d)
    (slot : Slot d k) (row : Vector p k d) (hzero) :
    (requeueAt old slot row hzero).entry = old.asVector.withRow row := rfl

@[simp] theorem requeueAt_start {p k d : Nat} (old : TaggedPivot p k d)
    (slot : Slot d k) (row : Vector p k d) (hzero) :
    (requeueAt old slot row hzero).startColumn = (slot.1 : Nat) + 1 := rfl

abbrev ScanResult {p k d : Nat} (task : WorkItem p k d)
    (table : List (TaggedPivot p k d)) :=
  Σ after : List (TaggedPivot p k d),
    Σ replacement : Option (WorkItem p k d),
      Σ visits : Nat, Scan task table after replacement visits

/-- A maximal-timestamp task always has a complete legal scan. -/
theorem scan_nonempty {p k d : Nat} (hp : p.Prime)
    {source : List (SourceVector p k d)}
    (hstrict : SourceStrict source)
    {task : WorkItem p k d} {rest : List (WorkItem p k d)}
    {table : List (TaggedPivot p k d)}
    (hdescending : QueueDescending (task :: rest))
    (hordered : Ordered (table.map TaggedPivot.pivot))
    (hkeys : ActiveKeysNodup table (task :: rest))
    (htable : TableLayerValid source table)
    (hqueue : QueueLayerValid source (task :: rest))
    (hprotected : ProtectedActive hp source table (task :: rest)) :
    Nonempty (ScanResult task table) := by
  classical
  generalize hremainingEq : task.remaining = remaining
  induction remaining using Nat.strong_induction_on generalizing task rest table with
  | h remaining ih =>
      by_cases hzero : task.entry.row = 0
      · exact ⟨table, none, 0, Scan.zero hzero⟩
      · rcases exists_hasLead hp.one_lt hzero with ⟨slot, hlead⟩
        have hstart : task.startColumn ≤ (slot.1 : Nat) := by
          by_contra hnot
          have hbefore : (slot.1 : Nat) < task.startColumn := Nat.lt_of_not_ge hnot
          exact hlead.exactAt.ne_zero hp.one_lt slot.2.isLt
            (task.zerosBefore slot.1 hbefore)
        by_cases hcollisionExists : ∃ old ∈ table, old.pivot.slot = slot
        · rcases hcollisionExists with ⟨old, holdMem, hcollision⟩
          rcases perm_extract holdMem with ⟨front, back, htableEq, hbeforePerm⟩
          let others := front ++ back
          rcases lt_trichotomy old.timestamp task.entry.timestamp with
            holdNewer | hsame | htaskOlder
          · rcases exists_normalized_pivot hp hlead with
              ⟨pivot, hpivotSlot, unit, hpivotRow⟩
            let stored : TaggedPivot p k d :=
              { timestamp := task.entry.timestamp, layer := task.entry.layer, pivot := pivot }
            have hstoredEq : stored.asVector =
                task.entry.withRow ((unit : Ring p k) • task.entry.row) := by
              dsimp [stored, TaggedPivot.asVector, TaggedVector.withRow]
              rw [hpivotRow]
            have hstoredSlot : stored.pivot.slot = slot := hpivotSlot
            let after := front ++ stored :: back
            have hafterPerm : after.Perm (stored :: others) := by
              dsimp [after, others]
              have hswap :=
                (List.perm_append_comm (l₁ := front) (l₂ := [stored])).append_right back
              simp
            have horderedDecomp : Ordered ((front ++ old :: back).map TaggedPivot.pivot) := by
              rw [← htableEq]
              exact hordered
            have hafterOrdered : Ordered (after.map TaggedPivot.pivot) := by
              exact ordered_replace_same_slot front back old stored horderedDecomp
                (hstoredSlot.trans hcollision.symm)
            have holdLead : HasLead old.pivot.row stored.pivot.slot := by
              have := PivotRow.hasLead hp.one_lt old.pivot
              simpa [hstoredSlot, hcollision] using this
            rcases zero_through_pivot stored.pivot holdLead with ⟨factor, hresidualZero⟩
            let residualRow := old.pivot.row - factor • stored.pivot.row
            have hzeroThrough : ∀ column : Fin d, column ≤ slot.1 →
                residualRow column = 0 := by
              intro column hcolumn
              exact hresidualZero column (by simpa [hstoredSlot] using hcolumn)
            by_cases hresidual : residualRow = 0
            · refine ⟨after, none, crossed task slot, ?_⟩
              apply Scan.replaceZero hlead hstart hbeforePerm hcollision holdNewer unit factor
                hstoredEq hstoredSlot hafterPerm hafterOrdered
              rw [← hpivotRow]
              exact hresidual
            · let replacement := requeueAt old slot residualRow hzeroThrough
              refine ⟨after, some replacement, crossed task slot, ?_⟩
              apply Scan.replace hlead hstart hbeforePerm hcollision holdNewer unit factor
                hstoredEq hstoredSlot hafterPerm hafterOrdered
              · dsimp [replacement]
                congr 1
                dsimp [residualRow, stored]
                rw [hpivotRow]
              · exact requeueAt_start old slot residualRow hzeroThrough
              · change residualRow ≠ 0
                exact hresidual
          · have hfalse := same_timestamp_collision_impossible hp hstrict hordered
              hkeys htable hqueue hprotected (List.mem_cons_self)
              hdescending.head_maximal holdMem hsame hlead hcollision
            exact False.elim hfalse
          · have taskLeadAtStored : HasLead task.entry.row old.pivot.slot := by
              simpa [hcollision] using hlead
            rcases zero_through_pivot old.pivot taskLeadAtStored with
              ⟨factor, hresidualZero⟩
            let residualRow := task.entry.row - factor • old.pivot.row
            have hzeroThrough : ∀ column : Fin d, column ≤ slot.1 →
                residualRow column = 0 := by
              intro column hcolumn
              exact hresidualZero column (by simpa [hcollision] using hcolumn)
            let residual := advanceAt task slot residualRow hzeroThrough
            have hresidualValid : LayerValid source residual.entry := by
              have htaskValid := hqueue task (by simp)
              have holdValid := htable old holdMem
              change LayerValid source (task.entry.withRow residualRow)
              exact htaskValid.sub_newer holdValid htaskOlder factor
            have hrestValid : QueueLayerValid source rest := by
              intro current hcurrent
              exact hqueue current (by simp [hcurrent])
            have hqueueResidual : QueueLayerValid source (residual :: rest) := by
              intro current hcurrent
              rcases List.mem_cons.mp hcurrent with rfl | hcurrent
              · exact hresidualValid
              · exact hrestValid current hcurrent
            have hdescendingResidual : QueueDescending (residual :: rest) := by
              rw [QueueDescending, List.pairwise_cons]
              constructor
              · intro current hcurrent
                have hle := (List.pairwise_cons.1 hdescending).1 current hcurrent
                simpa [residual, advanceAt, TaggedVector.withRow] using hle
              · exact hdescending.tail
            have hkeyEq : key residual.entry = key task.entry := by
              simp [residual]
            have hkeysResidual : ActiveKeysNodup table (residual :: rest) := by
              simpa [ActiveKeysNodup, activeKeys, queueKeys, hkeyEq] using hkeys
            have hprotectedResidual : ProtectedActive hp source table (residual :: rest) := by
              simpa [ProtectedActive, activeKeys, queueKeys, hkeyEq] using hprotected
            have hlt := advanceAt_remaining_lt task slot residualRow hzeroThrough hstart
            have hlt' : residual.remaining < remaining := by
              rw [← hremainingEq]
              exact hlt
            rcases ih residual.remaining hlt' hdescendingResidual hordered
              hkeysResidual htable hqueueResidual hprotectedResidual rfl with
              ⟨after, replacement, visits, tailScan⟩
            exact ⟨after, replacement, crossed task slot + visits,
              Scan.reduce hlead hstart hbeforePerm hcollision htaskOlder factor
                (by rfl) (by rfl) tailScan⟩
        · rcases exists_normalized_pivot hp hlead with
            ⟨pivot, hpivotSlot, unit, hpivotRow⟩
          let stored : TaggedPivot p k d :=
            { timestamp := task.entry.timestamp, layer := task.entry.layer, pivot := pivot }
          have hstoredEq : stored.asVector =
              task.entry.withRow ((unit : Ring p k) • task.entry.row) := by
            dsimp [stored, TaggedPivot.asVector, TaggedVector.withRow]
            rw [hpivotRow]
          have hstoredSlot : stored.pivot.slot = slot := hpivotSlot
          let after := insertTagged stored table
          have hafterOrdered : Ordered (after.map TaggedPivot.pivot) := by
            apply ordered_insertTagged stored hordered
            intro old hold hsameSlot
            apply hcollisionExists
            exact ⟨old, hold, by simpa [hstoredSlot] using hsameSlot⟩
          refine ⟨after, none, crossed task slot, ?_⟩
          exact Scan.store hlead hstart
            (by
              intro old hold hsameSlot
              apply hcollisionExists
              exact ⟨old, hold, by simpa [hstoredSlot] using hsameSlot⟩)
            unit hstoredEq hstoredSlot (perm_insertTagged stored table) hafterOrdered

def queuePotential {p k d : Nat} (queue : List (WorkItem p k d)) : Nat :=
  queue.length + (queueBudgets queue).sum

theorem queuePotential_perm {p k d : Nat}
    {before after : List (WorkItem p k d)} (hperm : before.Perm after) :
    queuePotential before = queuePotential after := by
  unfold queuePotential
  rw [hperm.length_eq, (queueBudgets_perm hperm).sum_eq]

abbrev DrainResult {p k d : Nat} (queue : List (WorkItem p k d))
    (table : List (TaggedPivot p k d)) :=
  Σ after : List (TaggedPivot p k d),
    Σ visits : Nat, Σ pops : Nat, Drain queue table after visits pops

/-- Repeatedly choosing the maximal timestamp and reinserting the one possible
displaced residual terminates.  The measure is queue length plus the sum of
all remaining-column budgets. -/
theorem drain_nonempty {p k d : Nat} (hp : p.Prime)
    {source : List (SourceVector p k d)}
    (hstrict : SourceStrict source)
    {queue : List (WorkItem p k d)} {table : List (TaggedPivot p k d)}
    (hdescending : QueueDescending queue)
    (hordered : Ordered (table.map TaggedPivot.pivot))
    (hkeys : ActiveKeysNodup table queue)
    (htable : TableLayerValid source table)
    (hqueue : QueueLayerValid source queue)
    (hprotected : ProtectedActive hp source table queue) :
    Nonempty (DrainResult queue table) := by
  classical
  generalize hpotentialEq : queuePotential queue = potential
  induction potential using Nat.strong_induction_on generalizing queue table with
  | h potential ih =>
      cases queue with
      | nil =>
          exact ⟨⟨table, 0, 0, Drain.done table⟩⟩
      | cons task rest =>
          have htask : LayerValid source task.entry := hqueue task (by simp)
          have hrest : QueueLayerValid source rest := by
            intro current hcurrent
            exact hqueue current (by simp [hcurrent])
          rcases scan_nonempty hp hstrict hdescending hordered hkeys htable hqueue
              hprotected with ⟨middle, replacement, visits, scan⟩
          have hmiddleOrdered : Ordered (middle.map TaggedPivot.pivot) :=
            scan.preservesOrdered hordered
          have hscanValid := scan.preservesLayerValid htask htable
          have hscanStrong := scan_preservesKeysAndProtected hp
            (SourceStrict.timestampInjective hstrict) scan rest htask htable hkeys hprotected
          cases replacement with
          | none =>
              have hmiddleKeys : ActiveKeysNodup middle rest := by
                simpa using hscanStrong.1
              have hmiddleProtected : ProtectedActive hp source middle rest := by
                simpa using hscanStrong.2
              have hlt : queuePotential rest < potential := by
                rw [← hpotentialEq]
                simp [queuePotential, queueBudgets]
                omega
              rcases ih (queuePotential rest) hlt hdescending.tail hmiddleOrdered
                  hmiddleKeys hscanValid.1 hrest hmiddleProtected rfl with
                ⟨after, tailVisits, tailPops, tail⟩
              exact ⟨⟨after, visits + tailVisits, tailPops + 1,
                Drain.stop scan tail⟩⟩
          | some val =>
              let next := insertDescending val rest
              have hrawValid : QueueLayerValid source (val :: rest) := by
                intro current hcurrent
                rcases List.mem_cons.mp hcurrent with rfl | hcurrent
                · exact hscanValid.2 current rfl
                · exact hrest current hcurrent
              have hrawKeys : ActiveKeysNodup middle (val :: rest) := by
                simpa using hscanStrong.1
              have hrawProtected : ProtectedActive hp source middle (val :: rest) := by
                simpa using hscanStrong.2
              have hnextPerm : next.Perm (val :: rest) :=
                insertDescending_perm val rest
              have hnextDescending : QueueDescending next :=
                insertDescending_ordered val hdescending.tail
              have hnextStrong := queuePerm_preserves hp middle hnextPerm.symm
                hrawValid hrawKeys hrawProtected
              have hcertificate := scan.toPopCertificate
              have hbudget := hcertificate.replacement_budget val rfl
              have hrawLt : queuePotential (val :: rest) <
                  queuePotential (task :: rest) := by
                simp only [queuePotential, queueBudgets, List.map_cons, List.sum_cons,
                  List.length_cons]
                rw [hbudget.2]
                have := hcertificate.visits_le
                omega
              have hnextLt : queuePotential next < potential := by
                rw [queuePotential_perm hnextPerm, ← hpotentialEq]
                exact hrawLt
              rcases ih (queuePotential next) hnextLt hnextDescending hmiddleOrdered
                  hnextStrong.2.1 hscanValid.1 hnextStrong.1 hnextStrong.2.2 rfl with
                ⟨after, tailVisits, tailPops, tail⟩
              exact ⟨⟨after, visits + tailVisits, tailPops + 1,
                Drain.requeue scan hnextPerm tail⟩⟩

theorem initialQueue_descending {p k d : Nat} (item : SourceVector p k d) :
    QueueDescending (initialQueue (powerEntry item)) := by
  rw [QueueDescending]
  apply List.pairwise_of_forall_mem_list
  intro earlier hearlier later hlater
  rw [initialQueue, List.mem_ofFn'] at hearlier hlater
  rcases hearlier with ⟨earlierIndex, rfl⟩
  rcases hlater with ⟨laterIndex, rfl⟩
  simp [powerEntry]

/-- The fully constructed result of one append.  Besides the new verified
table it retains the concrete drain and its exact operation counters. -/
structure AppendResult {p k d : Nat} {hp : Nat.Prime p}
    {source : List (SourceVector p k d)} (table : FastTable hp source)
    (item : SourceVector p k d) where
  result : FastTable hp (source ++ [item])
  after : List (TaggedPivot p k d)
  result_entries : result.entries = after
  visits : Nat
  pops : Nat
  drain : Drain (initialQueue (powerEntry item)) table.entries
    after visits pops
  visits_le : visits ≤ k * d
  pops_le : pops ≤ k * (d + 1)
  valuations_le : drain.valuations ≤ k * d
  normalizations_le : drain.normalizations ≤ k * d
  vectorPasses_le : drain.vectorPasses ≤ 2 * (k * d)
  cellOps_le : drain.vectorPasses * d ≤ 2 * k * d * d

/-- A legal latest-timestamp append always produces a verified table; no
termination or successful-execution premise remains. -/
theorem appendResult_nonempty {p k d : Nat} (hp : p.Prime)
    {source : List (SourceVector p k d)} (table : FastTable hp source)
    (item : SourceVector p k d)
    (hlatest : ∀ old ∈ source, old.timestamp < item.timestamp) :
    Nonempty (AppendResult table item) := by
  let fullSource := source ++ [item]
  have hstrict : SourceStrict fullSource := sourceStrict_append table.strict item hlatest
  have htable : TableLayerValid fullSource table.entries :=
    tableValid_append_source table.valid item
  have hqueue : QueueLayerValid fullSource (initialQueue (powerEntry item)) :=
    initialQueue_valid fullSource item (show item ∈ source ++ [item] by simp)
  have hkeys : ActiveKeysNodup table.entries (initialQueue (powerEntry item)) :=
    initial_active_keys_nodup table item hlatest
  have hprotected : ProtectedActive hp fullSource table.entries
      (initialQueue (powerEntry item)) := initial_protected hp table item
  rcases drain_nonempty hp hstrict (initialQueue_descending item) table.ordered
      hkeys htable hqueue hprotected with ⟨after, visits, pops, drain⟩
  rcases append_correct_and_bounded hp table item hlatest drain with
    ⟨result, hresult, hcorrect, hvisits, hpops, hvaluations,
      hnormalizations, hpasses, hcells⟩
  exact ⟨⟨result, after, hresult, visits, pops, drain, hvisits, hpops,
    hvaluations, hnormalizations, hpasses, hcells⟩⟩

noncomputable def totalAppend {p k d : Nat} (hp : p.Prime)
    {source : List (SourceVector p k d)} (table : FastTable hp source)
    (item : SourceVector p k d)
    (hlatest : ∀ old ∈ source, old.timestamp < item.timestamp) :
    AppendResult table item :=
  Classical.choice (appendResult_nonempty hp table item hlatest)

end CompositeModulusBasis.Totality
