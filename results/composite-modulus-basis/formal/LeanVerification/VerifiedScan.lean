import LeanVerification.TerminalExtraction
import Mathlib.Tactic

/-!
# Proof-relevant scan of one popped task

This relation mirrors the three branches of the implementation: store in an
empty slot, reduce by a newer row and continue, or replace an older row and
requeue its residual.  A same-timestamp collision deliberately has no
constructor; it is ruled out from the cyclic-layer invariant.
-/

namespace CompositeModulusBasis.VerifiedScan

open PadicEchelon TimestampedBasis TimestampLayerInvariant WorklistRefinement

def crossed {p k d : Nat} (task : WorkItem p k d) (slot : Slot d k) : Nat :=
  (slot.1 : Nat) + 1 - task.startColumn

theorem crossed_pos {p k d : Nat} (task : WorkItem p k d) (slot : Slot d k)
    (hstart : task.startColumn ≤ (slot.1 : Nat)) : 0 < crossed task slot := by
  unfold crossed
  omega

theorem crossed_le {p k d : Nat} (task : WorkItem p k d) (slot : Slot d k)
    (hstart : task.startColumn ≤ (slot.1 : Nat)) :
    crossed task slot ≤ task.remaining := by
  rw [task.remaining_eq]
  unfold crossed
  have := slot.1.isLt
  omega

/-- The complete scan performed during one heap pop. -/
inductive Scan {p k d : Nat} :
    WorkItem p k d → List (TaggedPivot p k d) →
      List (TaggedPivot p k d) → Option (WorkItem p k d) → Nat → Type where
  | zero {task table} (hzero : task.entry.row = 0) :
      Scan task table table none 0
  | store {task before after stored slot}
      (lead : HasLead task.entry.row slot)
      (hstart : task.startColumn ≤ (slot.1 : Nat))
      (slotEmpty : ∀ old ∈ before, old.pivot.slot ≠ slot)
      (unit : (Ring p k)ˣ)
      (storedEq : stored.asVector =
        task.entry.withRow ((unit : Ring p k) • task.entry.row))
      (storedSlot : stored.pivot.slot = slot)
      (afterPerm : after.Perm (stored :: before))
      (afterOrdered : Ordered (after.map TaggedPivot.pivot)) :
      Scan task before after none (crossed task slot)
  | replace {task replacement before after old stored others slot}
      (lead : HasLead task.entry.row slot)
      (hstart : task.startColumn ≤ (slot.1 : Nat))
      (beforePerm : before.Perm (old :: others))
      (collision : old.pivot.slot = slot)
      (newer : old.timestamp < task.entry.timestamp)
      (unit : (Ring p k)ˣ) (factor : Ring p k)
      (storedEq : stored.asVector =
        task.entry.withRow ((unit : Ring p k) • task.entry.row))
      (storedSlot : stored.pivot.slot = slot)
      (afterPerm : after.Perm (stored :: others))
      (afterOrdered : Ordered (after.map TaggedPivot.pivot))
      (replacementEq : replacement.entry = old.asVector.withRow
        (old.pivot.row - factor • ((unit : Ring p k) • task.entry.row)))
      (replacementStart : replacement.startColumn = (slot.1 : Nat) + 1)
      (replacementNonzero : replacement.entry.row ≠ 0) :
      Scan task before after (some replacement) (crossed task slot)
  | replaceZero {task before after old stored others slot}
      (lead : HasLead task.entry.row slot)
      (hstart : task.startColumn ≤ (slot.1 : Nat))
      (beforePerm : before.Perm (old :: others))
      (collision : old.pivot.slot = slot)
      (newer : old.timestamp < task.entry.timestamp)
      (unit : (Ring p k)ˣ) (factor : Ring p k)
      (storedEq : stored.asVector =
        task.entry.withRow ((unit : Ring p k) • task.entry.row))
      (storedSlot : stored.pivot.slot = slot)
      (afterPerm : after.Perm (stored :: others))
      (afterOrdered : Ordered (after.map TaggedPivot.pivot))
      (residualZero : old.pivot.row -
        factor • ((unit : Ring p k) • task.entry.row) = 0) :
      Scan task before after none (crossed task slot)
  | reduce {task residual stored others before after replacement slot tailVisits}
      (lead : HasLead task.entry.row slot)
      (hstart : task.startColumn ≤ (slot.1 : Nat))
      (beforePerm : before.Perm (stored :: others))
      (collision : stored.pivot.slot = slot)
      (newer : task.entry.timestamp < stored.timestamp)
      (factor : Ring p k)
      (residualEq : residual.entry = task.entry.withRow
        (task.entry.row - factor • stored.pivot.row))
      (residualStart : residual.startColumn = (slot.1 : Nat) + 1)
      (tail : Scan residual before after replacement tailVisits) :
      Scan task before after replacement (crossed task slot + tailVisits)

/-- Number of full length-`d` row traversals performed by a scan.  Storing a
row normalizes it once; replacing an older row additionally forms its
residual, hence costs two traversals. -/
def Scan.vectorPasses {p k d : Nat}
    {task : WorkItem p k d} {before after : List (TaggedPivot p k d)}
    {replacement : Option (WorkItem p k d)} {visits : Nat} :
    Scan task before after replacement visits → Nat
  | .zero _ => 0
  | .store _ _ _ _ _ _ _ _ => 1
  | .replace _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 2
  | .replaceZero _ _ _ _ _ _ _ _ _ _ _ _ => 2
  | .reduce _ _ _ _ _ _ _ _ tail => tail.vectorPasses + 1

/-- Number of nonzero coordinates whose p-adic valuation is inspected. -/
def Scan.valuations {p k d : Nat}
    {task : WorkItem p k d} {before after : List (TaggedPivot p k d)}
    {replacement : Option (WorkItem p k d)} {visits : Nat} :
    Scan task before after replacement visits → Nat
  | .zero _ => 0
  | .store _ _ _ _ _ _ _ _ => 1
  | .replace _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 1
  | .replaceZero _ _ _ _ _ _ _ _ _ _ _ _ => 1
  | .reduce _ _ _ _ _ _ _ _ tail => tail.valuations + 1

/-- Number of unit inversions/normalizations. -/
def Scan.normalizations {p k d : Nat}
    {task : WorkItem p k d} {before after : List (TaggedPivot p k d)}
    {replacement : Option (WorkItem p k d)} {visits : Nat} :
    Scan task before after replacement visits → Nat
  | .zero _ => 0
  | .store _ _ _ _ _ _ _ _ => 1
  | .replace _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 1
  | .replaceZero _ _ _ _ _ _ _ _ _ _ _ _ => 1
  | .reduce _ _ _ _ _ _ _ _ tail => tail.normalizations

theorem Scan.vectorPasses_le_twice_visits {p k d : Nat}
    {task : WorkItem p k d} {before after : List (TaggedPivot p k d)}
    {replacement : Option (WorkItem p k d)} {visits : Nat}
    (scan : Scan task before after replacement visits) :
    scan.vectorPasses ≤ 2 * visits := by
  induction scan with
  | zero hzero => simp [Scan.vectorPasses]
  | store lead hstart slotEmpty unit storedEq storedSlot afterPerm afterOrdered =>
      have hpositive := crossed_pos _ _ hstart
      simp only [Scan.vectorPasses]
      omega
  | replace lead hstart beforePerm collision newer unit factor storedEq storedSlot
      afterPerm afterOrdered replacementEq replacementStart replacementNonzero =>
      have hpositive := crossed_pos _ _ hstart
      simp only [Scan.vectorPasses]
      omega
  | replaceZero lead hstart beforePerm collision newer unit factor storedEq storedSlot
      afterPerm afterOrdered residualZero =>
      have hpositive := crossed_pos _ _ hstart
      simp only [Scan.vectorPasses]
      omega
  | reduce lead hstart beforePerm collision newer factor residualEq residualStart tail ih =>
      have hpositive := crossed_pos _ _ hstart
      simp only [Scan.vectorPasses]
      omega

theorem Scan.valuations_le_visits {p k d : Nat}
    {task : WorkItem p k d} {before after : List (TaggedPivot p k d)}
    {replacement : Option (WorkItem p k d)} {visits : Nat}
    (scan : Scan task before after replacement visits) :
    scan.valuations ≤ visits := by
  induction scan with
  | zero hzero => simp [Scan.valuations]
  | store lead hstart slotEmpty unit storedEq storedSlot afterPerm afterOrdered =>
      have hpositive := crossed_pos _ _ hstart
      simp only [Scan.valuations]
      omega
  | replace lead hstart beforePerm collision newer unit factor storedEq storedSlot
      afterPerm afterOrdered replacementEq replacementStart replacementNonzero =>
      have hpositive := crossed_pos _ _ hstart
      simp only [Scan.valuations]
      omega
  | replaceZero lead hstart beforePerm collision newer unit factor storedEq storedSlot
      afterPerm afterOrdered residualZero =>
      have hpositive := crossed_pos _ _ hstart
      simp only [Scan.valuations]
      omega
  | reduce lead hstart beforePerm collision newer factor residualEq residualStart tail ih =>
      have hpositive := crossed_pos _ _ hstart
      simp only [Scan.valuations]
      omega

theorem Scan.normalizations_le_valuations {p k d : Nat}
    {task : WorkItem p k d} {before after : List (TaggedPivot p k d)}
    {replacement : Option (WorkItem p k d)} {visits : Nat}
    (scan : Scan task before after replacement visits) :
    scan.normalizations ≤ scan.valuations := by
  induction scan <;> simp_all [Scan.normalizations, Scan.valuations]
  omega

theorem replacement_budget {p k d : Nat}
    {task replacement : WorkItem p k d} {slot : Slot d k}
    (hstart : task.startColumn ≤ (slot.1 : Nat))
    (hreplacement : replacement.startColumn = (slot.1 : Nat) + 1) :
    replacement.remaining = task.remaining - crossed task slot := by
  rw [replacement.remaining_eq, task.remaining_eq, hreplacement]
  unfold crossed
  omega

/-- Every proof-relevant scan produces the semantic/budget certificate consumed
by the drain and complexity theorems. -/
theorem Scan.toPopCertificate {p k d : Nat}
    {task : WorkItem p k d} {before after : List (TaggedPivot p k d)}
    {replacement : Option (WorkItem p k d)} {visits : Nat}
    (scan : Scan task before after replacement visits) :
    PopCertificate task before after replacement visits := by
  induction scan with
  | zero hzero => exact pop_zero _ _ _ (by simp) hzero
  | store lead hstart slotEmpty unit storedEq storedSlot afterPerm afterOrdered =>
      exact pop_store _ _ _ _ unit _ (crossed_le _ _ hstart) storedEq afterPerm
  | @replace task replacement before after old stored others slot lead hstart
      beforePerm collision newer unit factor storedEq storedSlot afterPerm
      afterOrdered replacementEq replacementStart replacementNonzero =>
      exact pop_replace task replacement before after old stored others unit factor _
        (crossed_pos task slot hstart) (crossed_le task slot hstart)
        (Nat.le_of_lt newer) beforePerm afterPerm storedEq replacementEq
        (replacement_budget hstart replacementStart)
  | replaceZero lead hstart beforePerm collision newer unit factor storedEq storedSlot
      afterPerm afterOrdered residualZero =>
      exact pop_replace_zero _ _ _ _ _ _ unit factor _
        (crossed_le _ _ hstart) (Nat.le_of_lt newer) beforePerm afterPerm storedEq residualZero
  | @reduce task residual stored others before after replacement slot tailVisits
      lead hstart beforePerm collision newer factor residualEq residualStart tail ih =>
      exact ih.prependReduction task residual stored others before after replacement factor
        tailVisits (crossed task slot) beforePerm (Nat.le_of_lt newer) residualEq
        (replacement_budget hstart residualStart)
        (crossed_pos task slot hstart) (crossed_le task slot hstart)

/-- Every scan branch preserves the source-layer identity of all stored and
requeued rows. -/
theorem Scan.preservesLayerValid {p k d : Nat}
    {source : List (SourceVector p k d)}
    {task : WorkItem p k d} {before after : List (TaggedPivot p k d)}
    {replacement : Option (WorkItem p k d)} {visits : Nat}
    (scan : Scan task before after replacement visits)
    (htask : LayerValid source task.entry)
    (htable : TableLayerValid source before) :
    TableLayerValid source after ∧
      ∀ next, replacement = some next → LayerValid source next.entry := by
  induction scan generalizing source with
  | zero hzero =>
      exact ⟨htable, by intro next hnone; simp at hnone⟩
  | @store task before after stored slot lead hstart slotEmpty unit storedEq storedSlot
      afterPerm afterOrdered =>
      have hstored : LayerValid source stored.asVector := by
        rw [storedEq]
        exact htask.unit_smul unit
      constructor
      · intro entry hentry
        have hmem := afterPerm.mem_iff.mp hentry
        rcases List.mem_cons.mp hmem with rfl | hbefore
        · exact hstored
        · exact htable entry hbefore
      · intro next hnone
        simp at hnone
  | @replace task replacement before after old stored others slot lead hstart
      beforePerm collision newer unit factor storedEq storedSlot afterPerm
      afterOrdered replacementEq replacementStart replacementNonzero =>
      have holdMem : old ∈ before := beforePerm.mem_iff.mpr (by simp)
      have holdValid : LayerValid source old.asVector := htable old holdMem
      have hstored : LayerValid source stored.asVector := by
        rw [storedEq]
        exact htask.unit_smul unit
      have hrequeued : LayerValid source replacement.entry := by
        rw [replacementEq]
        exact holdValid.sub_newer (htask.unit_smul unit) newer factor
      constructor
      · intro entry hentry
        have hmem := afterPerm.mem_iff.mp hentry
        rcases List.mem_cons.mp hmem with rfl | hothers
        · exact hstored
        · apply htable entry
          exact beforePerm.mem_iff.mpr (by simp [hothers])
      · intro next hnext
        simp only [Option.some.injEq] at hnext
        subst next
        exact hrequeued
  | @replaceZero task before after old stored others slot lead hstart
      beforePerm collision newer unit factor storedEq storedSlot afterPerm afterOrdered residualZero =>
      have hstored : LayerValid source stored.asVector := by
        rw [storedEq]
        exact htask.unit_smul unit
      constructor
      · intro entry hentry
        have hmem := afterPerm.mem_iff.mp hentry
        rcases List.mem_cons.mp hmem with rfl | hothers
        · exact hstored
        · apply htable entry
          exact beforePerm.mem_iff.mpr (by simp [hothers])
      · intro next hnone
        simp at hnone
  | @reduce task residual stored others before after replacement slot tailVisits
      lead hstart beforePerm collision newer factor residualEq residualStart tail ih =>
      have hstoredMem : stored ∈ before := beforePerm.mem_iff.mpr (by simp)
      have hstoredValid : LayerValid source stored.asVector := htable stored hstoredMem
      have hresidualValid : LayerValid source residual.entry := by
        rw [residualEq]
        exact htask.sub_newer hstoredValid newer factor
      exact ih hresidualValid htable

theorem Scan.preservesOrdered {p k d : Nat}
    {task : WorkItem p k d} {before after : List (TaggedPivot p k d)}
    {replacement : Option (WorkItem p k d)} {visits : Nat}
    (scan : Scan task before after replacement visits)
    (hbefore : Ordered (before.map TaggedPivot.pivot)) :
    Ordered (after.map TaggedPivot.pivot) := by
  induction scan with
  | zero hzero => exact hbefore
  | store lead hstart slotEmpty unit storedEq storedSlot afterPerm afterOrdered =>
      exact afterOrdered
  | replace lead hstart beforePerm collision newer unit factor storedEq storedSlot
      afterPerm afterOrdered replacementEq replacementStart replacementNonzero =>
      exact afterOrdered
  | replaceZero lead hstart beforePerm collision newer unit factor storedEq storedSlot
      afterPerm afterOrdered residualZero => exact afterOrdered
  | reduce lead hstart beforePerm collision newer factor residualEq residualStart tail ih =>
      exact ih hbefore

/-- The heap drain whose per-pop work is the concrete `Scan` relation above. -/
inductive Drain {p k d : Nat} :
    List (WorkItem p k d) → List (TaggedPivot p k d) →
      List (TaggedPivot p k d) → Nat → Nat → Type where
  | done (table) : Drain [] table table 0 0
  | stop {task rest before middle after visits tailVisits tailPops}
      (scan : Scan task before middle none visits)
      (tail : Drain rest middle after tailVisits tailPops) :
      Drain (task :: rest) before after (visits + tailVisits) (tailPops + 1)
  | requeue {task rest before middle after replacement next
      visits tailVisits tailPops}
      (scan : Scan task before middle (some replacement) visits)
      (queueOrder : next.Perm (replacement :: rest))
      (tail : Drain next middle after tailVisits tailPops) :
      Drain (task :: rest) before after (visits + tailVisits) (tailPops + 1)

def Drain.vectorPasses {p k d : Nat}
    {queue : List (WorkItem p k d)} {before after : List (TaggedPivot p k d)}
    {visits pops : Nat} : Drain queue before after visits pops → Nat
  | .done _ => 0
  | .stop scan tail => scan.vectorPasses + tail.vectorPasses
  | .requeue scan _ tail => scan.vectorPasses + tail.vectorPasses

def Drain.valuations {p k d : Nat}
    {queue : List (WorkItem p k d)} {before after : List (TaggedPivot p k d)}
    {visits pops : Nat} : Drain queue before after visits pops → Nat
  | .done _ => 0
  | .stop scan tail => scan.valuations + tail.valuations
  | .requeue scan _ tail => scan.valuations + tail.valuations

def Drain.normalizations {p k d : Nat}
    {queue : List (WorkItem p k d)} {before after : List (TaggedPivot p k d)}
    {visits pops : Nat} : Drain queue before after visits pops → Nat
  | .done _ => 0
  | .stop scan tail => scan.normalizations + tail.normalizations
  | .requeue scan _ tail => scan.normalizations + tail.normalizations

theorem Drain.vectorPasses_le_twice_visits {p k d : Nat}
    {queue : List (WorkItem p k d)} {before after : List (TaggedPivot p k d)}
    {visits pops : Nat} (drain : Drain queue before after visits pops) :
    drain.vectorPasses ≤ 2 * visits := by
  induction drain with
  | done table => simp [Drain.vectorPasses]
  | stop scan tail ih =>
      have hscan := scan.vectorPasses_le_twice_visits
      simp only [Drain.vectorPasses]
      omega
  | requeue scan queueOrder tail ih =>
      have hscan := scan.vectorPasses_le_twice_visits
      simp only [Drain.vectorPasses]
      omega

theorem Drain.valuations_le_visits {p k d : Nat}
    {queue : List (WorkItem p k d)} {before after : List (TaggedPivot p k d)}
    {visits pops : Nat} (drain : Drain queue before after visits pops) :
    drain.valuations ≤ visits := by
  induction drain with
  | done table => simp [Drain.valuations]
  | stop scan tail ih =>
      have hscan := scan.valuations_le_visits
      simp only [Drain.valuations]
      omega
  | requeue scan queueOrder tail ih =>
      have hscan := scan.valuations_le_visits
      simp only [Drain.valuations]
      omega

theorem Drain.normalizations_le_valuations {p k d : Nat}
    {queue : List (WorkItem p k d)} {before after : List (TaggedPivot p k d)}
    {visits pops : Nat} (drain : Drain queue before after visits pops) :
    drain.normalizations ≤ drain.valuations := by
  induction drain with
  | done table => simp [Drain.normalizations, Drain.valuations]
  | stop scan tail ih =>
      have hscan := scan.normalizations_le_valuations
      simp only [Drain.normalizations, Drain.valuations]
      omega
  | requeue scan queueOrder tail ih =>
      have hscan := scan.normalizations_le_valuations
      simp only [Drain.normalizations, Drain.valuations]
      omega

theorem Drain.toCertifiedDrain {p k d : Nat}
    {queue : List (WorkItem p k d)} {before after : List (TaggedPivot p k d)}
    {visits pops : Nat} (drain : Drain queue before after visits pops) :
    CertifiedDrain queue before after visits pops := by
  induction drain with
  | done table => exact .done table
  | stop scan tail ih => exact .stop scan.toPopCertificate ih
  | requeue scan queueOrder tail ih =>
      exact .requeue scan.toPopCertificate queueOrder ih

theorem Drain.thresholdEquivalent {p k d : Nat}
    {queue : List (WorkItem p k d)} {before after : List (TaggedPivot p k d)}
    {visits pops : Nat} (drain : Drain queue before after visits pops) :
    ThresholdEquivalent (activeRows before queue) (tableRows after) :=
  drain.toCertifiedDrain.thresholdEquivalent

theorem Drain.initial_bounds {p k d : Nat}
    (entries : Fin k → TaggedVector p k d)
    {before after : List (TaggedPivot p k d)} {visits pops : Nat}
    (drain : Drain (initialQueue entries) before after visits pops) :
    visits ≤ k * d ∧ pops ≤ k * (d + 1) ∧ visits * d ≤ k * d * d :=
  certified_insertion_bounds entries drain.toCertifiedDrain

/-- Exact implementation-facing bounds, including the two row traversals in
the replacement branch. -/
theorem Drain.initial_operational_bounds {p k d : Nat}
    (entries : Fin k → TaggedVector p k d)
    {before after : List (TaggedPivot p k d)} {visits pops : Nat}
    (drain : Drain (initialQueue entries) before after visits pops) :
    drain.valuations ≤ k * d ∧
      drain.normalizations ≤ k * d ∧
      drain.vectorPasses * d ≤ 2 * k * d * d := by
  have hvisits := (drain.initial_bounds entries).1
  refine ⟨drain.valuations_le_visits.trans hvisits,
    drain.normalizations_le_valuations.trans
      (drain.valuations_le_visits.trans hvisits), ?_⟩
  calc
    drain.vectorPasses * d ≤ (2 * visits) * d :=
      Nat.mul_le_mul_right d drain.vectorPasses_le_twice_visits
    _ ≤ (2 * (k * d)) * d :=
      Nat.mul_le_mul_right d (Nat.mul_le_mul_left 2 hvisits)
    _ = 2 * k * d * d := by ring

def QueueLayerValid {p k d : Nat} (source : List (SourceVector p k d))
    (queue : List (WorkItem p k d)) : Prop :=
  ∀ item ∈ queue, LayerValid source item.entry

def tableKeys {p k d : Nat} (table : List (TaggedPivot p k d)) :
    List (Nat × Nat) := table.map pivotKey

def optionKeys {p k d : Nat} (replacement : Option (WorkItem p k d)) :
    List (Nat × Nat) := replacement.toList.map (key ∘ WorkItem.entry)

theorem Scan.accounting {p k d : Nat}
    {source : List (SourceVector p k d)}
    {task : WorkItem p k d} {before after : List (TaggedPivot p k d)}
    {replacement : Option (WorkItem p k d)} {visits : Nat}
    (scan : Scan task before after replacement visits)
    (htask : LayerValid source task.entry)
    (htable : TableLayerValid source before) :
    ∃ dropped : List (TaggedVector p k d),
      (tableKeys before ++ [key task.entry]).Perm
        (tableKeys after ++ optionKeys replacement ++ dropped.map key) ∧
      (∀ entry ∈ dropped, entry.row = 0) ∧
      (∀ entry ∈ dropped, LayerValid source entry) := by
  induction scan generalizing source with
  | @zero task table hzero =>
      refine ⟨[task.entry], ?_, ?_, ?_⟩
      · simp [tableKeys, optionKeys]
      · simp [hzero]
      · simp [htask]
  | @store task before after stored slot lead hstart slotEmpty unit storedEq storedSlot
      afterPerm afterOrdered =>
      refine ⟨[], ?_, by simp, by simp⟩
      have hafterKeys : (tableKeys after).Perm
          (pivotKey stored :: tableKeys before) := afterPerm.map pivotKey
      have hstoredKey : pivotKey stored = key task.entry := by
        rw [← key_asVector, storedEq, key_withRow]
      have hin : (tableKeys before ++ [key task.entry]).Perm
          (key task.entry :: tableKeys before) := List.perm_append_comm
      rw [hstoredKey] at hafterKeys
      simpa [optionKeys] using hin.trans hafterKeys.symm
  | @replace task replacement before after old stored others slot lead hstart
      beforePerm collision newer unit factor storedEq storedSlot afterPerm
      afterOrdered replacementEq replacementStart replacementNonzero =>
      refine ⟨[], ?_, by simp, by simp⟩
      have hbeforeKeys : (tableKeys before).Perm
          (pivotKey old :: tableKeys others) := beforePerm.map pivotKey
      have hafterKeys : (tableKeys after).Perm
          (pivotKey stored :: tableKeys others) := afterPerm.map pivotKey
      have hstoredKey : pivotKey stored = key task.entry := by
        rw [← key_asVector, storedEq, key_withRow]
      have hreplacementKey : key replacement.entry = pivotKey old := by
        rw [replacementEq, key_withRow, key_asVector]
      have hin : (tableKeys before ++ [key task.entry]).Perm
          (key task.entry :: pivotKey old :: tableKeys others) :=
        (hbeforeKeys.append_right [key task.entry]).trans List.perm_append_comm
      have hrotate :
          (key task.entry :: pivotKey old :: tableKeys others).Perm
          (pivotKey stored :: tableKeys others ++ [key replacement.entry]) := by
        rw [hstoredKey, hreplacementKey]
        exact List.Perm.cons _ (by
          simpa using (List.perm_append_comm
            (l₁ := [pivotKey old]) (l₂ := tableKeys others)))
      have hout := hafterKeys.append_right [key replacement.entry]
      simpa [optionKeys, List.append_assoc] using hin.trans (hrotate.trans hout.symm)
  | @replaceZero task before after old stored others slot lead hstart
      beforePerm collision newer unit factor storedEq storedSlot afterPerm afterOrdered residualZero =>
      let residual := old.asVector.withRow
        (old.pivot.row - factor • ((unit : Ring p k) • task.entry.row))
      have holdValid : LayerValid source old.asVector :=
        htable old (beforePerm.mem_iff.mpr (by simp))
      have hresidualValid : LayerValid source residual := by
        exact holdValid.sub_newer (htask.unit_smul unit) newer factor
      refine ⟨[residual], ?_, ?_, ?_⟩
      · have hbeforeKeys : (tableKeys before).Perm
            (pivotKey old :: tableKeys others) := beforePerm.map pivotKey
        have hafterKeys : (tableKeys after).Perm
            (pivotKey stored :: tableKeys others) := afterPerm.map pivotKey
        have hstoredKey : pivotKey stored = key task.entry := by
          rw [← key_asVector, storedEq, key_withRow]
        have hresidualKey : key residual = pivotKey old := by
          simp [residual]
        have hin : (tableKeys before ++ [key task.entry]).Perm
            (key task.entry :: pivotKey old :: tableKeys others) :=
          (hbeforeKeys.append_right [key task.entry]).trans List.perm_append_comm
        have hrotate :
            (key task.entry :: pivotKey old :: tableKeys others).Perm
            (pivotKey stored :: tableKeys others ++ [key residual]) := by
          rw [hstoredKey, hresidualKey]
          exact List.Perm.cons _ (by
            simpa using (List.perm_append_comm
              (l₁ := [pivotKey old]) (l₂ := tableKeys others)))
        have hout := hafterKeys.append_right [key residual]
        simpa [optionKeys, List.append_assoc] using hin.trans (hrotate.trans hout.symm)
      · intro entry hentry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hentry
        subst entry
        exact residualZero
      · intro entry hentry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hentry
        subst entry
        exact hresidualValid
  | @reduce task residual stored others before after replacement slot tailVisits
      lead hstart beforePerm collision newer factor residualEq residualStart tail ih =>
      have hstoredValid : LayerValid source stored.asVector :=
        htable stored (beforePerm.mem_iff.mpr (by simp))
      have hresidualValid : LayerValid source residual.entry := by
        rw [residualEq]
        exact htask.sub_newer hstoredValid newer factor
      rcases ih hresidualValid htable with ⟨dropped, hkeys, hzero, hvalid⟩
      refine ⟨dropped, ?_, hzero, hvalid⟩
      have htaskKey : key task.entry = key residual.entry := by
        rw [residualEq, key_withRow]
      simpa [htaskKey] using hkeys

theorem Drain.preservesLayerValid {p k d : Nat}
    {source : List (SourceVector p k d)}
    {queue : List (WorkItem p k d)} {before after : List (TaggedPivot p k d)}
    {visits pops : Nat} (drain : Drain queue before after visits pops)
    (htable : TableLayerValid source before)
    (hqueue : QueueLayerValid source queue) :
    TableLayerValid source after := by
  induction drain with
  | done table => exact htable
  | @stop task rest before middle after visits tailVisits tailPops scan tail ih =>
      have htask : LayerValid source task.entry := hqueue task (by simp)
      have hrest : QueueLayerValid source rest := by
        intro item hitem
        exact hqueue item (by simp [hitem])
      have hscan := scan.preservesLayerValid htask htable
      exact ih hscan.1 hrest
  | @requeue task rest before middle after replacement next
      visits tailVisits tailPops scan queueOrder tail ih =>
      have htask : LayerValid source task.entry := hqueue task (by simp)
      have hrest : QueueLayerValid source rest := by
        intro item hitem
        exact hqueue item (by simp [hitem])
      have hscan := scan.preservesLayerValid htask htable
      have hreplacement : LayerValid source replacement.entry := hscan.2 replacement rfl
      have hnext : QueueLayerValid source next := by
        intro item hitem
        have hmem := queueOrder.mem_iff.mp hitem
        rcases List.mem_cons.mp hmem with rfl | hrestMem
        · exact hreplacement
        · exact hrest item hrestMem
      exact ih hscan.1 hnext

theorem Drain.preservesOrdered {p k d : Nat}
    {queue : List (WorkItem p k d)} {before after : List (TaggedPivot p k d)}
    {visits pops : Nat} (drain : Drain queue before after visits pops)
    (hbefore : Ordered (before.map TaggedPivot.pivot)) :
    Ordered (after.map TaggedPivot.pivot) := by
  induction drain with
  | done table => exact hbefore
  | stop scan tail ih => exact ih (scan.preservesOrdered hbefore)
  | requeue scan queueOrder tail ih => exact ih (scan.preservesOrdered hbefore)

end CompositeModulusBasis.VerifiedScan
