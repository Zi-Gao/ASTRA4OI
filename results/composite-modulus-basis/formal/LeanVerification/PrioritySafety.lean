import LeanVerification.FastAppend
import Mathlib.Tactic

/-!
# Safety of descending-timestamp priority

When a maximal-timestamp task is popped, no newer key remains in the queue.
The newer portion of the stored table therefore satisfies the terminal
extraction theorem and is a complete basis.  Distinct layers of the current
timestamp cannot collide in one slot by the intrinsic quotient-lead theorem.
-/

namespace CompositeModulusBasis.PrioritySafety

open BasisQuery CyclicExtension FastAppend FastInvariant PadicEchelon
  TerminalExtraction TimestampedBasis TimestampLayerInvariant
  VerifiedScan WorklistRefinement

def sourceAfter {p k d : Nat} (timestamp : Nat)
    (source : List (SourceVector p k d)) : List (SourceVector p k d) :=
  source.filter fun item => timestamp < item.timestamp

def tableAfter {p k d : Nat} (timestamp : Nat)
    (table : List (TaggedPivot p k d)) : List (TaggedPivot p k d) :=
  table.filter fun entry => timestamp < entry.timestamp

@[simp] theorem mem_sourceAfter {p k d : Nat} (timestamp : Nat)
    {source : List (SourceVector p k d)} {item : SourceVector p k d} :
    item ∈ sourceAfter timestamp source ↔ item ∈ source ∧ timestamp < item.timestamp := by
  simp [sourceAfter]

@[simp] theorem mem_tableAfter {p k d : Nat} (timestamp : Nat)
    {table : List (TaggedPivot p k d)} {entry : TaggedPivot p k d} :
    entry ∈ tableAfter timestamp table ↔ entry ∈ table ∧ timestamp < entry.timestamp := by
  simp [tableAfter]

theorem sourceAfter_strict {p k d : Nat} (timestamp : Nat)
    {source : List (SourceVector p k d)} (hstrict : SourceStrict source) :
    SourceStrict (sourceAfter timestamp source) := by
  have hsub : List.Sublist (sourceAfter timestamp source) source := List.filter_sublist
  exact hstrict.sublist hsub

theorem tableAfter_ordered {p k d : Nat} (timestamp : Nat)
    {table : List (TaggedPivot p k d)}
    (hordered : Ordered (table.map TaggedPivot.pivot)) :
    Ordered ((tableAfter timestamp table).map TaggedPivot.pivot) := by
  have hsub : List.Sublist ((tableAfter timestamp table).map TaggedPivot.pivot)
      (table.map TaggedPivot.pivot) := List.Sublist.map _ List.filter_sublist
  exact hordered.sublist hsub

theorem tableAfter_keys {p k d : Nat} (timestamp : Nat)
    {table : List (TaggedPivot p k d)} (hkeys : KeysNodup table) :
    KeysNodup (tableAfter timestamp table) := by
  have hsub : List.Sublist ((tableAfter timestamp table).map pivotKey)
      (table.map pivotKey) := List.Sublist.map _ List.filter_sublist
  exact hkeys.sublist hsub

theorem sourceSet_after_eq {p k d : Nat} (timestamp : Nat)
    (source : List (SourceVector p k d)) (left : Nat)
    (hleft : timestamp < left) :
    sourceSet (sourceAfter timestamp source) left = sourceSet source left := by
  ext row
  simp only [sourceSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨item, hitem, htime, rfl⟩
    exact ⟨item, (mem_sourceAfter timestamp).1 hitem |>.1, htime, rfl⟩
  · rintro ⟨item, hitem, htime, rfl⟩
    refine ⟨item, (mem_sourceAfter timestamp).2 ⟨hitem, ?_⟩, htime, rfl⟩
    omega

theorem newerSubmodule_after_eq {p k d : Nat} (timestamp : Nat)
    (source : List (SourceVector p k d))
    {item : SourceVector p k d} (htime : timestamp < item.timestamp) :
    newerSubmodule (sourceAfter timestamp source) item.timestamp =
      newerSubmodule source item.timestamp := by
  unfold newerSubmodule sourceSubmodule
  rw [sourceSet_after_eq]
  omega

theorem sourceAfter_full_eq_newer {p k d : Nat} (timestamp : Nat)
    (source : List (SourceVector p k d)) :
    sourceSubmodule (sourceAfter timestamp source) 0 =
      newerSubmodule source timestamp := by
  unfold sourceSubmodule newerSubmodule
  congr 1
  ext row
  simp only [sourceSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨item, hitem, hzero, rfl⟩
    have hafter := (mem_sourceAfter timestamp).1 hitem
    exact ⟨item, hafter.1, by omega, rfl⟩
  · rintro ⟨item, hitem, htime, rfl⟩
    exact ⟨item, (mem_sourceAfter timestamp).2 ⟨hitem, by omega⟩, Nat.zero_le _, rfl⟩

theorem tableAfter_valid {p k d : Nat} (timestamp : Nat)
    {source : List (SourceVector p k d)} {table : List (TaggedPivot p k d)}
    (hvalid : TableLayerValid source table) :
    TableLayerValid (sourceAfter timestamp source) (tableAfter timestamp table) := by
  intro entry hentry
  have hfull := (mem_tableAfter timestamp).1 hentry
  rcases hvalid entry hfull.1 with
    ⟨item, hitem, hentryTime, hlayer, hrepresentative⟩
  simp only [TaggedPivot.asVector_timestamp, TaggedPivot.asVector_layer,
    TaggedPivot.asVector_row] at hentryTime hlayer hrepresentative ⊢
  have hitemAfter : item ∈ sourceAfter timestamp source := by
    apply (mem_sourceAfter timestamp).2
    refine ⟨hitem, ?_⟩
    rw [← hentryTime]
    exact hfull.2
  refine ⟨item, hitemAfter, hentryTime, hlayer, ?_⟩
  have hsubmodule := newerSubmodule_after_eq timestamp source
    (show timestamp < item.timestamp by rw [← hentryTime]; exact hfull.2)
  simp only [TaggedPivot.asVector_timestamp, TaggedPivot.asVector_layer,
    TaggedPivot.asVector_row]
  rw [hentryTime, hsubmodule]
  rw [hentryTime] at hrepresentative
  exact hrepresentative

theorem quotientExponent_after {p k d : Nat} (hp : p.Prime)
    (timestamp : Nat) (source : List (SourceVector p k d))
    {item : SourceVector p k d} (htime : timestamp < item.timestamp) :
    quotientExponent hp (sourceAfter timestamp source) item =
      quotientExponent hp source item := by
  have hsubmodule := newerSubmodule_after_eq timestamp source htime
  have hleft := quotientExponent_order hp (sourceAfter timestamp source) item
  have hright := quotientExponent_order hp source item
  rw [hsubmodule] at hleft
  exact Nat.pow_right_injective hp.two_le (hleft.symm.trans hright)

def NoNewerPending {p k d : Nat} (timestamp : Nat)
    (queue : List (WorkItem p k d)) : Prop :=
  ∀ task ∈ queue, task.entry.timestamp ≤ timestamp

theorem tableAfter_complete {p k d : Nat} (hp : p.Prime)
    (timestamp : Nat)
    {source : List (SourceVector p k d)}
    {table : List (TaggedPivot p k d)} {queue : List (WorkItem p k d)}
    (hprotected : ProtectedActive hp source table queue)
    (hnone : NoNewerPending timestamp queue) :
    ProtectedComplete hp (sourceAfter timestamp source) (tableAfter timestamp table) := by
  intro item hitem e he
  have hitemFull := (mem_sourceAfter timestamp).1 hitem
  have heFull : e < quotientExponent hp source item := by
    rwa [← quotientExponent_after hp timestamp source hitemFull.2]
  have hactive := hprotected item hitemFull.1 e heFull
  rw [activeKeys, List.mem_append] at hactive
  rcases hactive with htable | hqueue
  · rcases List.mem_map.mp htable with ⟨entry, hentry, hkey⟩
    have htime : entry.timestamp = item.timestamp := congrArg Prod.fst hkey
    have hlayer : entry.layer = e := congrArg Prod.snd hkey
    refine ⟨entry, (mem_tableAfter timestamp).2 ⟨hentry, ?_⟩, htime, hlayer⟩
    rw [htime]
    exact hitemFull.2
  · rcases List.mem_map.mp hqueue with ⟨task, htask, hkey⟩
    have htime : task.entry.timestamp = item.timestamp := congrArg Prod.fst hkey
    have hle := hnone task htask
    rw [htime] at hle
    omega

/-- With no newer pending task, the strictly newer stored rows form a complete
cardinal basis. -/
theorem newer_table_correct {p k d : Nat} (hp : p.Prime)
    (timestamp : Nat)
    {source : List (SourceVector p k d)}
    {table : List (TaggedPivot p k d)} {queue : List (WorkItem p k d)}
    (hstrict : SourceStrict source)
    (hordered : Ordered (table.map TaggedPivot.pivot))
    (hkeys : KeysNodup table)
    (hvalid : TableLayerValid source table)
    (hprotected : ProtectedActive hp source table queue)
    (hnone : NoNewerPending timestamp queue) :
    CorrectTable (sourceAfter timestamp source) (tableAfter timestamp table) :=
  drained_table_correct hp (sourceAfter_strict timestamp hstrict)
    (tableAfter_ordered timestamp hordered) (tableAfter_keys timestamp hkeys)
    (tableAfter_valid timestamp hvalid)
    (tableAfter_complete hp timestamp hprotected hnone)

/-- The missing error branch of `Scan`: under the maintained invariants a
maximal-timestamp task cannot meet a stored row with the same timestamp in its
leading slot. -/
theorem same_timestamp_collision_impossible {p k d : Nat} (hp : p.Prime)
    {source : List (SourceVector p k d)}
    {table : List (TaggedPivot p k d)} {queue : List (WorkItem p k d)}
    (hstrict : SourceStrict source)
    (hordered : Ordered (table.map TaggedPivot.pivot))
    (hkeys : ActiveKeysNodup table queue)
    (hvalid : TableLayerValid source table)
    (hqueueValid : QueueLayerValid source queue)
    (hprotected : ProtectedActive hp source table queue)
    {task : WorkItem p k d} (htaskMem : task ∈ queue)
    (hmaximal : NoNewerPending task.entry.timestamp queue)
    {old : TaggedPivot p k d} (holdMem : old ∈ table)
    (hsameTime : old.timestamp = task.entry.timestamp)
    {slot : Slot d k} (hlead : HasLead task.entry.row slot)
    (hcollision : old.pivot.slot = slot) : False := by
  have hnewerCorrect := newer_table_correct hp task.entry.timestamp
    hstrict hordered (by
      have hactive : (activeKeys table queue).Nodup := hkeys
      exact (List.nodup_append.1 hactive).1)
    hvalid hprotected hmaximal
  let newerBasis : Basis p k d := basisAt hnewerCorrect 0
  have hnewerSubmodule : newerBasis.submodule =
      newerSubmodule source task.entry.timestamp := by
    change sourceSubmodule (sourceAfter task.entry.timestamp source) 0 = _
    exact sourceAfter_full_eq_newer task.entry.timestamp source
  have hnewerPivots : newerBasis.pivots =
      (tableAfter task.entry.timestamp table).map TaggedPivot.pivot := by
    change pivotsAt (tableAfter task.entry.timestamp table) 0 = _
    exact pivotsAt_zero _
  have hinjective := SourceStrict.timestampInjective hstrict
  have htaskValid := hqueueValid task htaskMem
  rcases htaskValid with
    ⟨taskSource, htaskSource, htaskTime, htaskLayerBound, htaskRep⟩
  have holdValid := hvalid old holdMem
  rcases holdValid with
    ⟨oldSource, holdSource, holdTime, holdLayerBound, holdRep⟩
  simp only [TaggedPivot.asVector_timestamp, TaggedPivot.asVector_layer,
    TaggedPivot.asVector_row] at holdTime holdLayerBound holdRep
  have hsourceEq : oldSource = taskSource := by
    apply hinjective holdSource htaskSource
    rw [← holdTime, hsameTime, htaskTime]
  subst oldSource
  rw [← hnewerSubmodule] at htaskRep
  rw [hsameTime, ← hnewerSubmodule] at holdRep
  have hmissing : ∀ pivot ∈ newerBasis.pivots, pivot.slot ≠ slot := by
    intro pivot hpivot hpivotSlot
    rw [hnewerPivots] at hpivot
    rcases List.mem_map.mp hpivot with ⟨entry, hentry, rfl⟩
    have hentryFull := (mem_tableAfter task.entry.timestamp).1 hentry
    have heq := ordered_tagged_slot_injective hordered
      hentryFull.1 holdMem (hpivotSlot.trans hcollision.symm)
    have hlater := hentryFull.2
    rw [heq, hsameTime] at hlater
    exact (Nat.lt_irrefl _ hlater)
  have hlayersNe : task.entry.layer ≠ old.layer := by
    intro hlayer
    have hactive : (activeKeys table queue).Nodup := hkeys
    have hdisjoint := (List.nodup_append.1 hactive).2.2
    exact (hdisjoint (pivotKey old)
      (List.mem_map.mpr ⟨old, holdMem, rfl⟩)
      (key task.entry)
      (List.mem_map.mpr ⟨task, htaskMem, rfl⟩))
      (Prod.ext hsameTime hlayer.symm)
  have hslotsNe := no_same_slot_of_missing_layers newerBasis hp taskSource.row
    (by
      rw [hnewerSubmodule, htaskTime]
      exact quotientExponent_order hp source taskSource)
    hlayersNe htaskRep holdRep hlead
    (by simpa [hcollision] using PivotRow.hasLead hp.one_lt old.pivot)
    hmissing hmissing
  exact hslotsNe rfl

end CompositeModulusBasis.PrioritySafety
