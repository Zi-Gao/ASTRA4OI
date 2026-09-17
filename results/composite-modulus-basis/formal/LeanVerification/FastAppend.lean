import LeanVerification.FastInvariant
import Mathlib.Tactic

/-!
# End-to-end verified timestamped append

`FastTable` is the inductive state maintained across prefix appends.  The new
source contributes exactly `k` non-branching power tasks.  Any concrete
`VerifiedScan.Drain` of those tasks produces another `FastTable`, hence a
complete basis for every interval ending at the new prefix, while inheriting
the `O(k d²)` cell-operation bound.
-/

namespace CompositeModulusBasis.FastAppend

open FastInvariant PadicEchelon SettledTimestamp TerminalExtraction
  TimestampedBasis TimestampLayerInvariant VerifiedScan WorklistRefinement

structure FastTable {p k d : Nat} (hp : p.Prime)
    (source : List (SourceVector p k d)) where
  entries : List (TaggedPivot p k d)
  strict : SourceStrict source
  ordered : Ordered (entries.map TaggedPivot.pivot)
  keys : KeysNodup entries
  valid : TableLayerValid source entries
  complete : ProtectedComplete hp source entries

theorem FastTable.correct {p k d : Nat} {hp : p.Prime}
    {source : List (SourceVector p k d)} (table : FastTable hp source) :
    CorrectTable source table.entries :=
  drained_table_correct hp table.strict table.ordered table.keys table.valid table.complete

noncomputable def emptyFastTable {p k d : Nat} (hp : p.Prime) :
    FastTable hp ([] : List (SourceVector p k d)) where
  entries := []
  strict := by simp [SourceStrict]
  ordered := by simp [Ordered]
  keys := by simp [KeysNodup]
  valid := by simp [TableLayerValid]
  complete := by simp [ProtectedComplete]

def powerEntry {p k d : Nat} (item : SourceVector p k d)
    (index : Fin k) : TaggedVector p k d :=
  { timestamp := item.timestamp
    layer := index
    row := (((p ^ (index : Nat) : Nat) : Ring p k) • item.row) }

theorem powerEntry_valid {p k d : Nat}
    (source : List (SourceVector p k d)) (item : SourceVector p k d)
    (hitem : item ∈ source) (index : Fin k) :
    LayerValid source (powerEntry item index) := by
  refine ⟨item, hitem, rfl, index.isLt, ?_⟩
  refine ⟨1, ?_⟩
  simp [powerEntry]

theorem initialQueue_valid {p k d : Nat}
    (source : List (SourceVector p k d)) (item : SourceVector p k d)
    (hitem : item ∈ source) :
    QueueLayerValid source (initialQueue (powerEntry item)) := by
  intro work hwork
  rw [initialQueue, List.mem_ofFn'] at hwork
  rcases hwork with ⟨index, rfl⟩
  exact powerEntry_valid source item hitem index

theorem sourceStrict_append {p k d : Nat}
    {source : List (SourceVector p k d)} (hstrict : SourceStrict source)
    (item : SourceVector p k d)
    (hlatest : ∀ old ∈ source, old.timestamp < item.timestamp) :
    SourceStrict (source ++ [item]) := by
  rw [SourceStrict, List.pairwise_append]
  refine ⟨hstrict, by simp, ?_⟩
  intro old hold new hnew
  simp only [List.mem_singleton] at hnew
  subst new
  exact hlatest old hold

theorem tableValid_append_source {p k d : Nat}
    {source : List (SourceVector p k d)} {entries : List (TaggedPivot p k d)}
    (hvalid : TableLayerValid source entries) (item : SourceVector p k d) :
    TableLayerValid (source ++ [item]) entries := by
  intro entry hentry
  exact (hvalid entry hentry).mono_source (by intro old hold; simp [hold])

private theorem initial_queue_keys {p k d : Nat} (item : SourceVector p k d) :
    queueKeys (initialQueue (powerEntry item)) =
      List.ofFn (fun index : Fin k => (item.timestamp, (index : Nat))) := by
  simp [queueKeys, initialQueue, powerEntry, key, List.map_ofFn, Function.comp_def]

private theorem initial_queue_keys_nodup {p k d : Nat} (item : SourceVector p k d) :
    (queueKeys (initialQueue (powerEntry item))).Nodup := by
  rw [initial_queue_keys, List.nodup_ofFn]
  intro left right heq
  apply Fin.ext
  exact congrArg Prod.snd heq

theorem initial_active_keys_nodup {p k d : Nat} {hp : p.Prime}
    {source : List (SourceVector p k d)} (table : FastTable hp source)
    (item : SourceVector p k d)
    (hlatest : ∀ old ∈ source, old.timestamp < item.timestamp) :
    ActiveKeysNodup table.entries (initialQueue (powerEntry item)) := by
  rw [ActiveKeysNodup, activeKeys]
  apply List.Nodup.append table.keys (initial_queue_keys_nodup item)
  rw [List.disjoint_left]
  intro value htable hqueue
  rcases List.mem_map.mp htable with ⟨entry, hentry, rfl⟩
  rw [initial_queue_keys, List.mem_ofFn'] at hqueue
  rcases hqueue with ⟨index, hkey⟩
  have hvalid := table.valid entry hentry
  rcases hvalid with ⟨sourceItem, hsourceItem, htime, hlayer, hrep⟩
  have htimestamp := congrArg Prod.fst hkey
  simp only [pivotKey] at htimestamp
  have := hlatest sourceItem hsourceItem
  simp only [TaggedPivot.asVector_timestamp] at htime
  omega

theorem initial_protected {p k d : Nat} (hp : p.Prime)
    {source : List (SourceVector p k d)} (table : FastTable hp source)
    (item : SourceVector p k d) :
    ProtectedActive hp (source ++ [item]) table.entries
      (initialQueue (powerEntry item)) := by
  intro represented hrepresented e he
  rw [List.mem_append] at hrepresented
  rcases hrepresented with hold | hnew
  · have hexponent : quotientExponent hp (source ++ [item]) represented ≤
        quotientExponent hp source represented :=
      quotientExponent_anti_source hp (by intro old hold; simp [hold]) represented
    rcases table.complete represented hold e (lt_of_lt_of_le he hexponent) with
      ⟨entry, hentry, htime, hlayer⟩
    rw [activeKeys, List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨entry, hentry, by simp [pivotKey, htime, hlayer]⟩)
  · simp only [List.mem_singleton] at hnew
    subst represented
    have heK : e < k := lt_of_lt_of_le he (quotientExponent_le hp (source ++ [item]) item)
    let index : Fin k := ⟨e, heK⟩
    rw [activeKeys, List.mem_append]
    right
    rw [initial_queue_keys, List.mem_ofFn']
    exact ⟨index, by simp [index]⟩

/-- One complete fast append: correctness for every left endpoint and all main
operation bounds are obtained together. -/
theorem append_correct_and_bounded {p k d : Nat} (hp : p.Prime)
    {source : List (SourceVector p k d)} (table : FastTable hp source)
    (item : SourceVector p k d)
    (hlatest : ∀ old ∈ source, old.timestamp < item.timestamp)
    {after : List (TaggedPivot p k d)} {visits pops : Nat}
    (drain : Drain (initialQueue (powerEntry item)) table.entries after visits pops) :
    ∃ result : FastTable hp (source ++ [item]),
      result.entries = after ∧
      CorrectTable (source ++ [item]) after ∧
      visits ≤ k * d ∧ pops ≤ k * (d + 1) ∧
      drain.valuations ≤ k * d ∧ drain.normalizations ≤ k * d ∧
      drain.vectorPasses ≤ 2 * (k * d) ∧
      drain.vectorPasses * d ≤ 2 * k * d * d := by
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
  have hstrong := drain_preservesStrongInvariant hp
    (SourceStrict.timestampInjective hstrict) drain htable hqueue hkeys hprotected
  have hordered := drain.preservesOrdered table.ordered
  let result : FastTable hp fullSource := {
    entries := after
    strict := hstrict
    ordered := hordered
    keys := hstrong.2.1
    valid := hstrong.1
    complete := hstrong.2.2
  }
  have hcorrect : CorrectTable fullSource after := result.correct
  rcases drain.initial_bounds (powerEntry item) with ⟨hvisits, hpops, hscanCells⟩
  rcases drain.initial_operational_bounds (powerEntry item) with
    ⟨hvaluations, hnormalizations, hcells⟩
  have hpasses : drain.vectorPasses ≤ 2 * (k * d) :=
    drain.vectorPasses_le_twice_visits.trans (Nat.mul_le_mul_left 2 hvisits)
  exact ⟨result, rfl, hcorrect, hvisits, hpops, hvaluations,
    hnormalizations, hpasses, hcells⟩

end CompositeModulusBasis.FastAppend
