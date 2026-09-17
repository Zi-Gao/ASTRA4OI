import LeanVerification.VerifiedScan
import Mathlib.Tactic

/-!
# Preservation of the strong fast-insertion invariant

The scan accounting theorem records every removed key together with the actual
zero row that was removed.  Therefore a quotient layer below its current
exponent can never disappear.  This proves preservation of unique active keys
and of all protected `(timestamp,layer)` keys through the complete heap drain.
-/

namespace CompositeModulusBasis.FastInvariant

open PadicEchelon TimestampedBasis TimestampLayerInvariant
  VerifiedScan WorklistRefinement

def queueKeys {p k d : Nat} (queue : List (WorkItem p k d)) :
    List (Nat × Nat) := queue.map (key ∘ WorkItem.entry)

def activeKeys {p k d : Nat} (table : List (TaggedPivot p k d))
    (queue : List (WorkItem p k d)) : List (Nat × Nat) :=
  tableKeys table ++ queueKeys queue

def ActiveKeysNodup {p k d : Nat} (table : List (TaggedPivot p k d))
    (queue : List (WorkItem p k d)) : Prop :=
  (activeKeys table queue).Nodup

def ProtectedActive {p k d : Nat} (hp : p.Prime)
    (source : List (SourceVector p k d))
    (table : List (TaggedPivot p k d)) (queue : List (WorkItem p k d)) : Prop :=
  ∀ item ∈ source, ∀ e < quotientExponent hp source item,
    (item.timestamp, e) ∈ activeKeys table queue

theorem optionKeys_eq_queueKeys {p k d : Nat}
    (replacement : Option (WorkItem p k d)) :
    optionKeys replacement = queueKeys replacement.toList := by
  cases replacement <;> rfl

private theorem accounting_with_tail {p k d : Nat}
    {task : WorkItem p k d} {before after : List (TaggedPivot p k d)}
    {replacement : Option (WorkItem p k d)}
    (rest : List (WorkItem p k d)) (dropped : List (TaggedVector p k d))
    (haccount : (tableKeys before ++ [key task.entry]).Perm
      (tableKeys after ++ optionKeys replacement ++ dropped.map key)) :
    (activeKeys before (task :: rest)).Perm
      (activeKeys after (replacement.toList ++ rest) ++ dropped.map key) := by
  have happend := haccount.append_right (queueKeys rest)
  have hrotate :
      ((tableKeys after ++ optionKeys replacement ++ dropped.map key) ++ queueKeys rest).Perm
      ((tableKeys after ++ optionKeys replacement ++ queueKeys rest) ++ dropped.map key) := by
    have hswap : (dropped.map key ++ queueKeys rest).Perm
        (queueKeys rest ++ dropped.map key) := List.perm_append_comm
    simpa [List.append_assoc] using
      List.Perm.append_left (tableKeys after ++ optionKeys replacement) hswap
  simpa [activeKeys, queueKeys, optionKeys_eq_queueKeys, List.append_assoc] using
    happend.trans hrotate

private theorem protected_not_dropped {p k d : Nat} (hp : p.Prime)
    {source : List (SourceVector p k d)} (hinjective : TimestampInjective source)
    {dropped : List (TaggedVector p k d)}
    (hzero : ∀ entry ∈ dropped, entry.row = 0)
    (hvalid : ∀ entry ∈ dropped, LayerValid source entry)
    {item : SourceVector p k d} (hitem : item ∈ source)
    {e : Nat} (he : e < quotientExponent hp source item) :
    (item.timestamp, e) ∉ dropped.map key := by
  intro hmem
  rcases List.mem_map.mp hmem with ⟨entry, hentry, hkey⟩
  have htimestamp : entry.timestamp = item.timestamp := by
    exact congrArg Prod.fst hkey
  have hlayer : entry.layer = e := by
    exact congrArg Prod.snd hkey
  exact (LayerValid.ne_zero_of_protected hp hinjective hitem htimestamp hlayer he
    (hvalid entry hentry)) (hzero entry hentry)

/-- One complete scan, with the untouched queue tail restored, preserves key
uniqueness and every protected layer. -/
theorem scan_preservesKeysAndProtected {p k d : Nat} (hp : p.Prime)
    {source : List (SourceVector p k d)} (hinjective : TimestampInjective source)
    {task : WorkItem p k d} {before after : List (TaggedPivot p k d)}
    {replacement : Option (WorkItem p k d)} {visits : Nat}
    (scan : Scan task before after replacement visits)
    (rest : List (WorkItem p k d))
    (htask : LayerValid source task.entry)
    (htable : TableLayerValid source before)
    (hkeys : ActiveKeysNodup before (task :: rest))
    (hprotected : ProtectedActive hp source before (task :: rest)) :
    ActiveKeysNodup after (replacement.toList ++ rest) ∧
      ProtectedActive hp source after (replacement.toList ++ rest) := by
  rcases scan.accounting htask htable with ⟨dropped, haccount, hzero, hvalid⟩
  have hperm := accounting_with_tail rest dropped haccount
  constructor
  · have hcombined :
        (activeKeys after (replacement.toList ++ rest) ++ dropped.map key).Nodup :=
      hperm.nodup_iff.mp hkeys
    exact hcombined.of_append_left
  · intro item hitem e he
    have hin := hprotected item hitem e he
    have hout := hperm.mem_iff.mp hin
    rw [List.mem_append] at hout
    rcases hout with hout | hdropped
    · exact hout
    · exact False.elim ((protected_not_dropped hp hinjective hzero hvalid hitem he) hdropped)

theorem queuePerm_preserves {p k d : Nat} (hp : p.Prime)
    {source : List (SourceVector p k d)}
    (table : List (TaggedPivot p k d))
    {before after : List (WorkItem p k d)} (hperm : before.Perm after)
    (hvalid : QueueLayerValid source before)
    (hkeys : ActiveKeysNodup table before)
    (hprotected : ProtectedActive hp source table before) :
    QueueLayerValid source after ∧ ActiveKeysNodup table after ∧
      ProtectedActive hp source table after := by
  have hqueueKeys : (queueKeys before).Perm (queueKeys after) :=
    hperm.map (key ∘ WorkItem.entry)
  have hactiveKeys : (activeKeys table before).Perm (activeKeys table after) :=
    List.Perm.append_left (tableKeys table) hqueueKeys
  refine ⟨?_, hactiveKeys.nodup_iff.mp hkeys, ?_⟩
  · intro item hitem
    exact hvalid item (hperm.mem_iff.mpr hitem)
  · intro item hitem e he
    exact hactiveKeys.mem_iff.mp (hprotected item hitem e he)

/-- The complete priority drain preserves all algebraic invariants needed by
`drained_table_correct`. -/
theorem drain_preservesStrongInvariant {p k d : Nat} (hp : p.Prime)
    {source : List (SourceVector p k d)} (hinjective : TimestampInjective source)
    {queue : List (WorkItem p k d)} {before after : List (TaggedPivot p k d)}
    {visits pops : Nat} (drain : Drain queue before after visits pops)
    (htable : TableLayerValid source before)
    (hqueue : QueueLayerValid source queue)
    (hkeys : ActiveKeysNodup before queue)
    (hprotected : ProtectedActive hp source before queue) :
    TableLayerValid source after ∧ KeysNodup after ∧
      ProtectedComplete hp source after := by
  induction drain with
  | done table =>
      refine ⟨htable, ?_, ?_⟩
      · simpa [ActiveKeysNodup, activeKeys, queueKeys, KeysNodup, tableKeys] using hkeys
      · intro item hitem e he
        have hmem := hprotected item hitem e he
        simp only [activeKeys, queueKeys, List.map_nil, List.append_nil] at hmem
        rcases List.mem_map.mp hmem with ⟨entry, hentry, hkey⟩
        refine ⟨entry, hentry, ?_, ?_⟩
        · exact congrArg Prod.fst hkey
        · exact congrArg Prod.snd hkey
  | @stop task rest before middle after visits tailVisits tailPops scan tail ih =>
      have htask : LayerValid source task.entry := hqueue task (by simp)
      have hrest : QueueLayerValid source rest := by
        intro item hitem
        exact hqueue item (by simp [hitem])
      have hscanValid := scan.preservesLayerValid htask htable
      have hscanKeys := scan_preservesKeysAndProtected hp hinjective scan rest
        htask htable hkeys hprotected
      have hmiddleKeys : ActiveKeysNodup middle rest := by
        simpa using hscanKeys.1
      have hmiddleProtected : ProtectedActive hp source middle rest := by
        simpa using hscanKeys.2
      exact ih hscanValid.1 hrest hmiddleKeys hmiddleProtected
  | @requeue task rest before middle after replacement next
      visits tailVisits tailPops scan queueOrder tail ih =>
      have htask : LayerValid source task.entry := hqueue task (by simp)
      have hrest : QueueLayerValid source rest := by
        intro item hitem
        exact hqueue item (by simp [hitem])
      have hscanValid := scan.preservesLayerValid htask htable
      have hreplacement : LayerValid source replacement.entry :=
        hscanValid.2 replacement rfl
      have hscanQueue : QueueLayerValid source ([replacement] ++ rest) := by
        intro item hitem
        rcases List.mem_cons.mp hitem with rfl | hrestMem
        · exact hreplacement
        · exact hrest item hrestMem
      have hscanKeys := scan_preservesKeysAndProtected hp hinjective scan rest
        htask htable hkeys hprotected
      have hpermuted := queuePerm_preserves hp middle queueOrder.symm
        hscanQueue hscanKeys.1 hscanKeys.2
      exact ih hscanValid.1 hpermuted.1 hpermuted.2.1 hpermuted.2.2

end CompositeModulusBasis.FastInvariant
