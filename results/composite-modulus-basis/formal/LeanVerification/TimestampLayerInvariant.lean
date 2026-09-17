import LeanVerification.WorklistRefinement
import Mathlib.Tactic

/-!
# Layer identities preserved by timestamped row operations

Every active row remembers `(timestamp, layer)`.  Its vector is a unit multiple
of that source's `p^layer` modulo all strictly newer sources.  This invariant is
preserved by unit normalization, reduction by a newer pivot, and source-list
extension.
-/

namespace CompositeModulusBasis.TimestampLayerInvariant

open CyclicExtension CyclicQuotient PadicEchelon TimestampedBasis

def newerSubmodule {p k d : Nat} (source : List (SourceVector p k d))
    (timestamp : Nat) : Submodule (Ring p k) (Vector p k d) :=
  sourceSubmodule source (timestamp + 1)

def LayerValid {p k d : Nat} (source : List (SourceVector p k d))
    (entry : TaggedVector p k d) : Prop :=
  ∃ item ∈ source,
    entry.timestamp = item.timestamp ∧ entry.layer < k ∧
      LayerRepresentative (newerSubmodule source entry.timestamp)
        item.row entry.layer entry.row

def TimestampInjective {p k d : Nat} (source : List (SourceVector p k d)) : Prop :=
  ∀ ⦃left right : SourceVector p k d⦄,
    left ∈ source → right ∈ source →
      left.timestamp = right.timestamp → left = right

def key {p k d : Nat} (entry : TaggedVector p k d) : Nat × Nat :=
  (entry.timestamp, entry.layer)

def pivotKey {p k d : Nat} (entry : TaggedPivot p k d) : Nat × Nat :=
  (entry.timestamp, entry.layer)

@[simp] theorem key_withRow {p k d : Nat} (entry : TaggedVector p k d)
    (row : Vector p k d) : key (entry.withRow row) = key entry := rfl

@[simp] theorem key_asVector {p k d : Nat} (entry : TaggedPivot p k d) :
    key entry.asVector = pivotKey entry := rfl

def TableLayerValid {p k d : Nat} (source : List (SourceVector p k d))
    (entries : List (TaggedPivot p k d)) : Prop :=
  ∀ entry ∈ entries, LayerValid source entry.asVector

def KeysNodup {p k d : Nat} (entries : List (TaggedPivot p k d)) : Prop :=
  (entries.map pivotKey).Nodup

def SourceStrict {p k d : Nat} (source : List (SourceVector p k d)) : Prop :=
  source.Pairwise fun earlier later => earlier.timestamp < later.timestamp

theorem LayerValid.unit_smul {p k d : Nat}
    {source : List (SourceVector p k d)} {entry : TaggedVector p k d}
    (unit : (Ring p k)ˣ) (hvalid : LayerValid source entry) :
    LayerValid source
      (entry.withRow ((unit : Ring p k) • entry.row)) := by
  rcases hvalid with ⟨item, hitem, htime, hlayer, hrepresentative⟩
  exact ⟨item, hitem, htime, hlayer,
    hrepresentative.unit_smul unit⟩

/-- A row belonging to a later timestamp lies in every older row's newer
suffix submodule. -/
theorem LayerValid.row_mem_newer {p k d : Nat}
    {source : List (SourceVector p k d)} {entry : TaggedVector p k d}
    (hvalid : LayerValid source entry) {oldTimestamp : Nat}
    (htime : oldTimestamp < entry.timestamp) :
    entry.row ∈ newerSubmodule source oldTimestamp := by
  rcases hvalid with ⟨item, hitem, hentryTime, hlayer, unit, hdifference⟩
  have hmono : newerSubmodule source entry.timestamp ≤
      newerSubmodule source oldTimestamp := by
    apply sourceSubmodule_antitone source
    omega
  have hdifference' := hmono hdifference
  have hitemRow : item.row ∈ newerSubmodule source oldTimestamp := by
    apply Submodule.subset_span
    exact ⟨item, hitem, by omega, rfl⟩
  have hlayerRow : (((p ^ entry.layer : Nat) : Ring p k) • item.row) ∈
      newerSubmodule source oldTimestamp :=
    (newerSubmodule source oldTimestamp).smul_mem _ hitemRow
  have hscaled := (newerSubmodule source oldTimestamp).smul_mem
    (unit : Ring p k) hlayerRow
  have hsum := (newerSubmodule source oldTimestamp).add_mem hdifference' hscaled
  simpa only [sub_add_cancel] using hsum

theorem LayerValid.sub_newer {p k d : Nat}
    {source : List (SourceVector p k d)}
    {task pivot : TaggedVector p k d}
    (htask : LayerValid source task) (hpivot : LayerValid source pivot)
    (htime : task.timestamp < pivot.timestamp) (factor : Ring p k) :
    LayerValid source (task.withRow (task.row - factor • pivot.row)) := by
  rcases htask with ⟨item, hitem, htimestamp, hlayer, hrepresentative⟩
  refine ⟨item, hitem, htimestamp, hlayer, ?_⟩
  exact hrepresentative.sub_mem
    ((newerSubmodule source task.timestamp).smul_mem factor
      (hpivot.row_mem_newer htime))

theorem LayerValid.mono_source {p k d : Nat}
    {small large : List (SourceVector p k d)}
    (hsource : ∀ item ∈ small, item ∈ large)
    {entry : TaggedVector p k d} (hvalid : LayerValid small entry) :
    LayerValid large entry := by
  rcases hvalid with ⟨item, hitem, htime, hlayer, hrepresentative⟩
  refine ⟨item, hsource item hitem, htime, hlayer, ?_⟩
  exact hrepresentative.mono
    (sourceSubmodule_mono_source hsource (entry.timestamp + 1))

noncomputable def quotientExponent {p k d : Nat} (hp : p.Prime)
    (source : List (SourceVector p k d)) (item : SourceVector p k d) : Nat :=
  Classical.choose
    (exists_quotient_order_exponent hp (newerSubmodule source item.timestamp) item.row)

theorem quotientExponent_le {p k d : Nat} (hp : p.Prime)
    (source : List (SourceVector p k d)) (item : SourceVector p k d) :
    quotientExponent hp source item ≤ k :=
  (Classical.choose_spec
    (exists_quotient_order_exponent hp (newerSubmodule source item.timestamp) item.row)).1

theorem quotientExponent_order {p k d : Nat} (hp : p.Prime)
    (source : List (SourceVector p k d)) (item : SourceVector p k d) :
    addOrderOf ((newerSubmodule source item.timestamp).mkQ item.row) =
      p ^ quotientExponent hp source item :=
  (Classical.choose_spec
    (exists_quotient_order_exponent hp (newerSubmodule source item.timestamp) item.row)).2

def ProtectedComplete {p k d : Nat} (hp : p.Prime)
    (source : List (SourceVector p k d))
    (entries : List (TaggedPivot p k d)) : Prop :=
  ∀ item ∈ source, ∀ e < quotientExponent hp source item,
    ∃ entry ∈ entries, entry.timestamp = item.timestamp ∧ entry.layer = e

theorem newerSubmodule_tail {p k d : Nat}
    (head : SourceVector p k d) (tail : List (SourceVector p k d))
    (headOlder : ∀ item ∈ tail, head.timestamp < item.timestamp)
    {item : SourceVector p k d} (hitem : item ∈ tail) :
    newerSubmodule (head :: tail) item.timestamp =
      newerSubmodule tail item.timestamp := by
  unfold newerSubmodule sourceSubmodule
  rw [sourceSet_cons_of_not_le]
  have := headOlder item hitem
  omega

theorem newerSubmodule_head {p k d : Nat}
    (head : SourceVector p k d) (tail : List (SourceVector p k d))
    (headOlder : ∀ item ∈ tail, head.timestamp < item.timestamp) :
    newerSubmodule (head :: tail) head.timestamp = sourceSubmodule tail 0 := by
  unfold newerSubmodule sourceSubmodule
  rw [sourceSet_cons_of_not_le]
  · rw [sourceSet_eq_zero_of_all]
    intro item hitem
    have := headOlder item hitem
    omega
  · omega

theorem quotientExponent_tail {p k d : Nat} (hp : p.Prime)
    (head : SourceVector p k d) (tail : List (SourceVector p k d))
    (headOlder : ∀ item ∈ tail, head.timestamp < item.timestamp)
    {item : SourceVector p k d} (hitem : item ∈ tail) :
    quotientExponent hp (head :: tail) item = quotientExponent hp tail item := by
  have hsubmodule := newerSubmodule_tail head tail headOlder hitem
  have hleft := quotientExponent_order hp (head :: tail) item
  have hright := quotientExponent_order hp tail item
  rw [hsubmodule] at hleft
  exact Nat.pow_right_injective hp.two_le (hleft.symm.trans hright)

theorem quotientExponent_anti_source {p k d : Nat} (hp : p.Prime)
    {small large : List (SourceVector p k d)}
    (hsource : ∀ source ∈ small, source ∈ large)
    (item : SourceVector p k d) :
    quotientExponent hp large item ≤ quotientExponent hp small item := by
  apply quotient_exponent_anti hp
    (newerSubmodule small item.timestamp)
    (newerSubmodule large item.timestamp)
    (sourceSubmodule_mono_source hsource (item.timestamp + 1)) item.row
    (quotientExponent_order hp small item)
    (quotientExponent_order hp large item)

/-- A protected layer below the current quotient exponent can never be dropped
as a zero residual. -/
theorem LayerValid.ne_zero_of_protected {p k d : Nat} (hp : p.Prime)
    {source : List (SourceVector p k d)} (hinjective : TimestampInjective source)
    {item : SourceVector p k d} (hitem : item ∈ source)
    {entry : TaggedVector p k d}
    (htimestamp : entry.timestamp = item.timestamp)
    {e : Nat} (hlayer : entry.layer = e)
    (he : e < quotientExponent hp source item)
    (hvalid : LayerValid source entry) : entry.row ≠ 0 := by
  rcases hvalid with
    ⟨represented, hrepresented, hrepresentedTime, hlayerBound, hrepresentative⟩
  have hsourceEq : represented = item := by
    apply hinjective hrepresented hitem
    rw [← hrepresentedTime, htimestamp]
  subst represented
  subst e
  have hsubmodule : newerSubmodule source entry.timestamp =
      newerSubmodule source item.timestamp := by rw [htimestamp]
  rw [hsubmodule] at hrepresentative
  exact hrepresentative.ne_zero_of_lt hp
    (quotientExponent_order hp source item) he

end CompositeModulusBasis.TimestampLayerInvariant
