import LeanVerification.ArbitraryExtension
import LeanVerification.TimestampedBasis
import Mathlib.Tactic

/-!
# Timestamp chains assembled from settled cyclic layers

For each source timestamp, the priority queue eventually leaves exactly the
nonzero quotient layers in slots missing from the already-settled newer suffix.
This file turns those terminal certificates into one table that is correct for
all timestamp thresholds simultaneously.
-/

namespace CompositeModulusBasis.SettledTimestamp

open ArbitraryExtension BasisQuery CyclicExtension DigitCardinality
  OrderedInsertion PadicEchelon TimestampedBasis

def insertTagged {p k d : Nat} (entry : TaggedPivot p k d) :
    List (TaggedPivot p k d) → List (TaggedPivot p k d)
  | [] => [entry]
  | current :: rest =>
      if Slot.lt entry.pivot.slot current.pivot.slot then entry :: current :: rest
      else current :: insertTagged entry rest

@[simp] theorem map_insertTagged {p k d : Nat} (entry : TaggedPivot p k d)
    (entries : List (TaggedPivot p k d)) :
    (insertTagged entry entries).map TaggedPivot.pivot =
      insertPivot entry.pivot (entries.map TaggedPivot.pivot) := by
  induction entries with
  | nil => simp [insertTagged, insertPivot]
  | cons current rest ih =>
      simp only [insertTagged, insertPivot, List.map_cons]
      split <;> simp [ih]

theorem perm_insertTagged {p k d : Nat} (entry : TaggedPivot p k d)
    (entries : List (TaggedPivot p k d)) :
    (insertTagged entry entries).Perm (entry :: entries) := by
  induction entries with
  | nil => simp [insertTagged]
  | cons current rest ih =>
      simp only [insertTagged]
      split_ifs
      · exact List.Perm.refl _
      · exact (ih.cons current).trans (List.Perm.swap current entry rest).symm

def insertAllTagged {p k d : Nat} :
    List (TaggedPivot p k d) → List (TaggedPivot p k d) →
      List (TaggedPivot p k d)
  | [], entries => entries
  | entry :: rest, entries => insertAllTagged rest (insertTagged entry entries)

@[simp] theorem map_insertAllTagged {p k d : Nat}
    (additions entries : List (TaggedPivot p k d)) :
    (insertAllTagged additions entries).map TaggedPivot.pivot =
      insertAll (additions.map TaggedPivot.pivot) (entries.map TaggedPivot.pivot) := by
  induction additions generalizing entries with
  | nil => simp [insertAllTagged, insertAll]
  | cons entry rest ih =>
      simp [insertAllTagged, insertAll, ih]

theorem perm_insertAllTagged {p k d : Nat}
    (additions entries : List (TaggedPivot p k d)) :
    (insertAllTagged additions entries).Perm (additions ++ entries) := by
  induction additions generalizing entries with
  | nil => simp [insertAllTagged]
  | cons entry rest ih =>
      rw [insertAllTagged]
      have hfirst := ih (insertTagged entry entries)
      have hsecond : (rest ++ insertTagged entry entries).Perm
          (rest ++ (entry :: entries)) :=
        List.Perm.append_left rest (perm_insertTagged entry entries)
      have hmiddle : (rest ++ (entry :: entries)).Perm
          (entry :: rest ++ entries) := by
        have hswap := (List.perm_append_comm (l₁ := rest) (l₂ := [entry])).append_right entries
        simp
      exact hfirst.trans (hsecond.trans hmiddle)

def taggedFamily {p k d h : Nat} (timestamp : Nat)
    (family : Fin h → PivotRow p k d) : List (TaggedPivot p k d) :=
  List.ofFn fun index =>
    { timestamp := timestamp, layer := index, pivot := family index }

@[simp] theorem map_taggedFamily {p k d h : Nat} (timestamp : Nat)
    (family : Fin h → PivotRow p k d) :
    (taggedFamily timestamp family).map TaggedPivot.pivot = familyPivots family := by
  simp [taggedFamily, familyPivots, List.map_ofFn, Function.comp_def]

@[simp] theorem taggedFamily_length {p k d h : Nat} (timestamp : Nat)
    (family : Fin h → PivotRow p k d) :
    (taggedFamily timestamp family).length = h := by
  simp [taggedFamily]

theorem taggedFamily_timestamp {p k d h : Nat} (timestamp : Nat)
    (family : Fin h → PivotRow p k d) {entry : TaggedPivot p k d}
    (hentry : entry ∈ taggedFamily timestamp family) :
    entry.timestamp = timestamp := by
  rw [taggedFamily, List.mem_ofFn'] at hentry
  rcases hentry with ⟨index, rfl⟩
  rfl

theorem pivotsAt_perm {p k d : Nat}
    {left : Nat} {a b : List (TaggedPivot p k d)} (h : a.Perm b) :
    (pivotsAt a left).Perm (pivotsAt b left) := by
  unfold pivotsAt
  exact (h.filter _).map _

@[simp] theorem pivotsAt_append {p k d : Nat}
    (a b : List (TaggedPivot p k d)) (left : Nat) :
    pivotsAt (a ++ b) left = pivotsAt a left ++ pivotsAt b left := by
  simp [pivotsAt]

theorem pivotsAt_taggedFamily_of_le {p k d h : Nat}
    (timestamp left : Nat) (family : Fin h → PivotRow p k d)
    (hle : left ≤ timestamp) :
    pivotsAt (taggedFamily timestamp family) left = familyPivots family := by
  rw [pivotsAt_eq_map_of_all, map_taggedFamily]
  intro entry hentry
  rw [taggedFamily_timestamp timestamp family hentry]
  exact hle

theorem pivotsAt_taggedFamily_of_not_le {p k d h : Nat}
    (timestamp left : Nat) (family : Fin h → PivotRow p k d)
    (hle : ¬left ≤ timestamp) :
    pivotsAt (taggedFamily timestamp family) left = [] := by
  unfold pivotsAt
  have hempty : (taggedFamily timestamp family).filter
      (fun entry => left ≤ entry.timestamp) = [] := by
    apply List.filter_eq_nil_iff.2
    intro entry hentry
    have htime := taggedFamily_timestamp timestamp family hentry
    simpa [htime] using hle
  rw [hempty]
  rfl

theorem span_rowsOf_eq_of_perm {p k d : Nat}
    {a b : List (PivotRow p k d)} (h : a.Perm b) :
    Submodule.span (Ring p k) {row | row ∈ rowsOf a} =
      Submodule.span (Ring p k) {row | row ∈ rowsOf b} := by
  congr 1
  ext row
  change row ∈ a.map PivotRow.row ↔ row ∈ b.map PivotRow.row
  exact (h.map PivotRow.row).mem_iff

structure SettledTable {p k d : Nat} (source : List (SourceVector p k d)) where
  entries : List (TaggedPivot p k d)
  correct : CorrectTable source entries
  timestamp_source : ∀ entry ∈ entries,
    ∃ item ∈ source, entry.timestamp = item.timestamp

theorem correctTable_perm {p k d : Nat}
    {source : List (SourceVector p k d)}
    {before after : List (TaggedPivot p k d)}
    (correct : CorrectTable source before) (hperm : after.Perm before)
    (hordered : Ordered (after.map TaggedPivot.pivot)) :
    CorrectTable source after where
  ordered := hordered
  span_at := by
    intro left
    rw [correct.span_at left]
    exact (span_rowsOf_eq_of_perm (pivotsAt_perm (left := left) hperm)).symm
  card_at := by
    intro left
    rw [correct.card_at left]
    congr 1
    exact (pivotsAt_perm (left := left) hperm).length_eq.symm

noncomputable def SettledTable.perm {p k d : Nat}
    {source : List (SourceVector p k d)} (table : SettledTable source)
    (entries : List (TaggedPivot p k d)) (hperm : entries.Perm table.entries)
    (hordered : Ordered (entries.map TaggedPivot.pivot)) : SettledTable source where
  entries := entries
  correct := correctTable_perm table.correct hperm hordered
  timestamp_source := by
    intro entry hentry
    exact table.timestamp_source entry (hperm.mem_iff.mp hentry)

noncomputable def SettledTable.basis {p k d : Nat}
    {source : List (SourceVector p k d)} (table : SettledTable source) : Basis p k d :=
  basisAt table.correct 0

noncomputable def emptySettledTable {p k d : Nat} (_hp : p.Prime) :
    SettledTable ([] : List (SourceVector p k d)) where
  entries := []
  correct := {
    ordered := by simp [Ordered]
    span_at := by
      intro left
      simp [sourceSubmodule, sourceSet, pivotsAt, rowsOf]
    card_at := by
      intro left
      letI : NeZero (p ^ k) := ⟨pow_ne_zero _ _hp.ne_zero⟩
      simp [sourceSubmodule, sourceSet, pivotsAt]
  }
  timestamp_source := by simp

theorem sourceSubmodule_prepend_of_le {p k d : Nat}
    (head : SourceVector p k d) (tail : List (SourceVector p k d))
    (left : Nat) (hle : left ≤ head.timestamp)
    (hall : ∀ item ∈ tail, left ≤ item.timestamp) :
    sourceSubmodule (head :: tail) left =
      sourceSubmodule tail 0 ⊔ Submodule.span (Ring p k) {head.row} := by
  rw [sourceSubmodule, sourceSet_cons_of_le head tail left hle,
    sourceSet_eq_zero_of_all tail left hall]
  unfold sourceSubmodule
  rw [Submodule.span_insert, sup_comm]

theorem sourceSubmodule_prepend_of_not_le {p k d : Nat}
    (head : SourceVector p k d) (tail : List (SourceVector p k d))
    (left : Nat) (hle : ¬left ≤ head.timestamp) :
    sourceSubmodule (head :: tail) left = sourceSubmodule tail left := by
  unfold sourceSubmodule
  rw [sourceSet_cons_of_not_le head tail left hle]

/-- Prepend one older timestamp after the priority queue has settled exactly
its nonzero quotient layers.  The result is correct for every timestamp
threshold, not just for the full prefix. -/
noncomputable def SettledTable.prepend {p k d h : Nat} (hp : p.Prime)
    {tail : List (SourceVector p k d)} (rest : SettledTable tail)
    (head : SourceVector p k d)
    (headOlder : ∀ item ∈ tail, head.timestamp < item.timestamp)
    (family : Fin h → PivotRow p k d)
    (horder : addOrderOf (rest.basis.submodule.mkQ head.row) = p ^ h)
    (hrepresentative : ∀ index : Fin h,
      LayerRepresentative rest.basis.submodule head.row index (family index).row)
    (hmissing : ∀ index : Fin h, ∀ current ∈ rest.basis.pivots,
      current.slot ≠ (family index).slot) :
    SettledTable (head :: tail) := by
  let additions := taggedFamily head.timestamp family
  let entries := insertAllTagged additions rest.entries
  let newBasis := basisFromSettledLayers rest.basis hp head.row family
    horder hrepresentative hmissing
  have hentriesPerm : entries.Perm (additions ++ rest.entries) := by
    exact perm_insertAllTagged additions rest.entries
  have hrestPivots : rest.basis.pivots = rest.entries.map TaggedPivot.pivot := by
    change pivotsAt rest.entries 0 = rest.entries.map TaggedPivot.pivot
    exact pivotsAt_zero rest.entries
  have hbasisPivots : newBasis.pivots = entries.map TaggedPivot.pivot := by
    dsimp [newBasis, basisFromSettledLayers, basisFromLayerFamily,
      familyCombined, entries, additions]
    rw [map_insertAllTagged, map_taggedFamily, ← hrestPivots]
  have htimestamp : ∀ entry ∈ entries,
      ∃ item ∈ head :: tail, entry.timestamp = item.timestamp := by
    intro entry hentry
    have hconcat : entry ∈ additions ++ rest.entries :=
      hentriesPerm.mem_iff.mp hentry
    rw [List.mem_append] at hconcat
    rcases hconcat with hadd | hold
    · refine ⟨head, by simp, ?_⟩
      exact taggedFamily_timestamp head.timestamp family hadd
    · rcases rest.timestamp_source entry hold with ⟨item, hitem, htime⟩
      exact ⟨item, by simp [hitem], htime⟩
  refine {
    entries := entries
    correct := {
      ordered := by
        rw [← hbasisPivots]
        exact newBasis.ordered
      span_at := ?_
      card_at := ?_
    }
    timestamp_source := htimestamp
  }
  · intro left
    by_cases hhead : left ≤ head.timestamp
    · have hallSource : ∀ item ∈ tail, left ≤ item.timestamp := by
        intro item hitem
        exact le_trans hhead (Nat.le_of_lt (headOlder item hitem))
      have hallEntries : ∀ entry ∈ entries, left ≤ entry.timestamp := by
        intro entry hentry
        rcases htimestamp entry hentry with ⟨item, hitem, htime⟩
        rcases List.mem_cons.mp hitem with rfl | htail
        · simpa [htime] using hhead
        · simpa [htime] using hallSource item htail
      have hsource : sourceSubmodule (head :: tail) left =
          extendedSubmodule rest.basis head.row := by
        exact sourceSubmodule_prepend_of_le head tail left hhead hallSource
      have hpivots : pivotsAt entries left = newBasis.pivots := by
        rw [pivotsAt_eq_map_of_all entries left hallEntries, ← hbasisPivots]
      calc
        sourceSubmodule (head :: tail) left = extendedSubmodule rest.basis head.row := hsource
        _ = newBasis.generated := rfl
        _ = Submodule.span (Ring p k) {row | row ∈ rowsOf newBasis.pivots} :=
          newBasis.generated_eq_span
        _ = Submodule.span (Ring p k) {row | row ∈ rowsOf (pivotsAt entries left)} := by
          rw [hpivots]
    · have hselected : (pivotsAt entries left).Perm (pivotsAt rest.entries left) := by
        have hperm := pivotsAt_perm (left := left) hentriesPerm
        rw [pivotsAt_append,
          pivotsAt_taggedFamily_of_not_le head.timestamp left family hhead] at hperm
        simpa using hperm
      calc
        sourceSubmodule (head :: tail) left = sourceSubmodule tail left :=
          sourceSubmodule_prepend_of_not_le head tail left hhead
        _ = Submodule.span (Ring p k)
            {row | row ∈ rowsOf (pivotsAt rest.entries left)} := rest.correct.span_at left
        _ = Submodule.span (Ring p k)
            {row | row ∈ rowsOf (pivotsAt entries left)} :=
          (span_rowsOf_eq_of_perm hselected).symm
  · intro left
    by_cases hhead : left ≤ head.timestamp
    · have hallSource : ∀ item ∈ tail, left ≤ item.timestamp := by
        intro item hitem
        exact le_trans hhead (Nat.le_of_lt (headOlder item hitem))
      have hallEntries : ∀ entry ∈ entries, left ≤ entry.timestamp := by
        intro entry hentry
        rcases htimestamp entry hentry with ⟨item, hitem, htime⟩
        rcases List.mem_cons.mp hitem with rfl | htail
        · simpa [htime] using hhead
        · simpa [htime] using hallSource item htail
      have hsource : sourceSubmodule (head :: tail) left =
          extendedSubmodule rest.basis head.row :=
        sourceSubmodule_prepend_of_le head tail left hhead hallSource
      have hpivots : pivotsAt entries left = newBasis.pivots := by
        rw [pivotsAt_eq_map_of_all entries left hallEntries, ← hbasisPivots]
      rw [hsource, hpivots]
      exact newBasis.card_generated
    · have hselected : (pivotsAt entries left).Perm (pivotsAt rest.entries left) := by
        have hperm := pivotsAt_perm (left := left) hentriesPerm
        rw [pivotsAt_append,
          pivotsAt_taggedFamily_of_not_le head.timestamp left family hhead] at hperm
        simpa using hperm
      rw [sourceSubmodule_prepend_of_not_le head tail left hhead,
        rest.correct.card_at left, hselected.length_eq]

/-- A terminal priority-queue state, described without choosing canonical
normal forms.  At each timestamp it contains exactly one row for each surviving
quotient layer, and its slots are fresh from all newer timestamps. -/
inductive TerminalLayers (p k d : Nat) :
    List (SourceVector p k d) → List (TaggedPivot p k d) → Type where
  | nil : TerminalLayers p k d [] []
  | cons {head : SourceVector p k d} {tail : List (SourceVector p k d)}
      {entries tailEntries : List (TaggedPivot p k d)} {h : Nat}
      (rest : TerminalLayers p k d tail tailEntries)
      (headOlder : ∀ item ∈ tail, head.timestamp < item.timestamp)
      (family : Fin h → PivotRow p k d)
      (horder : addOrderOf ((sourceSubmodule tail 0).mkQ head.row) = p ^ h)
      (hrepresentative : ∀ index : Fin h,
        LayerRepresentative (sourceSubmodule tail 0) head.row index (family index).row)
      (hmissing : ∀ index : Fin h,
        ∀ current ∈ tailEntries.map TaggedPivot.pivot,
          current.slot ≠ (family index).slot)
      (hentries : entries.Perm (taggedFamily head.timestamp family ++ tailEntries))
      (hordered : Ordered (entries.map TaggedPivot.pivot)) :
      TerminalLayers p k d (head :: tail) entries

/-- Terminal layer certificates recursively produce a table whose filtered
pivots are complete cardinal bases for every suffix threshold. -/
noncomputable def TerminalLayers.toSettled {p k d : Nat} (hp : p.Prime) :
    {source : List (SourceVector p k d)} →
    {entries : List (TaggedPivot p k d)} →
    TerminalLayers p k d source entries →
      {table : SettledTable source // table.entries = entries}
  | [], [], .nil => ⟨emptySettledTable hp, rfl⟩
  | _, _, @TerminalLayers.cons _ _ _ head tail entries tailEntries h rest
      headOlder family horder hrepresentative hmissing hentries hordered => by
      let restResult := rest.toSettled hp
      let restTable : SettledTable tail := restResult.1
      have hrestEntries : restTable.entries = tailEntries := restResult.2
      have hbase : restTable.basis.submodule = sourceSubmodule tail 0 := rfl
      have hbasePivots : restTable.basis.pivots =
          tailEntries.map TaggedPivot.pivot := by
        change pivotsAt restTable.entries 0 = tailEntries.map TaggedPivot.pivot
        rw [pivotsAt_zero, hrestEntries]
      have horder' : addOrderOf (restTable.basis.submodule.mkQ head.row) = p ^ h := by
        change addOrderOf ((sourceSubmodule tail 0).mkQ head.row) = p ^ h
        exact horder
      have hrepresentative' : ∀ index : Fin h,
          LayerRepresentative restTable.basis.submodule head.row index
            (family index).row := by
        change ∀ index : Fin h,
          LayerRepresentative (sourceSubmodule tail 0) head.row index (family index).row
        exact hrepresentative
      have hmissing' : ∀ index : Fin h, ∀ current ∈ restTable.basis.pivots,
          current.slot ≠ (family index).slot := by
        intro index current hcurrent
        apply hmissing index current
        simpa [hbasePivots] using hcurrent
      let built := restTable.prepend hp head headOlder family horder'
        hrepresentative' hmissing'
      have hbuilteq : built.entries =
          insertAllTagged (taggedFamily head.timestamp family) restTable.entries := rfl
      have hbuiltPerm : built.entries.Perm
          (taggedFamily head.timestamp family ++ tailEntries) := by
        rw [hbuilteq]
        have hperm := perm_insertAllTagged
          (taggedFamily head.timestamp family) restTable.entries
        simpa [hrestEntries] using hperm
      have htargetPerm : entries.Perm built.entries :=
        hentries.trans hbuiltPerm.symm
      let result := built.perm entries htargetPerm hordered
      exact ⟨result, rfl⟩

theorem terminal_correct {p k d : Nat} (hp : p.Prime)
    {source : List (SourceVector p k d)}
    {entries : List (TaggedPivot p k d)}
    (terminal : TerminalLayers p k d source entries) :
    CorrectTable source entries := by
  let result := terminal.toSettled hp
  have hentries : result.1.entries = entries := result.2
  simpa [hentries] using result.1.correct

end CompositeModulusBasis.SettledTimestamp
