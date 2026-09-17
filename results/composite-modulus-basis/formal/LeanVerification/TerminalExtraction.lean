import LeanVerification.TimestampLayerInvariant
import Mathlib.Tactic

/-!
# Extracting the timestamp invariant from a drained table

A drained table is correct once four operational invariants hold: timestamps
are strictly ordered in the source, stored slots and `(timestamp,layer)` keys
are unique, every stored row retains its layer identity, and every layer below
the current quotient exponent is still present.  Extra layers are impossible:
they would lie in the newer suffix while exposing a slot missing from its
complete basis.
-/

namespace CompositeModulusBasis.TerminalExtraction

open BasisQuery CyclicExtension PadicEchelon SettledTimestamp
  TimestampedBasis TimestampLayerInvariant

theorem SourceStrict.timestampInjective {p k d : Nat}
    {source : List (SourceVector p k d)} (hstrict : SourceStrict source) :
    TimestampInjective source := by
  have hnodup : (source.map SourceVector.timestamp).Nodup := by
    induction source with
    | nil => simp
    | cons head tail ih =>
        rw [SourceStrict] at hstrict
        cases hstrict with
        | cons hhead htail =>
          rw [List.map_cons, List.nodup_cons]
          constructor
          · intro hmem
            rcases List.mem_map.mp hmem with ⟨item, hitem, heq⟩
            have hlt := hhead item hitem
            omega
          · exact ih htail
  intro left right hleft hright htime
  exact List.inj_on_of_nodup_map hnodup hleft hright htime

theorem ordered_tagged_slot_injective {p k d : Nat}
    {entries : List (TaggedPivot p k d)}
    (hordered : Ordered (entries.map TaggedPivot.pivot))
    {left right : TaggedPivot p k d}
    (hleft : left ∈ entries) (hright : right ∈ entries)
    (hslot : left.pivot.slot = right.pivot.slot) : left = right := by
  have hslots : (entries.map fun entry => entry.pivot.slot).Nodup := by
    have := ordered_slots_nodup hordered
    simpa [List.map_map, Function.comp_def] using this
  exact List.inj_on_of_nodup_map hslots hleft hright hslot

theorem key_injective {p k d : Nat} {entries : List (TaggedPivot p k d)}
    (hkeys : KeysNodup entries)
    {left right : TaggedPivot p k d}
    (hleft : left ∈ entries) (hright : right ∈ entries)
    (hkey : pivotKey left = pivotKey right) : left = right :=
  List.inj_on_of_nodup_map hkeys hleft hright hkey

def withoutTimestamp {p k d : Nat} (timestamp : Nat)
    (entries : List (TaggedPivot p k d)) : List (TaggedPivot p k d) :=
  entries.filter fun entry => entry.timestamp != timestamp

theorem mem_withoutTimestamp {p k d : Nat} (timestamp : Nat)
    {entries : List (TaggedPivot p k d)} {entry : TaggedPivot p k d} :
    entry ∈ withoutTimestamp timestamp entries ↔
      entry ∈ entries ∧ entry.timestamp ≠ timestamp := by
  simp [withoutTimestamp]

theorem ordered_withoutTimestamp {p k d : Nat} (timestamp : Nat)
    {entries : List (TaggedPivot p k d)}
    (hordered : Ordered (entries.map TaggedPivot.pivot)) :
    Ordered ((withoutTimestamp timestamp entries).map TaggedPivot.pivot) := by
  have hsub : List.Sublist
      ((withoutTimestamp timestamp entries).map TaggedPivot.pivot)
      (entries.map TaggedPivot.pivot) := List.Sublist.map _ (List.filter_sublist)
  exact hordered.sublist hsub

theorem keysNodup_withoutTimestamp {p k d : Nat} (timestamp : Nat)
    {entries : List (TaggedPivot p k d)} (hkeys : KeysNodup entries) :
    KeysNodup (withoutTimestamp timestamp entries) := by
  have hsub : List.Sublist
      ((withoutTimestamp timestamp entries).map pivotKey)
      (entries.map pivotKey) := List.Sublist.map _ (List.filter_sublist)
  exact hkeys.sublist hsub

theorem tableValid_tail {p k d : Nat}
    (head : SourceVector p k d) (tail : List (SourceVector p k d))
    (headOlder : ∀ item ∈ tail, head.timestamp < item.timestamp)
    {entries : List (TaggedPivot p k d)}
    (hvalid : TableLayerValid (head :: tail) entries) :
    TableLayerValid tail (withoutTimestamp head.timestamp entries) := by
  intro entry hentry
  have hentryFull := (mem_withoutTimestamp head.timestamp).1 hentry
  rcases hvalid entry hentryFull.1 with
    ⟨item, hitem, htime, hlayer, hrepresentative⟩
  simp only [TaggedPivot.asVector_timestamp, TaggedPivot.asVector_layer,
    TaggedPivot.asVector_row] at htime hlayer hrepresentative ⊢
  rcases List.mem_cons.mp hitem with rfl | hitemTail
  · exact False.elim (hentryFull.2 htime)
  · refine ⟨item, hitemTail, htime, hlayer, ?_⟩
    have hsubmodule := newerSubmodule_tail head tail headOlder hitemTail
    rw [htime, hsubmodule] at hrepresentative
    simp only [TaggedPivot.asVector_timestamp, TaggedPivot.asVector_layer,
      TaggedPivot.asVector_row]
    rw [htime]
    exact hrepresentative

theorem protectedComplete_tail {p k d : Nat} (hp : p.Prime)
    (head : SourceVector p k d) (tail : List (SourceVector p k d))
    (headOlder : ∀ item ∈ tail, head.timestamp < item.timestamp)
    {entries : List (TaggedPivot p k d)}
    (hcomplete : ProtectedComplete hp (head :: tail) entries) :
    ProtectedComplete hp tail (withoutTimestamp head.timestamp entries) := by
  intro item hitem e he
  have he' : e < quotientExponent hp (head :: tail) item := by
    rwa [quotientExponent_tail hp head tail headOlder hitem]
  rcases hcomplete item (by simp [hitem]) e he' with
    ⟨entry, hentry, htime, hlayer⟩
  refine ⟨entry, (mem_withoutTimestamp head.timestamp).2 ⟨hentry, ?_⟩,
    htime, hlayer⟩
  have := headOlder item hitem
  omega

private theorem taggedFamily_keys_nodup {p k d h : Nat}
    (timestamp : Nat) (family : Fin h → PivotRow p k d) :
    ((taggedFamily timestamp family).map pivotKey).Nodup := by
  rw [taggedFamily, List.map_ofFn, List.nodup_ofFn]
  intro left right heq
  apply Fin.ext
  exact congrArg Prod.snd heq

private theorem taggedFamily_tail_keys_disjoint {p k d h : Nat}
    (timestamp : Nat) (family : Fin h → PivotRow p k d)
    (tailEntries : List (TaggedPivot p k d))
    (htail : ∀ entry ∈ tailEntries, entry.timestamp ≠ timestamp) :
    List.Disjoint ((taggedFamily timestamp family).map pivotKey)
      (tailEntries.map pivotKey) := by
  rw [List.disjoint_left]
  intro value hfamily htailKey
  rcases List.mem_map.mp hfamily with ⟨familyEntry, hfamilyEntry, rfl⟩
  rcases List.mem_map.mp htailKey with ⟨tailEntry, htailEntry, hkey⟩
  have hfamilyTime := taggedFamily_timestamp timestamp family hfamilyEntry
  have htime := congrArg Prod.fst hkey
  change tailEntry.timestamp = familyEntry.timestamp at htime
  exact htail tailEntry htailEntry (htime.trans hfamilyTime)

/-- The main terminal extraction theorem. -/
noncomputable def terminalLayers_of_invariants {p k d : Nat} (hp : p.Prime) :
    ∀ {source : List (SourceVector p k d)}
      {entries : List (TaggedPivot p k d)},
      SourceStrict source →
      Ordered (entries.map TaggedPivot.pivot) →
      KeysNodup entries →
      TableLayerValid source entries →
      ProtectedComplete hp source entries →
      TerminalLayers p k d source entries
  | [], entries, hstrict, hordered, hkeys, hvalid, hcomplete => by
      have hempty : entries = [] := by
        apply List.eq_nil_iff_forall_not_mem.2
        intro entry hentry
        rcases hvalid entry hentry with ⟨item, hitem, _⟩
        simp at hitem
      subst entries
      exact .nil
  | head :: tail, entries, hstrict, hordered, hkeys, hvalid, hcomplete => by
      have hparts := List.pairwise_cons.1 hstrict
      let headOlder := hparts.1
      let tailStrict := hparts.2
      have hsourceInjective : TimestampInjective (head :: tail) :=
        SourceStrict.timestampInjective hstrict
      let tailEntries := withoutTimestamp head.timestamp entries
      have htailOrdered : Ordered (tailEntries.map TaggedPivot.pivot) :=
        ordered_withoutTimestamp head.timestamp hordered
      have htailKeys : KeysNodup tailEntries :=
        keysNodup_withoutTimestamp head.timestamp hkeys
      have htailValid : TableLayerValid tail tailEntries :=
        tableValid_tail head tail headOlder hvalid
      have htailComplete : ProtectedComplete hp tail tailEntries :=
        protectedComplete_tail hp head tail headOlder hcomplete
      have restTerminal : TerminalLayers p k d tail tailEntries :=
        terminalLayers_of_invariants hp tailStrict htailOrdered htailKeys
          htailValid htailComplete
      have tailCorrect : CorrectTable tail tailEntries := terminal_correct hp restTerminal
      let tailBasis : Basis p k d := basisAt tailCorrect 0
      let h : Nat := quotientExponent hp (head :: tail) head
      have horder : addOrderOf ((sourceSubmodule tail 0).mkQ head.row) = p ^ h := by
        have horderFull := quotientExponent_order hp (head :: tail) head
        rw [newerSubmodule_head head tail headOlder] at horderFull
        exact horderFull
      let headEntry : Fin h → TaggedPivot p k d := fun index =>
        Classical.choose (hcomplete head (by simp) index index.isLt)
      have headEntry_spec (index : Fin h) :
          headEntry index ∈ entries ∧
            (headEntry index).timestamp = head.timestamp ∧
            (headEntry index).layer = index :=
        Classical.choose_spec (hcomplete head (by simp) index index.isLt)
      let family : Fin h → PivotRow p k d := fun index => (headEntry index).pivot
      have htaggedFamily : taggedFamily head.timestamp family = List.ofFn headEntry := by
        rw [taggedFamily]
        congr 1
        funext index
        cases hentryEq : headEntry index with
        | mk timestamp layer pivot =>
            have hspec := headEntry_spec index
            simp only [hentryEq] at hspec
            simp only [family, hentryEq]
            cases hspec.2.1
            cases hspec.2.2
            rfl
      have hrepresentative : ∀ index : Fin h,
          LayerRepresentative (sourceSubmodule tail 0) head.row index
            (family index).row := by
        intro index
        rcases hvalid (headEntry index) (headEntry_spec index).1 with
          ⟨item, hitem, htime, hlayer, hrep⟩
        simp only [TaggedPivot.asVector_timestamp, TaggedPivot.asVector_layer,
          TaggedPivot.asVector_row] at htime hlayer hrep
        have hitemEq : item = head := by
          apply hsourceInjective hitem (by simp)
          rw [← htime, (headEntry_spec index).2.1]
        subst item
        have hnewer := newerSubmodule_head head tail headOlder
        rw [(headEntry_spec index).2.1, hnewer] at hrep
        simpa [family, (headEntry_spec index).2.2] using hrep
      have htailBasisPivots : tailBasis.pivots =
          tailEntries.map TaggedPivot.pivot := by
        change pivotsAt tailEntries 0 = tailEntries.map TaggedPivot.pivot
        exact pivotsAt_zero tailEntries
      have hmissing : ∀ index : Fin h, ∀ current ∈ tailBasis.pivots,
          current.slot ≠ (family index).slot := by
        intro index current hcurrent hslot
        rw [htailBasisPivots] at hcurrent
        rcases List.mem_map.mp hcurrent with ⟨currentEntry, hcurrentEntry, rfl⟩
        have hcurrentFull := (mem_withoutTimestamp head.timestamp).1 hcurrentEntry
        have heq := ordered_tagged_slot_injective hordered
          hcurrentFull.1 (headEntry_spec index).1 hslot
        have hnot := hcurrentFull.2
        rw [heq, (headEntry_spec index).2.1] at hnot
        exact hnot rfl
      have head_layer_lt (entry : TaggedPivot p k d) (hentry : entry ∈ entries)
          (htime : entry.timestamp = head.timestamp) : entry.layer < h := by
        rcases hvalid entry hentry with
          ⟨item, hitem, hitemTime, hlayerBound, hrep⟩
        simp only [TaggedPivot.asVector_timestamp, TaggedPivot.asVector_layer,
          TaggedPivot.asVector_row] at hitemTime hlayerBound hrep
        have hitemEq : item = head := by
          apply hsourceInjective hitem (by simp)
          rw [← hitemTime, htime]
        subst item
        have hnewer := newerSubmodule_head head tail headOlder
        rw [htime, hnewer] at hrep
        by_contra hnot
        have hmem : entry.pivot.row ∈ sourceSubmodule tail 0 :=
          hrep.mem_of_exponent_le hp horder (Nat.le_of_not_gt hnot)
        have hslotMissing : ∀ pivot ∈ tailBasis.pivots,
            pivot.slot ≠ entry.pivot.slot := by
          intro pivot hpivot hpivotSlot
          rw [htailBasisPivots] at hpivot
          rcases List.mem_map.mp hpivot with ⟨pivotEntry, hpivotEntry, rfl⟩
          have hpivotFull := (mem_withoutTimestamp head.timestamp).1 hpivotEntry
          have heq := ordered_tagged_slot_injective hordered
            hpivotFull.1 hentry hpivotSlot
          exact hpivotFull.2 (by rw [heq, htime])
        exact (tailBasis.not_mem_of_missing_lead hp.one_lt
          (PivotRow.hasLead hp.one_lt entry.pivot) hslotMissing) hmem
      have hentriesPerm : entries.Perm
          (taggedFamily head.timestamp family ++ tailEntries) := by
        classical
        have hentriesNodup : entries.Nodup := List.Nodup.of_map pivotKey hkeys
        have htailKeyNodup : (tailEntries.map pivotKey).Nodup := htailKeys
        have hfamilyKeyNodup := taggedFamily_keys_nodup head.timestamp family
        have hdisjoint := taggedFamily_tail_keys_disjoint head.timestamp family tailEntries
          (fun entry hentry => (mem_withoutTimestamp head.timestamp).1 hentry |>.2)
        have hrightKeys :
            ((taggedFamily head.timestamp family ++ tailEntries).map pivotKey).Nodup := by
          rw [List.map_append]
          exact List.Nodup.append hfamilyKeyNodup htailKeyNodup hdisjoint
        have hrightNodup : (taggedFamily head.timestamp family ++ tailEntries).Nodup :=
          List.Nodup.of_map pivotKey hrightKeys
        apply (List.perm_ext_iff_of_nodup hentriesNodup hrightNodup).2
        intro entry
        constructor
        · intro hentry
          by_cases htime : entry.timestamp = head.timestamp
          · have hlayer := head_layer_lt entry hentry htime
            let index : Fin h := ⟨entry.layer, hlayer⟩
            have hchosen := headEntry_spec index
            have hkey : pivotKey entry = pivotKey (headEntry index) := by
              apply Prod.ext
              · change entry.timestamp = (headEntry index).timestamp
                exact htime.trans hchosen.2.1.symm
              · change entry.layer = (headEntry index).layer
                simpa [index] using hchosen.2.2.symm
            have heq := key_injective hkeys hentry hchosen.1 hkey
            rw [List.mem_append, htaggedFamily, List.mem_ofFn']
            exact Or.inl ⟨index, heq.symm⟩
          · rw [List.mem_append]
            exact Or.inr ((mem_withoutTimestamp head.timestamp).2 ⟨hentry, htime⟩)
        · rw [List.mem_append]
          rintro (hfamily | htail)
          · rw [htaggedFamily, List.mem_ofFn'] at hfamily
            rcases hfamily with ⟨index, rfl⟩
            exact (headEntry_spec index).1
          · exact (mem_withoutTimestamp head.timestamp).1 htail |>.1
      have hmissing' : ∀ index : Fin h,
          ∀ current ∈ tailEntries.map TaggedPivot.pivot,
            current.slot ≠ (family index).slot := by
        intro index current hcurrent
        apply hmissing index current
        rw [htailBasisPivots]
        exact hcurrent
      exact TerminalLayers.cons restTerminal headOlder family horder
        hrepresentative hmissing' hentriesPerm hordered

theorem drained_table_correct {p k d : Nat} (hp : p.Prime)
    {source : List (SourceVector p k d)}
    {entries : List (TaggedPivot p k d)}
    (hstrict : SourceStrict source)
    (hordered : Ordered (entries.map TaggedPivot.pivot))
    (hkeys : KeysNodup entries)
    (hvalid : TableLayerValid source entries)
    (hcomplete : ProtectedComplete hp source entries) :
    CorrectTable source entries :=
  terminal_correct hp
    (terminalLayers_of_invariants hp hstrict hordered hkeys hvalid hcomplete)

end CompositeModulusBasis.TerminalExtraction
