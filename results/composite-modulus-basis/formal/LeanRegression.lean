import LeanVerification

/-!
Optional executable finite regression model.  Expected answers enumerate all
coefficients independently.  General correctness and complexity are proved in
`LeanVerification`; none of those proofs depend on this file.
-/

namespace CompositeModulusBasis

namespace FiniteModel

abbrev FRow := List Nat

structure Pivot where
  timestamp : Nat
  level : Nat
  row : FRow
deriving Repr, BEq

abbrev Table := List (Option Pivot)

structure Task where
  timestamp : Nat
  level : Nat
  startColumn : Nat
  row : FRow
deriving Repr, BEq

structure Basis where
  table : Table
  length : Nat
  ok : Bool
deriving Repr, BEq

def modulus (p k : Nat) : Nat := p ^ k

def canonicalRow (m : Nat) (row : FRow) : FRow := row.map (· % m)

def allZero (row : FRow) : Bool := row.all (· == 0)

def rowAt (row : FRow) (column : Nat) : Nat := row.getD column 0

def valuation (p k value : Nat) : Nat :=
  (List.range k).foldl
    (fun best v => if value % (p ^ (v + 1)) = 0 then v + 1 else best) 0

def unitInverse (m unit : Nat) : Nat :=
  ((List.range m).find? fun inverse => unit * inverse % m == 1 % m).getD 0

def subMod (m a b : Nat) : Nat := (a + m - (b % m)) % m

def scaleMod (m c : Nat) (row : FRow) : FRow :=
  row.map fun a => c * a % m

def addMod (m : Nat) (x y : FRow) : FRow :=
  List.zipWith (fun a b => (a + b) % m) x y

def subtractAt (m pPow column : Nat) (row pivot : FRow) : FRow :=
  let factor := rowAt row column / pPow
  List.zipWith (fun a b => subMod m a (factor * b)) row pivot

def tableIndex (k column value : Nat) : Nat := column * k + value

def tableGet (table : Table) (k column value : Nat) : Option Pivot :=
  table.getD (tableIndex k column value) none

def tableSet (table : Table) (k column value : Nat) (pivot : Pivot) : Table :=
  table.set (tableIndex k column value) (some pivot)

def taskBefore (a b : Task) : Bool :=
  if a.timestamp = b.timestamp then a.level < b.level else a.timestamp > b.timestamp

def insertTask (task : Task) : List Task → List Task
  | [] => [task]
  | current :: rest =>
      if taskBefore task current then task :: current :: rest
      else current :: insertTask task rest

structure TaskOutcome where
  table : Table
  replacement : Option Task
  ok : Bool
deriving Repr, BEq

def scanTask (p k d : Nat) : Nat → Nat → FRow → Task → Table → TaskOutcome
  | 0, _, _, _, table => { table := table, replacement := none, ok := true }
  | fuel + 1, column, row, task, table =>
      if column ≥ d then
        { table := table, replacement := none, ok := true }
      else if rowAt row column = 0 then
        scanTask p k d fuel (column + 1) row task table
      else
        let v := valuation p k (rowAt row column)
        let pPow := p ^ v
        match tableGet table k column v with
        | none =>
            let inverse := unitInverse (modulus p k) (rowAt row column / pPow)
            let pivot : Pivot := {
              timestamp := task.timestamp
              level := task.level
              row := scaleMod (modulus p k) inverse row
            }
            { table := tableSet table k column v pivot, replacement := none, ok := true }
        | some old =>
            if old.timestamp = task.timestamp then
              { table := table, replacement := none, ok := false }
            else if task.timestamp > old.timestamp then
              let inverse := unitInverse (modulus p k) (rowAt row column / pPow)
              let pivot : Pivot := {
                timestamp := task.timestamp
                level := task.level
                row := scaleMod (modulus p k) inverse row
              }
              let residual := subtractAt (modulus p k) pPow column old.row pivot.row
              let replacement :=
                if allZero residual then none
                else some {
                  timestamp := old.timestamp
                  level := old.level
                  startColumn := column + 1
                  row := residual
                }
              { table := tableSet table k column v pivot,
                replacement := replacement, ok := true }
            else
              let residual := subtractAt (modulus p k) pPow column row old.row
              scanTask p k d fuel (column + 1) residual task table

structure DrainOutcome where
  table : Table
  ok : Bool
deriving Repr, BEq

def drain (p k d : Nat) : Nat → List Task → Table → DrainOutcome
  | 0, pending, table => { table := table, ok := pending.isEmpty }
  | _ + 1, [], table => { table := table, ok := true }
  | fuel + 1, task :: rest, table =>
      let outcome := scanTask p k d (d - task.startColumn)
        task.startColumn task.row task table
      let pending := match outcome.replacement with
        | none => rest
        | some replacement => insertTask replacement rest
      let tail := drain p k d fuel pending outcome.table
      { table := tail.table, ok := outcome.ok && tail.ok }

def initialTasks (p k timestamp : Nat) (row : FRow) : List Task :=
  (List.range k).filterMap fun level =>
    let scaled := scaleMod (modulus p k) (p ^ level) row
    if allZero scaled then none
    else some { timestamp := timestamp, level := level, startColumn := 0, row := scaled }

def emptyBasis (k d : Nat) : Basis :=
  { table := List.replicate (d * k) none, length := 0, ok := true }

def append (p k d : Nat) (basis : Basis) (vector : FRow) : Basis :=
  let timestamp := basis.length + 1
  let row := canonicalRow (modulus p k) vector
  let pending := initialTasks p k timestamp row
  let outcome := drain p k d (k * (d + 1)) pending basis.table
  { table := outcome.table, length := timestamp, ok := basis.ok && outcome.ok }

def queryLoop (p k d left : Nat) (table : Table) : Nat → Nat → FRow → Bool
  | 0, _, _ => true
  | fuel + 1, column, row =>
      if column ≥ d then true
      else if rowAt row column = 0 then queryLoop p k d left table fuel (column + 1) row
      else
        let v := valuation p k (rowAt row column)
        match tableGet table k column v with
        | none => false
        | some pivot =>
            if pivot.timestamp < left then false
            else
              let residual := subtractAt (modulus p k) (p ^ v) column row pivot.row
              queryLoop p k d left table fuel (column + 1) residual

def contains (p k d : Nat) (basis : Basis) (left : Nat) (target : FRow) : Bool :=
  basis.ok && queryLoop p k d left basis.table d 0
    (canonicalRow (modulus p k) target)

def buildPrefix (p k d right : Nat) (sequence : List FRow) : Basis :=
  (sequence.take right).foldl (append p k d) (emptyBasis k d)

/-! The oracle below knows nothing about pivots or valuations: it enumerates every coefficient. -/

def extendSpan (m : Nat) (span : List FRow) (vector : FRow) : List FRow :=
  (span.flatMap fun old =>
    (List.range m).map fun coefficient => addMod m old (scaleMod m coefficient vector)).eraseDups

def bruteSpan (m d : Nat) (generators : List FRow) : List FRow :=
  generators.foldl (extendSpan m) [List.replicate d 0]

def bruteContains (m d : Nat) (generators : List FRow) (target : FRow) : Bool :=
  (bruteSpan m d generators).contains (canonicalRow m target)

def listsOfLength {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | n + 1, values =>
      values.flatMap fun value => (listsOfLength n values).map (value :: ·)

def interval (sequence : List FRow) (left right : Nat) : List FRow :=
  (sequence.drop (left - 1)).take (right - left + 1)

def checkPrimePowerSequence (p k d n : Nat) (targets : List FRow)
    (sequence : List FRow) : Bool :=
  (List.range n).all fun left0 =>
    (List.range (n - left0)).all fun width =>
      let left := left0 + 1
      let right := left + width
      let basis := buildPrefix p k d right sequence
      targets.all fun target =>
        contains p k d basis left target ==
          bruteContains (modulus p k) d (interval sequence left right) target

def checkPrimePower (p k d n : Nat) : Bool :=
  let rows := listsOfLength d (List.range (modulus p k))
  (listsOfLength n rows).all (checkPrimePowerSequence p k d n rows)

def containsCRT (factors : List (Nat × Nat)) (d right left : Nat)
    (sequence : List FRow) (target : FRow) : Bool :=
  factors.all fun factor =>
    let p := factor.1
    let k := factor.2
    contains p k d (buildPrefix p k d right sequence) left target

def checkCompositeSequence (m d n : Nat) (factors : List (Nat × Nat))
    (targets : List FRow) (sequence : List FRow) : Bool :=
  (List.range n).all fun left0 =>
    (List.range (n - left0)).all fun width =>
      let left := left0 + 1
      let right := left + width
      targets.all fun target =>
        containsCRT factors d right left sequence target ==
          bruteContains m d (interval sequence left right) target

def checkComposite (m d n : Nat) (factors : List (Nat × Nat)) : Bool :=
  let rows := listsOfLength d (List.range m)
  (listsOfLength n rows).all (checkCompositeSequence m d n factors rows)

/-- All length-3, one-dimensional sequences over `Z/4Z`, all intervals and targets. -/
theorem exhaustive_mod4_d1_n3 : checkPrimePower 2 2 1 3 = true := by native_decide

/-- All length-2, two-dimensional sequences over `Z/4Z`, all intervals and targets. -/
theorem exhaustive_mod4_d2_n2 : checkPrimePower 2 2 2 2 = true := by native_decide

/-- A deeper p-adic chain: all length-3 scalar sequences over `Z/8Z`. -/
theorem exhaustive_mod8_d1_n3 : checkPrimePower 2 3 1 3 = true := by native_decide

/-- Odd prime-power path: all length-3 scalar sequences over `Z/9Z`. -/
theorem exhaustive_mod9_d1_n3 : checkPrimePower 3 2 1 3 = true := by native_decide

/-- CRT path checked end-to-end against direct coefficient enumeration modulo 6. -/
theorem exhaustive_mod6_d1_n2 : checkComposite 6 1 2 [(2, 1), (3, 1)] = true := by
  native_decide

/-- CRT with a nontrivial `2²` component, checked directly modulo 12. -/
theorem exhaustive_mod12_d1_n2 : checkComposite 12 1 2 [(2, 2), (3, 1)] = true := by
  native_decide

/-- The non-unit pivot regression from `SOLUTION.md`: `(2,1)` generates `(0,2)`. -/
theorem annihilator_regression :
    bruteContains 4 2 [[2, 1]] [0, 2] = true := by native_decide

/-- The timestamp regression: vector `1` is lost from suffix `[2,2]` containing only `2`. -/
theorem timestamp_regression :
    bruteContains 4 1 [[1], [2]] [1] = true ∧
    bruteContains 4 1 [[2]] [1] = false := by native_decide

end FiniteModel

end CompositeModulusBasis
