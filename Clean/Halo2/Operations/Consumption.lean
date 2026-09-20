import Clean.Halo2.Operations.Copy
import Clean.Halo2.WitnessSupport

/-!
# Witness reads, and copies and reads together

`RegionOperation.Reads` is the second instance of `AssignedFrom`: an advice assignment reads
the cells of a certified support of its witness program (`WitnessFunctionSupport`), and the
other operations do not read any cells. The read set of a native closure is never computed;
it is whatever a support rule for the closure's shape supplies. `RegionOperation.Consumes` combines
copies and reads, and provenance for it is provenance for each.
-/

namespace Halo2

variable {F : Type} [FiniteField F]

/-- An advice assignment reads a certified support of its witness program; the other
operations do not read any cells. -/
def RegionOperation.Reads : RegionOperation F → List Cell → Prop
  | .assignAdvice _ _ program, cells =>
      ∃ reads : List (AssignedCell F),
        WitnessFunctionSupport reads (fun env => (program.eval env)[0]) ∧
          cells = reads.map (·.cell)
  | _, cells => cells = []

/-- Copies and reads together: everything an operation needs to find already assigned. -/
def RegionOperation.Consumes (operation : RegionOperation F) (cells : List Cell) : Prop :=
  ∃ reads, operation.Reads reads ∧ cells = operation.copiedCells ++ reads

namespace RegionOperation

variable (available : List Cell)

/-! What each operation consumes, reduced: a support obligation for an advice assignment,
memberships for the copy-like operations, nothing for the rest. -/

@[keygen_norm, keygen_spine]
theorem consumesFrom_consumes_assignAdvice_iff (column : Column .advice) (row : ℕ)
    (program : WitgenIR F 1) :
    ConsumesFrom Consumes available (.assignAdvice column row program) ↔
      ∃ reads : List (AssignedCell F),
        WitnessFunctionSupport reads (fun env => (program.eval env)[0]) ∧
          ∀ cell ∈ reads, cell.cell ∈ available := by
  simp only [ConsumesFrom, Consumes, Reads, copiedCells, List.nil_append]
  constructor
  · rintro ⟨_, ⟨_, ⟨reads, hsupport, rfl⟩, rfl⟩, havailable⟩
    exact ⟨reads, hsupport, fun cell hcell => havailable _ (List.mem_map_of_mem hcell)⟩
  · rintro ⟨reads, hsupport, havailable⟩
    refine ⟨reads.map (·.cell), ⟨reads.map (·.cell), ⟨reads, hsupport, rfl⟩, rfl⟩, ?_⟩
    intro cell hcell
    obtain ⟨read, hread, rfl⟩ := List.mem_map.mp hcell
    exact havailable read hread

/-- The form the registration tactic applies, with the read set left to unification. -/
theorem consumesFrom_consumes_assignAdvice_of_support (column : Column .advice) (row : ℕ)
    (program : WitgenIR F 1) (reads : List (AssignedCell F))
    (support : WitnessFunctionSupport reads (fun env => (program.eval env)[0]))
    (havailable : ∀ cell ∈ reads, cell.cell ∈ available) :
    ConsumesFrom Consumes available (.assignAdvice column row program) :=
  (consumesFrom_consumes_assignAdvice_iff available column row program).mpr
    ⟨reads, support, havailable⟩

@[keygen_norm, keygen_spine]
theorem consumesFrom_consumes_assignFixed_iff (column : Column .fixed) (row : ℕ) (value : F) :
    ConsumesFrom Consumes available (.assignFixed column row value) ↔ True := by
  simp [ConsumesFrom, Consumes, Reads, copiedCells]

@[keygen_norm, keygen_spine]
theorem consumesFrom_consumes_enableGate_iff (gate : Gate F) (row : ℕ) :
    ConsumesFrom Consumes available (.enableGate gate row) ↔ True := by
  simp [ConsumesFrom, Consumes, Reads, copiedCells]

@[keygen_norm, keygen_spine]
theorem consumesFrom_consumes_enableLookup_iff (lookup : LookupArgument F)
    (selectors : List Selector) (row : ℕ) :
    ConsumesFrom Consumes available (.enableLookup lookup selectors row) ↔ True := by
  simp [ConsumesFrom, Consumes, Reads, copiedCells]

@[keygen_norm, keygen_spine]
theorem consumesFrom_consumes_constrainEqual_iff (left right : Cell) :
    ConsumesFrom Consumes available (.constrainEqual left right : RegionOperation F) ↔
      left ∈ available ∧ right ∈ available := by
  simp [ConsumesFrom, Consumes, Reads, copiedCells]

@[keygen_norm, keygen_spine]
theorem consumesFrom_consumes_constrainConstant_iff (cell : Cell) (value : F) :
    ConsumesFrom Consumes available (.constrainConstant cell value) ↔ cell ∈ available := by
  simp [ConsumesFrom, Consumes, Reads, copiedCells]

@[keygen_norm, keygen_spine]
theorem consumesFrom_consumes_constrainInstance_iff (cell : Cell) (column : Column .instance)
    (row : ℕ) :
    ConsumesFrom Consumes available (.constrainInstance cell column row : RegionOperation F) ↔
      cell ∈ available := by
  simp [ConsumesFrom, Consumes, Reads, copiedCells]

/-- Consuming from a cell state is copying from it and reading from it. -/
theorem consumesFrom_consumes_iff (operation : RegionOperation F) :
    ConsumesFrom Consumes available operation ↔
      ConsumesFrom Copies available operation ∧ ConsumesFrom Reads available operation := by
  constructor
  · rintro ⟨_, ⟨reads, hreads, rfl⟩, havailable⟩
    exact ⟨⟨_, rfl, fun cell hcell => havailable cell (List.mem_append_left _ hcell)⟩,
      ⟨reads, hreads, fun cell hcell => havailable cell (List.mem_append_right _ hcell)⟩⟩
  · rintro ⟨⟨_, rfl, hcopiesAvailable⟩, ⟨reads, hreads, hreadsAvailable⟩⟩
    refine ⟨operation.copiedCells ++ reads, ⟨reads, hreads, rfl⟩, ?_⟩
    intro cell hcell
    rcases List.mem_append.mp hcell with hcell | hcell
    · exact hcopiesAvailable cell hcell
    · exact hreadsAvailable cell hcell

/-- Under combined provenance, a copy-like operation consumes at least its endpoints. -/
theorem copiedCells_subset_of_consumes
    (operation : RegionOperation F) (cells : List Cell) (hconsumes : operation.Consumes cells) :
    ∀ cell ∈ operation.copiedCells, cell ∈ cells := by
  rintro cell hcell
  obtain ⟨reads, _, rfl⟩ := hconsumes
  exact List.mem_append_left _ hcell

end RegionOperation

def RegionOperations.ConsumedCellsAssigned (operations : RegionOperations F)
    (region : RegionIndex) (cells : List Cell) : Prop :=
  AssignedFrom RegionOperation.Consumes region cells operations

def Operations.ConsumedCellsAssigned (operations : Operations F)
    (initialRegion : RegionIndex) (cells : List Cell) : Prop :=
  AssignedFrom RegionOperation.Consumes initialRegion cells operations

theorem Operations.copyCellsCovered_of_consumed
    (operations : Operations F) (initialRegion : RegionIndex) (cells : List Cell)
    (hassigned : operations.ConsumedCellsAssigned initialRegion cells) :
    operations.CopyCellsCovered initialRegion cells :=
  operations.copyCellsCovered_of_assignedFrom RegionOperation.copiedCells_subset_of_consumes
    initialRegion cells hassigned

/-- Combined provenance is copy provenance together with read provenance. -/
theorem RegionOperations.assignedFrom_consumes_iff (region : RegionIndex)
    (available : List Cell) (operations : RegionOperations F) :
    AssignedFrom RegionOperation.Consumes region available operations ↔
      AssignedFrom RegionOperation.Copies region available operations ∧
        AssignedFrom RegionOperation.Reads region available operations := by
  induction operations generalizing available with
  | nil => simp only [assignedFrom_nil_iff, and_self]
  | cons operation rest inductionHypothesis =>
      simp only [assignedFrom_cons_iff, RegionOperation.consumesFrom_consumes_iff,
        inductionHypothesis]
      exact and_and_and_comm

end Halo2
