import Clean.Halo2.Operations.Provenance

namespace Halo2

variable {F : Type}

/-! ## Copy-cell provenance

The instance of `AssignedFrom` at `RegionOperation.Copies`: a copy-like operation consumes its
endpoints, and nothing else consumes anything. -/

/-- Cells referenced as regional endpoints of copy constraints. -/
def RegionOperation.copiedCells : RegionOperation F → List Cell
  | .constrainEqual left right => [left, right]
  | .constrainConstant cell _ => [cell]
  | .constrainInstance cell _ _ => [cell]
  | _ => []

def RegionOperations.copiedCells (operations : RegionOperations F) : List Cell :=
  operations.flatMap RegionOperation.copiedCells

def RegionOperations.CopyCellsCovered (operations : RegionOperations F)
    (region : RegionIndex) (inputCells : List Cell) : Prop :=
  ∀ cell ∈ operations.copiedCells,
    cell ∈ inputCells ++ operations.assignedCells region

/-- Copy-like operations consume their endpoints; nothing else consumes anything. -/
def RegionOperation.Copies (operation : RegionOperation F) (cells : List Cell) : Prop :=
  cells = operation.copiedCells

def RegionOperations.CopyCellsAssigned (operations : RegionOperations F)
    (region : RegionIndex) (inputCells : List Cell) : Prop :=
  AssignedFrom RegionOperation.Copies region inputCells operations

/-! What each operation consumes under copy provenance, reduced to memberships. -/

namespace RegionOperation

variable (available : List Cell)

@[keygen_norm, keygen_spine]
theorem consumesFrom_copies_assignAdvice_iff (column : Column .advice) (row : ℕ)
    (compute : WitgenIR F 1) :
    ConsumesFrom Copies available (.assignAdvice column row compute) ↔ True := by
  simp [ConsumesFrom, Copies, copiedCells]

@[keygen_norm, keygen_spine]
theorem consumesFrom_copies_assignFixed_iff (column : Column .fixed) (row : ℕ) (value : F) :
    ConsumesFrom Copies available (.assignFixed column row value) ↔ True := by
  simp [ConsumesFrom, Copies, copiedCells]

@[keygen_norm, keygen_spine]
theorem consumesFrom_copies_enableGate_iff (gate : Gate F) (row : ℕ) :
    ConsumesFrom Copies available (.enableGate gate row) ↔ True := by
  simp [ConsumesFrom, Copies, copiedCells]

@[keygen_norm, keygen_spine]
theorem consumesFrom_copies_enableLookup_iff (lookup : LookupArgument F)
    (selectors : List Selector) (row : ℕ) :
    ConsumesFrom Copies available (.enableLookup lookup selectors row) ↔ True := by
  simp [ConsumesFrom, Copies, copiedCells]

@[keygen_norm, keygen_spine]
theorem consumesFrom_copies_constrainEqual_iff (left right : Cell) :
    ConsumesFrom Copies available (.constrainEqual left right : RegionOperation F) ↔
      left ∈ available ∧ right ∈ available := by
  simp [ConsumesFrom, Copies, copiedCells]

@[keygen_norm, keygen_spine]
theorem consumesFrom_copies_constrainConstant_iff (cell : Cell) (value : F) :
    ConsumesFrom Copies available (.constrainConstant cell value) ↔ cell ∈ available := by
  simp [ConsumesFrom, Copies, copiedCells]

@[keygen_norm, keygen_spine]
theorem consumesFrom_copies_constrainInstance_iff (cell : Cell) (column : Column .instance)
    (row : ℕ) :
    ConsumesFrom Copies available (.constrainInstance cell column row : RegionOperation F) ↔
      cell ∈ available := by
  simp [ConsumesFrom, Copies, copiedCells]

/-- Under copy provenance, a copy-like operation consumes exactly its endpoints. -/
theorem copiedCells_subset_of_copies
    (operation : RegionOperation F) (cells : List Cell) (hcopies : operation.Copies cells) :
    ∀ cell ∈ operation.copiedCells, cell ∈ cells := by
  intro cell hcell
  rw [hcopies]
  exact hcell

end RegionOperation

/-- A region fragment containing no copy-like operation is copy-lawful for every incoming
cell state. -/
@[keygen_helper]
theorem RegionOperations.copyCellsAssignedFrom_of_forall_copiedCells_eq_nil
    (operations : RegionOperations F) (region : RegionIndex)
    (available : List Cell)
    (hoperations : operations.Forall fun operation =>
      operation.copiedCells = []) :
    operations.AssignedFrom RegionOperation.Copies region available :=
  assignedFrom_of_forall_consumes_nil _ region available operations
    (List.forall_iff_forall_mem.mpr fun operation hoperation =>
      (List.forall_iff_forall_mem.mp hoperations operation hoperation).symm)

/-- Cells referenced by one copy-like layouter operation. -/
def Operation.copiedCells : Operation F → List Cell
  | .region _ body => body.copiedCells
  | .constrainInstance cell _ _ => [cell]
  | .loadTable _ _ => []

/-- Cells referenced by every copy-like operation in a layouter stream. -/
def Operations.copiedCells (operations : Operations F) : List Cell :=
  operations.flatMap Operation.copiedCells

/-- A layouter stream containing no copy-like operation is copy-lawful for every incoming
cell state. -/
@[keygen_helper]
theorem Operations.copyCellsAssignedFrom_of_forall_copiedCells_eq_nil
    (operations : Operations F) (region : RegionIndex)
    (available : List Cell)
    (hoperations : operations.Forall fun operation =>
      operation.copiedCells = []) :
    operations.AssignedFrom RegionOperation.Copies region available := by
  induction operations generalizing region available with
  | nil => exact .nil region available
  | cons operation rest inductionHypothesis =>
      rw [List.forall_cons] at hoperations
      cases operation with
      | region name body =>
          apply Operations.AssignedFrom.region region available name body rest
          · apply RegionOperations.copyCellsAssignedFrom_of_forall_copiedCells_eq_nil
            rw [List.forall_iff_forall_mem]
            simpa only [Operation.copiedCells, RegionOperations.copiedCells,
              List.flatMap_eq_nil_iff] using hoperations.1
          · exact inductionHypothesis (region := region + 1)
              (available := body.assignedCellsAfter region available) hoperations.2
      | constrainInstance cell column row =>
          simp only [Operation.copiedCells, List.cons_ne_nil] at hoperations
          exact False.elim hoperations.1
      | loadTable column values =>
          exact .loadTable region available column values rest
            (inductionHypothesis (region := region) (available := available)
              hoperations.2)

def Operations.CopyCellsAssigned (operations : Operations F)
    (initialRegion : RegionIndex) (inputCells : List Cell) : Prop :=
  AssignedFrom RegionOperation.Copies initialRegion inputCells operations

/-- Set-level consequence used by compiler proofs. -/
def Operations.CopyCellsCovered (operations : Operations F)
    (initialRegion : RegionIndex) (inputCells : List Cell) : Prop :=
  ∀ cell ∈ operations.copiedCells,
    cell ∈ inputCells ++ operations.assignedCellsFrom initialRegion

/-- Provenance for a relation under which every copy-like operation consumes at least its
endpoints yields the set-level copy coverage. -/
theorem RegionOperations.copyCellsCovered_of_assignedFrom
    {consumption : Consumption F}
    (hcopies : ∀ operation cells, consumption operation cells →
      ∀ cell ∈ operation.copiedCells, cell ∈ cells)
    (operations : RegionOperations F) (region : RegionIndex)
    (available : List Cell)
    (hassigned : operations.AssignedFrom consumption region available) :
    operations.CopyCellsCovered region available := by
  induction operations generalizing available with
  | nil => simp [CopyCellsCovered, copiedCells]
  | cons operation rest inductionHypothesis =>
      rw [assignedFrom_cons_iff] at hassigned
      obtain ⟨⟨cells, hconsumes, havailable⟩, hrest⟩ := hassigned
      intro cell hcell
      simp only [copiedCells, List.flatMap_cons, List.mem_append] at hcell
      simp only [assignedCells, List.flatMap_cons, List.mem_append]
      rcases hcell with hcurrent | hcell
      · exact Or.inl (havailable cell (hcopies operation cells hconsumes cell hcurrent))
      · have hcovered := inductionHypothesis _ hrest cell hcell
        simp only [List.mem_append] at hcovered
        tauto

theorem Operations.copyCellsCovered_of_assignedFrom
    {consumption : Consumption F}
    (hcopies : ∀ operation cells, consumption operation cells →
      ∀ cell ∈ operation.copiedCells, cell ∈ cells)
    (operations : Operations F) (initialRegion : RegionIndex)
    (available : List Cell)
    (hassigned : AssignedFrom consumption initialRegion available operations) :
    operations.CopyCellsCovered initialRegion available := by
  induction operations generalizing initialRegion available with
  | nil => simp [CopyCellsCovered, Operations.copiedCells]
  | cons operation rest inductionHypothesis =>
      cases operation with
      | region name body =>
          intro cell hcell
          rw [assignedFrom_region_iff] at hassigned
          rw [Operations.copiedCells, List.mem_flatMap] at hcell
          rcases hcell with ⟨candidate, hcandidate, hcell⟩
          rw [List.mem_cons] at hcandidate
          rcases hcandidate with rfl | hrest
          · have hcovered := RegionOperations.copyCellsCovered_of_assignedFrom hcopies body
              initialRegion available hassigned.1 cell hcell
            rw [List.mem_append] at hcovered
            rw [Operations.assignedCellsFrom, List.mem_append]
            exact Or.imp_right (fun hbody => List.mem_append_left _ hbody) hcovered
          · have hcovered := inductionHypothesis (initialRegion + 1)
              (body.assignedCellsAfter initialRegion available)
              hassigned.2 cell (List.mem_flatMap.mpr ⟨candidate, hrest, hcell⟩)
            rw [List.mem_append] at hcovered
            rw [Operations.assignedCellsFrom, List.mem_append]
            rcases hcovered with hafter | hrestAssigned
            · rw [body.mem_assignedCellsAfter_iff] at hafter
              rw [List.mem_append] at hafter
              exact Or.imp_right (List.mem_append_left _) hafter
            · exact Or.inr (List.mem_append_right _ hrestAssigned)
      | constrainInstance copied column row =>
          intro cell hcell
          rw [Operations.assignedFrom_constrainInstance_iff] at hassigned
          rw [Operations.copiedCells, List.mem_flatMap] at hcell
          rcases hcell with ⟨candidate, hcandidate, hcell⟩
          rw [List.mem_cons] at hcandidate
          rcases hcandidate with rfl | hrest
          · simp only [Operation.copiedCells, List.mem_singleton] at hcell
            subst cell
            exact List.mem_append_left _ hassigned.1
          · exact inductionHypothesis initialRegion available hassigned.2 cell
              (List.mem_flatMap.mpr ⟨candidate, hrest, hcell⟩)
      | loadTable column values =>
          cases hassigned with
          | loadTable _ _ _ _ _ hassignedRest =>
            exact inductionHypothesis initialRegion available hassignedRest

theorem Operations.copyCellsCovered_of_assigned
    (operations : Operations F) (initialRegion : RegionIndex)
    (inputCells : List Cell)
    (hassigned : operations.CopyCellsAssigned initialRegion inputCells) :
    operations.CopyCellsCovered initialRegion inputCells :=
  operations.copyCellsCovered_of_assignedFrom RegionOperation.copiedCells_subset_of_copies
    initialRegion inputCells hassigned

end Halo2
