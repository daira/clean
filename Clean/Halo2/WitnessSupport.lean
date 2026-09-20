import Clean.Circuit.WitnessReads
import Clean.Halo2.WitnessSupportAttr
import Clean.Halo2.Basic

/-!
# Semantic read support for witness programs

Native callbacks are ordinary functions, so their dependencies cannot be inferred by the
structured IR collector. `WitnessFunctionSupport reads compute` certifies the function
itself: equal immutable context data and equal listed cell values imply equal results. It
composes through arbitrary deterministic arithmetic on those results. The rules tagged
`witness_support` cover the program shapes Clean itself produces; a downstream project tags
the rules for its own callbacks.
-/

namespace Halo2

open Witgen

variable {F : Type} [FiniteField F]

/-- Declared cell values and the immutable public/fixed environment agree. -/
structure WitnessFunctionAgreement
    (reads : List (AssignedCell F)) (left right : Placed ProverEnvironment F) : Prop extends
    WitnessContextAgreement reads
      ({ env := left } : CtxOver F (Placed ProverEnvironment F)) { env := right } where
  nonAdvice : ∀ column row, column.kind ≠ .advice →
    left.env.get column row = right.env.get column row

/-- Structured IR uses the context part of native-function agreement. -/
instance witnessFunctionAgreementCoe
    {reads : List (AssignedCell F)} {left right : Placed ProverEnvironment F} :
    Coe (WitnessFunctionAgreement reads left right)
      (WitnessContextAgreement reads
        ({ env := left } : CtxOver F (Placed ProverEnvironment F)) { env := right }) :=
  ⟨WitnessFunctionAgreement.toWitnessContextAgreement⟩

/-- Restrict declared reads while retaining all immutable values. -/
theorem WitnessFunctionAgreement.mono
    {reads smaller : List (AssignedCell F)} {left right : Placed ProverEnvironment F}
    (agreement : WitnessFunctionAgreement reads left right) (hsubset : smaller ⊆ reads) :
    WitnessFunctionAgreement smaller left right :=
  ⟨agreement.toWitnessContextAgreement.mono hsubset, agreement.nonAdvice⟩

/-- Restrict a concatenated support to its first component. -/
theorem WitnessFunctionAgreement.left
    {first second : List (AssignedCell F)} {left right : Placed ProverEnvironment F}
    (agreement : WitnessFunctionAgreement (first ++ second) left right) :
    WitnessFunctionAgreement first left right :=
  agreement.mono (List.subset_append_left _ _)

/-- Restrict a concatenated support to its second component. -/
theorem WitnessFunctionAgreement.right
    {first second : List (AssignedCell F)} {left right : Placed ProverEnvironment F}
    (agreement : WitnessFunctionAgreement (first ++ second) left right) :
    WitnessFunctionAgreement second left right :=
  agreement.mono (List.subset_append_right _ _)

/-- The declared cell reads and immutable context determine the callback's result. -/
def WitnessFunctionSupport {Value : Type}
    (reads : List (AssignedCell F)) (compute : Placed ProverEnvironment F → Value) : Prop :=
  ∀ left right, WitnessFunctionAgreement reads left right → compute left = compute right

/-- Enlarging the declared read set preserves a semantic support certificate. -/
theorem WitnessFunctionSupport.mono {Value : Type}
    {reads larger : List (AssignedCell F)} {compute : Placed ProverEnvironment F → Value}
    (support : WitnessFunctionSupport reads compute) (hincluded : reads ⊆ larger) :
    WitnessFunctionSupport larger compute :=
  fun left right agreement => support left right (agreement.mono hincluded)

/-- A deterministic function of supported data introduces no additional environment read. -/
theorem WitnessFunctionSupport.map {Value Result : Type}
    {reads : List (AssignedCell F)} {compute : Placed ProverEnvironment F → Value}
    (support : WitnessFunctionSupport reads compute) (f : Value → Result) :
    WitnessFunctionSupport reads (fun env => f (compute env)) :=
  fun left right agreement => congrArg f (support left right agreement)

/-- Pair two supported computations using the concatenation of their read sets. -/
theorem WitnessFunctionSupport.pair {Left Right : Type}
    {leftReads rightReads : List (AssignedCell F)}
    {leftCompute : Placed ProverEnvironment F → Left}
    {rightCompute : Placed ProverEnvironment F → Right}
    (leftSupport : WitnessFunctionSupport leftReads leftCompute)
    (rightSupport : WitnessFunctionSupport rightReads rightCompute) :
    WitnessFunctionSupport (leftReads ++ rightReads)
      (fun env => (leftCompute env, rightCompute env)) :=
  fun left right agreement => Prod.ext
    (leftSupport left right agreement.left) (rightSupport left right agreement.right)

/-! ## The rules for Clean's own program shapes -/

/-- Reading one assigned cell has exactly that cell as a sufficient support. -/
@[witness_support]
theorem witnessFunctionSupport_readCell (cell : AssignedCell F) :
    WitnessFunctionSupport [cell] (fun env => readCell env cell) :=
  fun _ _ agreement => agreement.cellValues cell (List.mem_singleton_self _)

/-- Absolute instance reads depend only on immutable public input, with no advice
dependency. -/
@[witness_support]
theorem witnessFunctionSupport_instanceGet (column : Column .instance) (row : ℕ) :
    WitnessFunctionSupport (F := F) [] (fun env => ((instanceGet column row).eval env)[0]) := by
  intro left right agreement
  dsimp only
  rw [eval_instanceGet, eval_instanceGet]
  exact agreement.nonAdvice column.toAny (row : ℤ)
    (by change ColumnKind.instance ≠ ColumnKind.advice; decide)

/-- A field-expression program reads only the cells in its syntax. -/
@[witness_support]
theorem witnessFunctionSupport_ofFExpr (expression : FExpr F) :
    WitnessFunctionSupport (fieldWitnessReads expression)
      (fun env => ((WitgenIROver.ofFExpr expression : WitgenIR F 1).eval env)[0]) := by
  intro left right agreement
  dsimp only
  rw [eval_ofFExpr_zero, eval_ofFExpr_zero]
  exact fieldWitnessReads_eval expression { env := left } { env := right } agreement

/-- A structured program reads the cells of its local steps and its output. -/
@[witness_support]
theorem witnessFunctionSupport_structured (steps : List (StepOver F (AssignedCell F)))
    (output : VExprOver F (AssignedCell F) 1) :
    WitnessFunctionSupport (stepsWitnessReads steps ++ vectorWitnessReads output)
      (fun env => ((WitgenIROver.ir steps output : WitgenIR F 1).eval env)[0]) :=
  fun left right agreement => congrArg (fun values : Vector F 1 => values[0])
    (structuredWitnessReads_eval steps output left right agreement.toWitnessContextAgreement)

/-- The scalar program emitted by a builder reads exactly the builder's support. -/
@[witness_support]
theorem witnessFunctionSupport_scalarBuilder (program : MOver F (AssignedCell F) (FExpr F)) :
    WitnessFunctionSupport (valueBuilderReads (value := field) program)
      (fun env => ((program.toIRScalar (Env := Placed ProverEnvironment F)).eval env)[0]) := by
  intro left right agreement
  dsimp only
  simp only [MOver.eval_toIRScalar]
  exact valueBuilderReads_eval (value := field) program left right agreement

/-- Structured field or record builders supply a support for native callers. -/
@[witness_support]
theorem witnessFunctionSupport_valueBuilder {value : TypeMap} [ProvableType value]
    (program : MOver F (AssignedCell F) (value (FExpr F))) :
    WitnessFunctionSupport (valueBuilderReads program) (fun env => program.eval env) :=
  fun left right agreement => valueBuilderReads_eval program left right agreement

/-- Native callers of a structured Nat builder inherit all its collected reads. -/
@[witness_support]
theorem witnessFunctionSupport_natBuilder (program : MOver F (AssignedCell F) (NExpr F)) :
    WitnessFunctionSupport (natBuilderReads program) (fun env => program.evalNat env) :=
  fun left right agreement => natBuilderReads_eval program left right agreement

/-- Native callers of a structured Boolean builder inherit all its collected reads. -/
@[witness_support]
theorem witnessFunctionSupport_boolBuilder (program : MOver F (AssignedCell F) (BExpr F)) :
    WitnessFunctionSupport (boolBuilderReads program) (fun env => program.evalBool env) :=
  fun left right agreement => boolBuilderReads_eval program left right agreement

/-- A fixed value does not need any cell read. Last among the rules, since it matches any
program whose evaluation unfolds to a constant. -/
@[witness_support]
theorem witnessFunctionSupport_const {Value : Type} (value : Value) :
    WitnessFunctionSupport (F := F) [] (fun _ => value) := fun _ _ _ => rfl

end Halo2
