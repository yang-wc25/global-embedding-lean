import Repair.EndpointPositiveNeighborhood

/-!
# Local finite dictionaries assemble the original global decomposition

The actual global cutoff is the product of its normalized host cutoff and
the local refinement cutoff. A finite dependent sum retains every original
piece; no chart-count multiplier is inserted into the reconstruction. The
result produces the original positive-decomposition and reserve records in
the native tangent fibers, with the open neighborhood constructed explicitly.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set
open scoped BigOperators
namespace GlobalEmbedding.Continuation

theorem repair_finite_dictionary_partition
    {E Host : Type*} [AddCommGroup E] [Module ℝ E] [Fintype Host]
    {Piece : Host → Type*} [∀ i, Fintype (Piece i)]
    (A : E) (outer : Host → ℝ)
    (inner : (Σ i, Piece i) → ℝ)
    (argument : (Σ i, Piece i) → ℝ)
    (square : (Σ i, Piece i) → E)
    (houter : ∑ i, outer i ^ 2 = 1)
    (hlocal : ∀ i, outer i ≠ 0 →
      (∑ a : Piece i, (inner ⟨i,a⟩ ^ 2 * argument ⟨i,a⟩) • square ⟨i,a⟩) = A) :
    (∑ a : (Σ i, Piece i),
      ((outer a.1 * inner a)^2 * argument a) • square a) = A := by
  classical
  rw [Fintype.sum_sigma]
  calc
    (∑ i, ∑ a : Piece i,
      ((outer i * inner ⟨i,a⟩)^2 * argument ⟨i,a⟩) • square ⟨i,a⟩) =
        ∑ i, outer i ^ 2 •
          (∑ a : Piece i, (inner ⟨i,a⟩ ^ 2 * argument ⟨i,a⟩) • square ⟨i,a⟩) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finset.smul_sum, smul_smul, mul_pow, mul_assoc]
    _ = ∑ i, outer i ^ 2 • A := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : outer i = 0
      · simp [hi]
      · rw [hlocal i hi]
    _ = (∑ i, outer i ^ 2) • A := (Finset.sum_smul ..).symm
    _ = A := by rw [houter, one_smul]

variable {n d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace P]
local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

/-- The actual local template identities and squared host partition supply
the original whole-source reference decomposition, including its constructed
open positive neighborhood and numerical reserve on joint cutoff supports. -/
theorem repair_reference_positive_from_local_dictionaries
    (D : IncrementsOriginalNativeData n d N M P)
    (rho : ℝ) (hrho : 0 < rho)
    (hH : D.H = D.reference)
    (hSym : ∀ p ∈ D.parameterOpen, ∀ x, (D.reference p x).IsSymm)
    (hReference : ∀ p ∈ D.parameterOpen, ∀ x ν,
      (p,x) ∈ incrementsOriginalRelativeCutoffSupport D ν →
      rho < D.linearArgument ν p x (D.reference p x))
    {Host : Type*} [Fintype Host] {Piece : Host → Type*} [∀ i, Fintype (Piece i)]
    (index : Fin D.primaryCount ≃ (Σ i, Piece i))
    (outer : Host → P × M → ℝ)
    (inner : (Σ i, Piece i) → P × M → ℝ)
    (hcutoff : ∀ ν z, D.cutoff ν z = outer (index ν).1 z * inner (index ν) z)
    (hpartition : ∀ p ∈ D.parameterOpen, ∀ x, ∑ i, outer i (p,x)^2 = 1)
    (hlocal : ∀ p ∈ D.parameterOpen, ∀ x i, outer i (p,x) ≠ 0 →
      ∀ A : {A : LinearMap.BilinForm ℝ (TangentSpace I x) // A.IsSymm},
        (∑ a : Piece i,
          (inner ⟨i,a⟩ (p,x)^2 * D.linearArgument (index.symm ⟨i,a⟩) p x A.val) •
            incrementsOriginalPhaseSquare D (index.symm ⟨i,a⟩) p x) = A.val) :
    IncrementsOriginalQualitativeDecompositionInputs (repairReferencePositiveData D rho) ∧
    IncrementsOriginalDecompositionReserveInputs (repairReferencePositiveData D rho) rho := by
  apply repair_reference_positive_decomposition D rho hrho hH hSym hReference
  intro p hp x A
  have h := repair_finite_dictionary_partition A.val (fun i => outer i (p,x))
    (fun a => inner a (p,x)) (fun a => D.linearArgument (index.symm a) p x A.val)
    (fun a => incrementsOriginalPhaseSquare D (index.symm a) p x)
    (hpartition p hp x) (fun i hi => hlocal p hp x i hi A)
  calc
    A.val = ∑ a : (Σ i, Piece i),
      ((outer a.1 (p,x) * inner a (p,x))^2 *
        D.linearArgument (index.symm a) p x A.val) •
          incrementsOriginalPhaseSquare D (index.symm a) p x := h.symm
    _ = ∑ ν, (D.cutoff ν (p,x)^2 * D.linearArgument ν p x A.val) •
        incrementsOriginalPhaseSquare D ν p x := by
      rw [← Equiv.sum_comp index]
      apply Finset.sum_congr rfl
      intro ν _
      rw [index.symm_apply_apply, hcutoff]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_reference_positive_from_local_dictionaries

