import GlobalEmbedding.Paper.IncrementsOriginalDecompositionExtension
import GlobalEmbedding.Paper.IncrementsOriginalReserveInputs
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The original open positive neighborhood from the actual reference dictionary

The neighborhood is constructed in the original symmetric tangent fiber.
Only coefficients on the actual relative joint cutoff supports are constrained.
All of its openness, reference membership, positive square-root arguments and
uniform reserve are proved. No neighborhood or positive-domain check is supplied
as an output assumption. The linear reconstruction input is the finite dictionary
identity; a squared-partition producer is supplied separately.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set
open scoped BigOperators
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace P]
local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

private local instance repairBilinAddCommGroup (x : M) :
    AddCommGroup (LinearMap.BilinForm ℝ (TangentSpace I x)) := LinearMap.addCommGroup

/-- Every original linear tensor functional is continuous on the original
point-evaluation topology of the symmetric fiber. No tensor norm is changed. -/
theorem repair_original_fiber_linear_continuous (x : M)
    (L : LinearMap.BilinForm ℝ (TangentSpace I x) →ₗ[ℝ] ℝ) :
    let _ := incrementsOriginalSymmetricFiberTopology (n := n) x
    Continuous (fun A : {A : LinearMap.BilinForm ℝ (TangentSpace I x) // A.IsSymm} =>
      L A.val) := by
  let _ := incrementsOriginalSymmetricFiberTopology (n := n) x
  let K := LinearMap.eqLocus (LinearMap.BilinForm.flipHom (R := ℝ)
      (M := TangentSpace I x)).toLinearMap
      (LinearMap.id : Module.End ℝ (LinearMap.BilinForm ℝ (TangentSpace I x)))
  let _ : AddCommGroup K := Submodule.addCommGroup K
  let _ : TopologicalSpace K := incrementsOriginalSymmetricEqLocusTopology (n := n) x
  let ev : K →ₗ[ℝ] (TangentSpace I x → TangentSpace I x → ℝ) :=
    { toFun := fun A v w => A.val v w
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    intro A B h
    apply Subtype.ext
    ext v w
    exact congrFun (congrFun h v) w
  let _ : T2Space K := T2Space.of_injective_continuous hinj continuous_induced_dom
  have hc := incrementsOriginal_symmetricEqLocus_continuousModule (n := n) x
  let _ : ContinuousAdd K := hc.1
  let _ : ContinuousSMul ℝ K := hc.2
  let _ : ContinuousNeg K := ⟨by
    simpa only [neg_one_smul] using
      (continuous_const_smul (-1 : ℝ) : Continuous (fun a : K => (-1 : ℝ) • a))⟩
  let _ : IsTopologicalAddGroup K := ⟨⟩
  let f : K →ₗ[ℝ] ℝ :=
    { toFun := fun A => L A.val
      map_add' := fun A B => L.map_add A.val B.val
      map_smul' := fun r A => L.map_smul r A.val }
  exact f.continuous_of_finiteDimensional.comp
    (incrementsOriginalSymmetricFiberEqLocusHomeomorph (n := n) x).continuous

def repairReferencePositiveNeighborhood
    (D : IncrementsOriginalNativeData n d N M P) (rho : ℝ) (p : P) (x : M) :
    Set {A : LinearMap.BilinForm ℝ (TangentSpace I x) // A.IsSymm} :=
  {A | ∀ ν, (p,x) ∈ incrementsOriginalRelativeCutoffSupport D ν →
    rho < D.linearArgument ν p x A.val}

def repairReferencePositiveData
    (D : IncrementsOriginalNativeData n d N M P) (rho : ℝ) :
    IncrementsOriginalNativeData n d N M P :=
  { D with tensorNeighborhood := repairReferencePositiveNeighborhood D rho }

theorem repair_reference_positive_neighborhood_open
    (D : IncrementsOriginalNativeData n d N M P) (rho : ℝ) (p : P) (x : M) :
    @IsOpen _ (incrementsOriginalSymmetricFiberTopology (n := n) x)
      (repairReferencePositiveNeighborhood D rho p x) := by
  let _ := incrementsOriginalSymmetricFiberTopology (n := n) x
  change IsOpen {A : {A : LinearMap.BilinForm ℝ (TangentSpace I x) // A.IsSymm} |
    ∀ ν, (p,x) ∈ incrementsOriginalRelativeCutoffSupport D ν →
    rho < D.linearArgument ν p x A.val}
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro ν
  have hopen : IsOpen {A : {A : LinearMap.BilinForm ℝ (TangentSpace I x) // A.IsSymm} |
      rho < D.linearArgument ν p x A.val} :=
    isOpen_lt continuous_const (repair_original_fiber_linear_continuous x (D.linearArgument ν p x))
  by_cases h : (p,x) ∈ incrementsOriginalRelativeCutoffSupport D ν
  · simpa [h] using hopen
  · simp [h]

theorem repair_original_nonzero_cutoff_mem_relative
    (D : IncrementsOriginalNativeData n d N M P) (p : P)
    (hp : p ∈ D.parameterOpen) (x : M) (ν : Fin D.primaryCount)
    (hcut : D.cutoff ν (p,x) ≠ 0) :
    (p,x) ∈ incrementsOriginalRelativeCutoffSupport D ν := by
  let z : incrementsOriginalParameterRegion D := ⟨(p,x), hp, mem_univ x⟩
  exact ⟨z, subset_tsupport _ hcut, rfl⟩

/-- Supply the two original positive-decomposition records from the actual
linear rank-one identity and a strict reserve at the reference tensor.
The same native H/reference fields and all original domains are retained. -/
theorem repair_reference_positive_decomposition
    (D : IncrementsOriginalNativeData n d N M P)
    (rho : ℝ) (hrho : 0 < rho)
    (hH : D.H = D.reference)
    (hSym : ∀ p ∈ D.parameterOpen, ∀ x, (D.reference p x).IsSymm)
    (hReference : ∀ p ∈ D.parameterOpen, ∀ x ν,
      (p,x) ∈ incrementsOriginalRelativeCutoffSupport D ν →
      rho < D.linearArgument ν p x (D.reference p x))
    (hLinear : ∀ p ∈ D.parameterOpen, ∀ x
      (A : {A : LinearMap.BilinForm ℝ (TangentSpace I x) // A.IsSymm}),
      A.val = ∑ ν, (D.cutoff ν (p,x)^2 * D.linearArgument ν p x A.val) •
        incrementsOriginalPhaseSquare D ν p x) :
    IncrementsOriginalQualitativeDecompositionInputs (repairReferencePositiveData D rho) ∧
    IncrementsOriginalDecompositionReserveInputs (repairReferencePositiveData D rho) rho := by
  let E := repairReferencePositiveData D rho
  have hHSym : ∀ p ∈ E.parameterOpen, ∀ x, (E.H p x).IsSymm := by
    intro p hp x
    change (D.H p x).IsSymm
    rw [hH]
    exact hSym p hp x
  constructor
  · refine ⟨fun p _ x => repair_reference_positive_neighborhood_open D rho p x,
      hHSym, hSym, ?_, ?_, ?_, ?_⟩
    · intro p hp x
      change ∀ ν, (p,x) ∈ incrementsOriginalRelativeCutoffSupport D ν →
        rho < D.linearArgument ν p x (D.H p x)
      rw [hH]
      exact hReference p hp x
    · intro p hp x
      exact hReference p hp x
    · intro p hp x A hA
      apply (hLinear p hp x A).trans
      apply Finset.sum_congr rfl
      intro ν _
      change (D.cutoff ν (p,x)^2 * D.linearArgument ν p x A.val) •
        incrementsOriginalPhaseSquare D ν p x =
        (D.cutoff ν (p,x) * Real.sqrt (D.linearArgument ν p x A.val))^2 •
          incrementsOriginalPhaseSquare D ν p x
      by_cases hc : D.cutoff ν (p,x) = 0
      · simp [hc]
      · have hpos := hA ν (repair_original_nonzero_cutoff_mem_relative D p hp x ν hc)
        rw [mul_pow, Real.sq_sqrt (hrho.trans hpos).le]
    · intro p hp x ν hc A hA
      exact hrho.trans (hA ν (repair_original_nonzero_cutoff_mem_relative D p hp x ν hc))
  · refine ⟨hrho, ?_⟩
    intro ν z hz _ A hA
    exact (hA ν hz).le

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_original_fiber_linear_continuous
#print axioms GlobalEmbedding.Continuation.repair_reference_positive_decomposition

