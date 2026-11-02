import Repair.EndpointTemplateData

/-! The same actual local template family now produces the original global
linear decomposition, its open positive fiber neighborhood and its uniform
reserve. Neither the linear identity nor a positive-domain output is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Bundle
open scoped BigOperators ContDiff
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,D)
local notation "Edge" => EdgePair (Module.finrank ℝ D+1)

private local instance repairDecompBilinGroup (x : M) :
    AddCommGroup (LinearMap.BilinForm ℝ (TangentSpace IT x)) := LinearMap.addCommGroup

variable {Host : Type*} [Fintype Host] {Piece : Host → Type*} [∀ i, Fintype (Piece i)]

/-- Exact reconstruction by every actual local template, before any positivity
restriction, followed by the actual squared refinement partition. -/
theorem repair_host_refinement_linear_reconstruction
    (host : OpenPartialHomeomorph M D)
    (hhost : host ∈ IsManifold.maximalAtlas IT ∞ M)
    {Local : Type*} [Fintype Local]
    (template : Local → ActualGoodDictionaryTemplate D V)
    (chi : Local → ℝ) (hpart : ∑ q, chi q ^ 2 = 1)
    (x : M) (hx : x ∈ host.source)
    (A : LinearMap.BilinForm ℝ (TangentSpace IT x)) (hA : A.IsSymm) :
    (∑ a : Local × Edge,
      (chi a.1 ^ 2 * repairHostTemplateArgument host hhost (template a.1) a.2 x A) •
        LinearMap.BilinForm.comp (LinearMap.mul ℝ ℝ)
          (round4HostPhaseCovector host ((template a.1).covectors a.2) x).toLinearMap
          (round4HostPhaseCovector host ((template a.1).covectors a.2) x).toLinearMap) = A := by
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ q, chi q ^ 2 •
      (∑ a, repairHostTemplateArgument host hhost (template q) a x A •
        LinearMap.BilinForm.comp (LinearMap.mul ℝ ℝ)
          (round4HostPhaseCovector host ((template q).covectors a) x).toLinearMap
          (round4HostPhaseCovector host ((template q).covectors a) x).toLinearMap) := by
      apply Finset.sum_congr rfl
      intro q _
      simp only [Finset.smul_sum, smul_smul]
    _ = ∑ q, chi q ^ 2 • A := by
      apply Finset.sum_congr rfl
      intro q _
      rw [← repair_host_template_linear_reconstruction host hhost (template q) x hx A hA]
    _ = (∑ q, chi q ^ 2) • A := (Finset.sum_smul ..).symm
    _ = A := by rw [hpart, one_smul]

/-- Production of the original decomposition records for the fully constructed
native reference datum. The same actual host cutoffs and local refinements are
retained; no estimate depends on the total number of charts. -/
theorem repair_original_template_positive_decomposition
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (host : Host → OpenPartialHomeomorph M D)
    (hhost : ∀ i, host i ∈ IsManifold.maximalAtlas IT ∞ M)
    (template : ∀ i, Piece i → ActualGoodDictionaryTemplate D V)
    (outer : Host → P × M → ℝ) (inner : ∀ i, Piece i → P × M → ℝ)
    (normal : (Σ i, Piece i × Edge) → P × M → V)
    (domain : (Σ i, Piece i × Edge) → Set (P × M))
    (rho : ℝ) (hrho : 0 < rho)
    (hreserve : ∀ i q, rho < (template i q).coefficientReserve)
    (houter : ∀ p ∈ seed.parameterOpen, ∀ x, ∑ i, outer i (p,x)^2 = 1)
    (hinner : ∀ p ∈ seed.parameterOpen, ∀ x i, outer i (p,x) ≠ 0 →
      ∑ q, inner i q (p,x)^2 = 1)
    (hsource : ∀ p ∈ seed.parameterOpen, ∀ x i, outer i (p,x) ≠ 0 → x ∈ (host i).source)
    (hTensor : ∀ nu z,
      z ∈ incrementsOriginalRelativeCutoffSupport
        (repairOriginalTemplateData seed host hhost template outer inner normal domain) nu →
      let a := repairTemplateIndex (m := m) (Piece := Piece) nu
      repairNativeTensorPullback (repairHostTensorInverse (host a.1) (hhost a.1) z.2)
        (inducedMetric (I := IT) (fun y => seed.F0 (z.1,y)) z.2) ∈
        (template a.1 a.2.1).tensorDomain) :
    let data := repairReferencePositiveData
      (repairOriginalTemplateData seed host hhost template outer inner normal domain) rho
    IncrementsOriginalQualitativeDecompositionInputs data ∧
      IncrementsOriginalDecompositionReserveInputs data rho := by
  intro data
  let raw := repairOriginalTemplateData seed host hhost template outer inner normal domain
  apply repair_reference_positive_from_local_dictionaries raw rho hrho rfl
    (fun p _ x => (inducedMetric_isPosSemidef (I := IT) (fun y => seed.F0 (p,y)) x).isSymm)
    ?_ (repairTemplateIndex (m := m) (Piece := Piece)) outer
    (fun a z => inner a.1 a.2.1 z) (fun _ _ => rfl) houter ?_
  · intro p hp x nu hnu
    let a := repairTemplateIndex (m := m) (Piece := Piece) nu
    exact (hreserve a.1 a.2.1).trans_le
      (repair_host_template_reserve (host a.1) (hhost a.1) (template a.1 a.2.1) x
        (inducedMetric (I := IT) (fun y => seed.F0 (p,y)) x)
        (hTensor nu (p,x) hnu) a.2.2)
  · intro p hp x i hi A
    have h := repair_host_refinement_linear_reconstruction (host i) (hhost i)
      (template i) (fun q => inner i q (p,x)) (hinner p hp x i hi)
      x (hsource p hp x i hi) A.val A.property
    let e := repairTemplateIndex (m := m) (Piece := Piece)
    change (∑ a : Piece i × Edge,
      (inner i a.1 (p,x)^2 *
        repairHostTemplateArgument (host (e (e.symm ⟨i,a⟩)).1)
          (hhost (e (e.symm ⟨i,a⟩)).1)
          (template (e (e.symm ⟨i,a⟩)).1 (e (e.symm ⟨i,a⟩)).2.1)
          (e (e.symm ⟨i,a⟩)).2.2 x A.val) •
      LinearMap.BilinForm.comp (LinearMap.mul ℝ ℝ)
        (round4HostPhaseCovector (host (e (e.symm ⟨i,a⟩)).1)
          ((template (e (e.symm ⟨i,a⟩)).1 (e (e.symm ⟨i,a⟩)).2.1).covectors
            (e (e.symm ⟨i,a⟩)).2.2) x).toLinearMap
        (round4HostPhaseCovector (host (e (e.symm ⟨i,a⟩)).1)
          ((template (e (e.symm ⟨i,a⟩)).1 (e (e.symm ⟨i,a⟩)).2.1).covectors
            (e (e.symm ⟨i,a⟩)).2.2) x).toLinearMap) = A.val
    calc
      _ = ∑ a : Piece i × Edge,
        (inner i a.1 (p,x)^2 * repairHostTemplateArgument (host i) (hhost i)
          (template i a.1) a.2 x A.val) •
        LinearMap.BilinForm.comp (LinearMap.mul ℝ ℝ)
          (round4HostPhaseCovector (host i) ((template i a.1).covectors a.2) x).toLinearMap
          (round4HostPhaseCovector (host i) ((template i a.1).covectors a.2) x).toLinearMap := by
        apply Finset.sum_congr rfl
        intro a _
        exact congrArg (fun b : (Σ i, Piece i × Edge) =>
          (inner i a.1 (p,x)^2 * repairHostTemplateArgument (host b.1) (hhost b.1)
            (template b.1 b.2.1) b.2.2 x A.val) •
          LinearMap.BilinForm.comp (LinearMap.mul ℝ ℝ)
            (round4HostPhaseCovector (host b.1) ((template b.1 b.2.1).covectors b.2.2) x).toLinearMap
            (round4HostPhaseCovector (host b.1) ((template b.1 b.2.1).covectors b.2.2) x).toLinearMap)
          (e.apply_symm_apply ⟨i,a⟩)
      _ = A.val := h

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_original_template_positive_decomposition

