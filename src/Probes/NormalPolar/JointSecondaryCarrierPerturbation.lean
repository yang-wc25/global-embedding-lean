import NormalPolar.JointSecondaryNativePerturbation
import NormalPolar.JointSecondarySignedRefinement
import GlobalEmbedding.Offline.UniformHierarchicalGoodPhases
import GlobalEmbedding.Paper.GoodCovectorRescaling

/-! A genuine compact original carrier has a uniform scalar perturbation
radius. The finite charts and their ordinary partition are manufactured
internally from the original noncritical phase. No one-chart carrier or
uniform native Good ball is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

theorem jointSecondary_compact_carrier_phase_perturbation
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (hImm : ∀ x, Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (psi phi : M → ℝ) (C O : Set M) (hC : IsClosed C)
    (hO : IsOpen O) (hCO : C ⊆ O)
    (hpsi : ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ psi O)
    (hphi : ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ phi O)
    (hgood : ∀ x ∈ C, GoodCovector F hF x (mfderiv IM 𝓘(ℝ,ℝ) psi x)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ t : ℝ, |t| < epsilon → ∀ x ∈ C,
      GoodCovector F hF x
        (jointSecondaryPhaseCovector psi x + t • jointSecondaryPhaseCovector phi x) := by
  obtain ⟨d⟩ := jointSecondary_exists_signed_refinement psi C O hC hO hCO hpsi
    (fun x hx => (hgood x hx).1)
  choose epsilon heps hpert using fun i : Fin d.count =>
    jointSecondary_native_compact_phase_perturbation F hF hImm psi phi O hO hpsi hphi
      (d.chart i) (d.maximal i) (d.source_domain i)
      (C ∩ tsupport (d.cutoff i)) (hC.isCompact.inter_right (isClosed_tsupport _))
      (fun _ hx => d.cutoff_support i hx.2) (fun x hx => hgood x hx.1)
  obtain ⟨eps,heps0,hle⟩ := finite_positive_common_lower_bound epsilon heps
  refine ⟨eps,heps0,?_⟩
  intro t ht x hx
  have hsome : ∃ i : Fin d.count, d.cutoff i x ≠ 0 := by
    by_contra! hz
    have hsum := d.partition x hx
    simp only [hz,Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  obtain ⟨i,hi⟩ := hsome
  exact hpert i t (ht.trans_le (hle i)) x
    ⟨hx,subset_tsupport (d.cutoff i) (Function.mem_support.mpr hi)⟩

theorem jointSecondary_original_good_smul_iff
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F) (x : M)
    (xi : TangentSpace IM x →L[ℝ] ℝ) (c : ℝ) (hc : c ≠ 0) :
    GoodCovector F hF x (c • xi) ↔ GoodCovector F hF x xi :=
  good_covector_smul_iff F hF x xi c hc

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_compact_carrier_phase_perturbation
#print axioms GlobalEmbedding.Continuation.jointSecondary_original_good_smul_iff
