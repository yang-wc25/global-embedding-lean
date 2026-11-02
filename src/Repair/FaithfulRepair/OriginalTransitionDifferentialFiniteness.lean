import FaithfulRepair.OriginalTransitionFiniteness

/-! Finiteness of the SAME original transition differential profile follows
from the original next transition jets.  This does not use the desired
given-input-profile finiteness in reverse. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation.FaithfulRepair

/-- Literal matrix entries of the actual derivative, in the original Pi
norm.  Its finite operator norm is retained rather than assumed to be one. -/
def originalTransitionDifferentialExtractor (a : ℕ) :
    ((Fin a → ℝ) →L[ℝ] (Fin a → ℝ)) →L[ℝ] (Fin (a*a) → ℝ) :=
  ContinuousLinearMap.pi fun c =>
    (ContinuousLinearMap.proj (finProdFinEquiv.symm c).1 : (Fin a → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ (Fin a → ℝ)
        (Pi.single (finProdFinEquiv.symm c).2 1))

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

/-- All weighted differential norms of the actual original transitions are
finite on their unchanged original overlap samples. -/
theorem original_transition_differential_weighted_finite
    (D : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions D)
    (T : ℕ → ℝ)
    (hTransition : ∀ p i k, 1 ≤ k → ∀ y ∈ actualOriginalGivenTransitionSample D (p,i),
      ‖iteratedFDeriv ℝ k (actualOriginalGivenTransition D p i) y‖ ≤ T k)
    (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell (actualOriginalGivenTransitionDifferentialCoordinates D)
      (actualOriginalGivenTransitionDomain D) (actualOriginalGivenTransitionSample D) ≠ ⊤ := by
  let L := originalTransitionDifferentialExtractor (n+d)
  apply paperAtlasWeighted_ne_top base j ell _ _ _ (actualOriginalGivenTransitionDomain_open D)
    (fun _ => inter_subset_right) (actualOriginalGivenTransitionDifferential_contDiffOn D hd)
  intro ik k _
  refine ⟨‖L‖ * T (k+1),?_⟩
  rintro _ ⟨y,rfl⟩
  let e := actualOriginalGivenTransition D ik.1 ik.2
  have he := actualOriginalGivenTransition_contDiffOn D hd ik
  have hO := actualOriginalGivenTransitionDomain_open D ik
  have hder := he.fderiv_of_isOpen hO (m := ∞) (by simp)
  have h := L.norm_iteratedFDeriv_comp_left (hder.contDiffAt (hO.mem_nhds y.property.2))
    (n := k) (by simp)
  change ‖iteratedFDeriv ℝ k (L ∘ fderiv ℝ e) (y : Fin (n+d) → ℝ)‖ ≤ _
  apply h.trans
  rw [norm_iteratedFDeriv_fderiv]
  exact mul_le_mul_of_nonneg_left (hTransition ik.1 ik.2 (k+1) (by omega) y y.property) (norm_nonneg _)

/-- Existing original geometry produces this component of the given
profile without an independent transition-differential supplier. -/
theorem original_transition_differential_finite_of_original_geometry
    {m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
    [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
    (D : IncrementsOriginalNativeData (m+1) d N M P) (hd : IncrementsOriginalDomainConditions D)
    (Parameter Spatial : ℕ → ℝ) (h : RepairOriginalTransitionBudgets D Parameter Spatial)
    (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell (actualOriginalGivenTransitionDifferentialCoordinates D)
      (actualOriginalGivenTransitionDomain D) (actualOriginalGivenTransitionSample D) ≠ ⊤ :=
  original_transition_differential_weighted_finite D hd
    (originalJointTransitionProfile (m+1) d Parameter Spatial)
    (repairOriginalTransitionBudgets_joint D hd Parameter Spatial h) base j ell

end GlobalEmbedding.Continuation.FaithfulRepair

#print axioms GlobalEmbedding.Continuation.FaithfulRepair.original_transition_differential_weighted_finite
#print axioms GlobalEmbedding.Continuation.FaithfulRepair.original_transition_differential_finite_of_original_geometry
