import NormalPolar.ParameterDisplacementPrescribedPhysicalCoordinates
import Probes.ActualSourceRestriction
import Probes.ActualSecondaryRemodulation

/-! Native source geometry for the same actual prescribed mode. Joint
primitive jet bounds restrict to the true fixed-parameter source jets with
no additional constant. The phase normalization follows from the actual
adapted chart, including its weight; it is not a new phase-jet assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold Filter GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation
variable {m N n j : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

theorem globalWave_raw_fixed_source_jets
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (c : Ep → D → M) (chi : X → ℝ)
    (nu : (b : Ep) → (x : D) → normalSpace (I:=IM) (F b) (c b x))
    (a : OpenPartialHomeomorph (Ep × M) X) (W K : Set (Ep × M))
    (ell Mg Bchi Bnu : ℝ) (hell : 0 ≤ ell)
    (raw : ActualPrescribedSpatialRawProfiles F hF c chi nu a W K n j ell Mg Bchi Bnu)
    (b : Ep) (S : Set D) (hS : ∀ y ∈ S, (b,y) ∈ raw.sample) :
    (∀ k ≤ n, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (incrementsModeComplexFirstOrderA (F b) (hF b) (c b)) y‖ ≤ Mg) ∧
    (∀ k ≤ n, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (incrementsModeComplexFirstOrderB (F b) (hF b) (c b)) y‖ ≤ Mg) ∧
    (∀ k ≤ j, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (fun y => freeGramRightInverse (fderiv ℝ (F b ∘ c b) y)) y‖ ≤ Mg) ∧
    (∀ k ≤ j, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (fun y => (normalSpace (I:=IM) (F b) (c b y)).subtypeL.comp
        (incrementsModeCoordinateJ (F b) (hF b) (c b) y)) y‖ ≤ Mg) ∧
    (∀ k ≤ j, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (incrementsModeTransverseValue (F b) (c b)) y‖ ≤ Mg) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro k hk y hy
    exact (mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_fixed_parameter_slice_le _ a.target a.open_target raw.A_smooth
        b y (raw.sample_subset (hS y hy)) k) (pow_nonneg hell k)).trans (raw.A_jets k hk (b,y) (hS y hy))
  · intro k hk y hy
    exact (mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_fixed_parameter_slice_le _ a.target a.open_target raw.B_smooth
        b y (raw.sample_subset (hS y hy)) k) (pow_nonneg hell k)).trans (raw.B_jets k hk (b,y) (hS y hy))
  · intro k hk y hy
    exact (mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_fixed_parameter_slice_le _ a.target a.open_target raw.G_smooth
        b y (raw.sample_subset (hS y hy)) k) (pow_nonneg hell k)).trans (raw.G_jets k hk (b,y) (hS y hy))
  · intro k hk y hy
    exact (mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_fixed_parameter_slice_le _ a.target a.open_target raw.J_smooth
        b y (raw.sample_subset (hS y hy)) k) (pow_nonneg hell k)).trans (raw.J_jets k hk (b,y) (hS y hy))
  · intro k hk y hy
    exact (mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_fixed_parameter_slice_le _ a.target a.open_target raw.T_smooth
        b y (raw.sample_subset (hS y hy)) k) (pow_nonneg hell k)).trans (raw.T_jets k hk (b,y) (hS y hy))

/-- The normalized source phase is the actual adapted coordinate divided
by its physical weight. Its weighted fast phase has all positive jets
bounded by one, independently of the physical family and scale. -/
theorem globalWave_physical_source_phase
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (c : Ep → D → M)
    (nu : (b : Ep) → (x : D) → normalSpace (I:=IM) (F b) (c b x))
    (a : OpenPartialHomeomorph (Ep × M) X) (phase : Ep × M → ℝ)
    (geom : ActualPrescribedPhysicalGeometry F hF c nu a phase)
    (b : Ep) (weight ell : ℝ) (hweight : 0 < weight) :
    let psi := fun y : D => y 0/weight
    ContMDiffOn 𝓘(ℝ,D) IM ∞ (c b) ((fun y : D => (b,y)) ⁻¹' a.target) ∧
    ContDiff ℝ ∞ psi ∧
    (∀ y, (b,y) ∈ a.target → phase (a.symm (b,y)) = weight*psi y) ∧
    (∀ k y, ell^k*‖iteratedFDeriv ℝ (k+1) (fun y => weight*psi y) y‖ ≤ 1) := by
  intro psi
  have hs : ContMDiffOn 𝓘(ℝ,D) IM ∞ (c b) ((fun y : D => (b,y)) ⁻¹' a.target) := by
    rw [geom.coordinates]
    exact (contMDiffOn_symm_of_mem_maximalAtlas (geom.maximal b)).mono (fun y hy => geom.target (b,y) hy)
  have hp : ContDiff ℝ ∞ psi := by
    change ContDiff ℝ ∞ (fun y : D => y 0 / weight)
    exact ((EuclideanSpace.proj (0 : Fin (m+1)) : D →L[ℝ] ℝ).contDiff).div_const weight
  have he : (fun y => weight*psi y) = (EuclideanSpace.proj (0 : Fin (m+1)) : D → ℝ) := by
    funext y
    change weight*(y 0/weight)=y 0
    field_simp
  refine ⟨hs,hp,?_,?_⟩
  · intro y hy
    rw [geom.adaptation _ (a.map_target hy),a.right_inv hy]
    exact (congrFun he y).symm
  · intro k y
    rw [he]
    apply actual_linear_phase_slow_jets
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    change ‖z (0 : Fin (m+1))‖ ≤ 1*‖z‖
    simpa only [one_mul] using PiLp.norm_apply_le z (0 : Fin (m+1))

/-- Actual adaptation plus the genuine source chart already supplies the
needed local phase smoothness. No extension of the phase off its source is
used in the reconstructed wave. -/
theorem globalWave_physical_local_phase_smooth
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (c : Ep → D → M)
    (nu : (b : Ep) → (x : D) → normalSpace (I:=IM) (F b) (c b x))
    (a : OpenPartialHomeomorph (Ep × M) X) (phase : Ep × M → ℝ)
    (geom : ActualPrescribedPhysicalGeometry F hF c nu a phase)
    (ha : ContMDiffOn ((𝓘(ℝ,Ep)).prod IM) 𝓘(ℝ,X) ∞ a a.source) :
    ContMDiffOn ((𝓘(ℝ,Ep)).prod IM) 𝓘(ℝ,ℝ) ∞ phase a.source := by
  have hp := (actualSecondaryCoordinatePhase (Ep:=Ep) (m:=m)).contDiff.contMDiff.comp_contMDiffOn ha
  apply hp.congr
  intro z hz
  exact geom.adaptation z hz

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_raw_fixed_source_jets
#print axioms GlobalEmbedding.NormalPolar.globalWave_physical_source_phase

#print axioms GlobalEmbedding.NormalPolar.globalWave_physical_local_phase_smooth
