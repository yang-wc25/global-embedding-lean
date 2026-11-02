import NormalPolar.ActualProbeSecondaryUniform
import GlobalEmbedding.Offline.ModelCoordinateNorms

/-! The actual secondary observation after a fixed affine change of the
parameter coordinates. The same physical array, supports and samples are
retained. Its transition cost is computed from the true linear coordinate
norm, before the oscillation scale is chosen. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m N n j : ℕ} {Ep M Label Sub Y Z : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype Sub]

def ActualSecondaryProbeObservation.affinePullback
    {F : Ep → M → EuclideanSpace ℝ (Fin N)}
    {hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
      𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p)}
    {ell Mg CH delta : ℝ} {W : Set (Ep × M)}
    {data : ActualSecondarySignedRecord Label → Sub →
      ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W}
    (obs : ActualSecondaryProbeObservation F hF data Y)
    (e : Z ≃L[ℝ] Y) (center : Y) (hell : 0 ≤ ell) :
    ActualSecondaryProbeObservation F hF data Z := by
  let phi : Z → Y := fun z => center+e z
  have hphi : ContDiff ℝ ∞ phi := contDiff_const.add e.contDiff
  refine {
    kappa := obs.kappa ∘ phi
    domain := phi ⁻¹' obs.domain
    sample := phi ⁻¹' obs.sample
    domain_open := obs.domain_open.preimage hphi.continuous
    sample_subset := fun _ hz => obs.sample_subset hz
    smooth := obs.smooth.comp hphi.contMDiff.contMDiffOn (fun _ hz => hz)
    mapsTo := fun _ hz => obs.mapsTo hz
    primarySupport := obs.primarySupport
    primary_support := obs.primary_support
    localDomain := fun rec a => phi ⁻¹' obs.localDomain rec a
    local_open := fun rec a => (obs.local_open rec a).preimage hphi.continuous
    active_local := fun rec a _ hz => obs.active_local rec a hz
    source := fun rec a _ hz => obs.source rec a hz
    transition_smooth := fun rec a =>
      (obs.transition_smooth rec a).comp hphi.contDiffOn (fun _ hz => hz)
    transitionCost := fun k => linearModelFactor e k*obs.transitionCost k
    transitionCost_nonneg := fun k =>
      mul_nonneg (linearModelFactor_nonneg e k) (obs.transitionCost_nonneg k)
    active_sample := fun rec a _ hz => obs.active_sample rec a _ hz
    transition_bound := ?_
    primaryCount := obs.primaryCount
    secondaryCount := obs.secondaryCount
    primary_count := fun _ hz => obs.primary_count _ hz
    secondary_count := fun rec _ hz => obs.secondary_count rec _ hz }
  intro rec a z hz k hk hkj
  let f := (data rec a).base.chart ∘ obs.kappa
  have he := norm_iteratedFDeriv_comp_equiv_le e (fun y => f (center+y)) k z
  rw [iteratedFDeriv_comp_add_left] at he
  change ‖iteratedFDeriv ℝ k (f ∘ phi) z‖ ≤
    ‖iteratedFDeriv ℝ k f (phi z)‖*linearModelFactor e k at he
  calc
    _ ≤ ell^(k-1)*(‖iteratedFDeriv ℝ k f (phi z)‖*linearModelFactor e k) :=
      mul_le_mul_of_nonneg_left he (pow_nonneg hell _)
    _ = linearModelFactor e k*(ell^(k-1)*‖iteratedFDeriv ℝ k f (phi z)‖) := by ring
    _ ≤ linearModelFactor e k*obs.transitionCost k :=
      mul_le_mul_of_nonneg_left (obs.transition_bound rec a (phi z) hz k hk hkj)
        (linearModelFactor_nonneg e k)

theorem ActualSecondaryProbeObservation.affinePullback_wave
    {F : Ep → M → EuclideanSpace ℝ (Fin N)}
    {hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
      𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p)}
    {ell Mg CH delta : ℝ} {W : Set (Ep × M)}
    {data : ActualSecondarySignedRecord Label → Sub →
      ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W}
    (obs : ActualSecondaryProbeObservation F hF data Y)
    (e : Z ≃L[ℝ] Y) (center : Y) (hell : 0 ≤ ell) (tau : ℝ) (length : ℕ) :
    (obs.affinePullback e center hell).wave tau length =
      fun z => obs.wave tau length (center+e z) := rfl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.ActualSecondaryProbeObservation.affinePullback
#print axioms GlobalEmbedding.Continuation.ActualSecondaryProbeObservation.affinePullback_wave
