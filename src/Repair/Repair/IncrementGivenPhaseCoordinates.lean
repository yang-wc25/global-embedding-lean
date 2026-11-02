import Repair.IncrementGivenPhaseExtraction
import Repair.ReferenceSlicePhases
import Repair.EntranceOriginalObserverJets

/-! The original spatial covector coordinates are the spatial entries of
 the actual full joint differential for the literal weighted template phase.
 The genuine inverse chart tangent vectors are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter Bundle
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Y" => Fin (m+1+d) → ℝ
local notation "I" => 𝓘(ℝ,D)

private def givenPhaseSourceProjection : Y →L[ℝ] D :=
  (ContinuousLinearMap.snd ℝ Ep D).comp (parameterTensorModelEquiv (m+1) d).symm.toContinuousLinearMap

private theorem givenPhaseSourceProjection_single (r : Fin (m+1)) :
    givenPhaseSourceProjection (d := d) (Pi.single (Fin.castAdd d r) 1) = EuclideanSpace.single r 1 := by
  ext s
  change (Pi.single (Fin.castAdd d r) (1 : ℝ) : Fin (m+1+d) → ℝ) (Fin.castAdd d s) =
    (EuclideanSpace.single r (1 : ℝ)) s
  simp [Pi.single_apply,EuclideanSpace.single]

theorem increment_given_phase_spatial_coordinates
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (nu : Fin Data.primaryCount) (owner : Fin Data.atlas.count)
    (xi : D →L[ℝ] ℝ) (weight : ℝ)
    (hphase : Data.phase nu = fun z => weight*xi (Data.atlas.chart owner z.2))
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (y : Y)
    (hy : y ∈ incrementsOriginalDifferentiation Data.atlas Data.parameterChart i)
    (hOwn : (incrementsOriginalJointPoint Data.atlas Data.parameterChart i y).2 ∈
      (Data.atlas.chart owner).source) :
    incrementsOriginalPhaseCovectorCoordinates Data nu i y =
      incrementGivenSpatialExtraction (m+1) d (fderiv ℝ (actualOriginalJointPhase Data nu i) y) := by
  let host := Data.atlas.chart owner
  let observer := Data.atlas.chart i.1
  let x := incrementsOriginalSourcePoint y
  let z := incrementsOriginalJointPoint Data.atlas Data.parameterChart i y
  have hcov : incrementsOriginalPhaseCovector Data nu z.1 z.2 =
      (weight • xi).comp (mfderiv I I host z.2) := by
    unfold incrementsOriginalPhaseCovector
    rw [hphase]
    change round4HostPhaseCovector host (weight • xi) z.2 = _
    exact repair_reference_source_linear_covector host (hd.atlas_smooth.chart_mem owner)
      (weight • xi) z.2 hOwn
  have ht : DifferentiableAt ℝ (host ∘ observer.symm) x := by
    let b := repairReferenceHostTransition («Ep» := Ep) observer host
    have hz : (incrementsOriginalParameterPoint y,x) ∈ b.source := ⟨mem_univ _,hy.1,hOwn⟩
    have hh := ((repair_reference_host_transition_smooth («Ep» := Ep) observer host
      (hd.atlas_smooth.chart_mem i.1) (hd.atlas_smooth.chart_mem owner)).1.snd
      |>.contDiffAt (b.open_source.mem_nhds hz)).comp x (contDiffAt_const.prodMk contDiffAt_id)
    exact hh.differentiableAt (by simp)
  have hfun : actualOriginalJointPhase Data nu i =
      (weight • xi) ∘ (host ∘ observer.symm) ∘ givenPhaseSourceProjection (m := m) (d := d) := by
    funext u
    simp only [actualOriginalJointPhase,hphase,Function.comp_apply]
    rfl
  have hderiv : fderiv ℝ (actualOriginalJointPhase Data nu i) y =
      ((weight • xi).comp (fderiv ℝ (host ∘ observer.symm) x)).comp
        (givenPhaseSourceProjection (m := m) (d := d)) := by
    rw [hfun]
    change fderiv ℝ (((weight • xi) ∘ (host ∘ observer.symm)) ∘ givenPhaseSourceProjection (m := m) (d := d)) y = _
    rw [fderiv_comp y ((weight • xi).differentiableAt.comp _ ht)
      (givenPhaseSourceProjection (m := m) (d := d)).differentiableAt,
      ContinuousLinearMap.fderiv]
    have hsy : givenPhaseSourceProjection (m := m) (d := d) y = x := rfl
    rw [hsy,fderiv_comp _ (weight • xi).differentiableAt ht,ContinuousLinearMap.fderiv]
  have htransition := repair_reference_actual_transition_derivative observer host
    (hd.atlas_smooth.chart_mem i.1) (hd.atlas_smooth.chart_mem owner) x hy.1 hOwn
  ext r
  change incrementsOriginalPhaseCovector Data nu z.1 z.2
    (incrementsOriginalSourceVector Data.atlas i.1 y r) =
    fderiv ℝ (actualOriginalJointPhase Data nu i) y (Pi.single (Fin.castAdd d r) 1)
  rw [hcov,hderiv]
  change (weight • xi) (mfderiv I I host z.2 (mfderiv I I observer.symm x (EuclideanSpace.single r 1))) =
    (weight • xi) (fderiv ℝ (host ∘ observer.symm) x
      (givenPhaseSourceProjection (Pi.single (Fin.castAdd d r) 1)))
  rw [givenPhaseSourceProjection_single,htransition]
  rfl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_given_phase_spatial_coordinates
