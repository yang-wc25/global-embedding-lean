import NormalPolar.ParameterDisplacementPrescribedRaw
import Probes.Round4PrescribedPhysicalResidual
import Probes.ActualIncrementPrimaryObservedJets

/-!
# Physical prescribed geometry and the genuine two-slot observation formula

The source chart and its actual inverse are retained. A value identity on
the true open observation domain gives equality of the real linearized
metric with the two spatial Jacobian slots; no tensor identity is postulated.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold Filter GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep Eq M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Eq] [NormedSpace ℝ Eq]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Y" => Eq × D
local notation "IM" => 𝓘(ℝ,D)

structure ActualPrescribedPhysicalGeometry
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b)) (c : Ep → D → M)
    (nu : (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c b x))
    (a : OpenPartialHomeomorph (Ep × M) X) (phase : Ep × M → ℝ) where
  slices : Ep → OpenPartialHomeomorph M D
  maximal : ∀ b, slices b ∈ IsManifold.maximalAtlas IM ∞ M
  coordinates : c = fun b x => (slices b).symm x
  target : ∀ z ∈ a.target, z.2 ∈ (slices z.1).target
  inverse : ∀ z ∈ a.target, a.symm z = (z.1,c z.1 z.2)
  immersion : ∀ z ∈ a.target, Function.Injective (mfderiv IM 𝓘(ℝ,V) (F z.1) (c z.1 z.2))
  gram : ∀ z ∈ a.target,
    let B := incrementsTransversePairing (F z.1) (hF z.1) (c z.1 z.2)
      (fun q : Fin m => incrementsModeCoordinateDirections (c z.1) z.2 q.succ)
    (B.comp B.adjoint).IsInvertible
  normal_kernel : ∀ z ∈ a.target,
    incrementsTransversePairing (F z.1) (hF z.1) (c z.1 z.2)
      (fun q : Fin m => incrementsModeCoordinateDirections (c z.1) z.2 q.succ) (nu z.1 z.2) = 0
  adaptation : ∀ z ∈ a.source, phase z = (a z).2 0

private local instance prescribedCoordTensorSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance prescribedCoordTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance prescribedCoordTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem actual_observed_linearization_source_coordinates
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b)) (c : Ep → D → M)
    (a : OpenPartialHomeomorph (Ep × M) X)
    (slices : Ep → OpenPartialHomeomorph M D)
    (hmaximal : ∀ b, slices b ∈ IsManifold.maximalAtlas IM ∞ M)
    (hc : c = fun b x => (slices b).symm x)
    (htarget : ∀ z ∈ a.target, z.2 ∈ (slices z.1).target)
    (hinverse : ∀ z ∈ a.target, a.symm z = (z.1,c z.1 z.2))
    (piece : Ep × M → V) (localWave : X → V) (hlocal : ContDiffOn ℝ ∞ localWave a.target)
    (kappa : Y → Ep × M) (parameter : Eq → Ep) (O : Set Y) (hO : IsOpen O)
    (hsource : MapsTo kappa O a.source) (hfirst : ∀ z ∈ O, (kappa z).1 = parameter z.1)
    (htransition : ContDiffOn ℝ ∞ (a ∘ kappa) O)
    (hvalue : ∀ z ∈ O, piece (kappa z) = localWave (a (kappa z))) :
    let Fobs := fun z : Y => F (kappa z).1 (kappa z).2
    let Elocal := fun z : X => actualCoordinateMetricLinearization (F z.1 ∘ c z.1)
      (fun x => localWave (z.1,x)) z.2
    EqOn (actualJointMetricLinearization Fobs (piece ∘ kappa))
      (fun z => (Elocal (a (kappa z))).bilinearComp
        (actualJointSpatialJacobian (a ∘ kappa) z) (actualJointSpatialJacobian (a ∘ kappa) z)) O := by
  intro Fobs Elocal
  let Phi : Y → X := a ∘ kappa
  have hcoords (y : Ep × M) (hy : y ∈ a.source) :
      (a y).1 = y.1 ∧ c (a y).1 (a y).2 = y.2 := by
    have he : y = ((a y).1,c (a y).1 (a y).2) :=
      (a.left_inv hy).symm.trans (hinverse _ (a.map_source hy))
    exact ⟨(congrArg Prod.fst he).symm,(congrArg Prod.snd he).symm⟩
  have hp : ∀ y ∈ O, (Phi y).1 = parameter y.1 :=
    fun y hy => (hcoords (kappa y) (hsource hy)).1.trans (hfirst y hy)
  have hWcoord : ∀ y ∈ O, piece (kappa y) = localWave (parameter y.1,(Phi y).2) := by
    intro y hy
    exact (hvalue y hy).trans (congrArg localWave (Prod.ext (hp y hy) rfl))
  have hFcoord : ∀ y ∈ O,
      F (kappa y).1 (kappa y).2 = F (parameter y.1) (c (parameter y.1) (Phi y).2) := by
    intro y hy
    have hh : c (Phi y).1 (Phi y).2 = (kappa y).2 := (hcoords (kappa y) (hsource hy)).2
    rw [hp y hy] at hh
    rw [hfirst y hy,hh]
  intro z hz
  let S : Set D := (fun x : D => (z.1,x)) ⁻¹' O
  have hS : IsOpen S := hO.preimage (continuous_const.prodMk continuous_id)
  have hzS : z.2 ∈ S := hz
  have htar : Phi z ∈ a.target := a.map_source (hsource hz)
  have htar' : (parameter z.1,(Phi z).2) ∈ a.target := by
    rw [← show Phi z = (parameter z.1,(Phi z).2) from Prod.ext (hp z hz) rfl]
    exact htar
  have hloc : (Phi z).2 ∈ (slices (parameter z.1)).target := by
    simpa only [hp z hz] using htarget (Phi z) htar
  let phix : D → D := fun x => (Phi (z.1,x)).2
  let Fx : D → V := F (parameter z.1) ∘ c (parameter z.1)
  let Ux : D → V := fun x => localWave (parameter z.1,x)
  have hphi : DifferentiableAt ℝ phix z.2 := by
    have hh := actual_joint_contDiffOn_slice (fun y : Y => (Phi y).2) O htransition.snd z.1
    exact (hh.contDiffAt (hS.mem_nhds hzS)).differentiableAt (by simp)
  have hFx : DifferentiableAt ℝ Fx (phix z.2) := by
    have hf := ((hF (parameter z.1)).comp_contMDiffOn
      (contMDiffOn_symm_of_mem_maximalAtlas (hmaximal (parameter z.1)))).contDiffOn
    have hh := (hf.contDiffAt ((slices (parameter z.1)).open_target.mem_nhds hloc)).differentiableAt (by simp)
    simpa only [Fx,hc,Function.comp_def,phix] using hh
  have hUx : DifferentiableAt ℝ Ux (phix z.2) := by
    have hh := actual_joint_contDiffOn_slice localWave a.target hlocal (parameter z.1)
    have hopen : IsOpen ((fun x : D => (parameter z.1,x)) ⁻¹' a.target) :=
      a.open_target.preimage (continuous_const.prodMk continuous_id)
    exact (hh.contDiffAt (hopen.mem_nhds htar')).differentiableAt (by simp)
  have hFG : (fun x => F (kappa (z.1,x)).1 (kappa (z.1,x)).2) =ᶠ[𝓝 z.2] Fx ∘ phix := by
    filter_upwards [hS.mem_nhds hzS] with x hx
    exact hFcoord (z.1,x) hx
  have hUG : (fun x => piece (kappa (z.1,x))) =ᶠ[𝓝 z.2] Ux ∘ phix := by
    filter_upwards [hS.mem_nhds hzS] with x hx
    exact hWcoord (z.1,x) hx
  have hlinear : actualJointMetricLinearization Fobs (piece ∘ kappa) z =
      (actualCoordinateMetricLinearization Fx Ux (phix z.2)).bilinearComp
        (fderiv ℝ phix z.2) (fderiv ℝ phix z.2) := by
    dsimp only [actualJointMetricLinearization,Fobs,Function.comp_def]
    unfold actualCoordinateMetricLinearization
    rw [hFG.fderiv_eq,hUG.fderiv_eq]
    exact actual_coordinate_metric_linearization_comp Fx Ux phix z.2 hFx hUx hphi
  rw [hlinear]
  have he : Elocal (Phi z) = actualCoordinateMetricLinearization Fx Ux (phix z.2) := by
    dsimp only [Elocal]
    rw [hp z hz]
  change _ = (Elocal (Phi z)).bilinearComp _ _
  rw [he]
  rfl

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_observed_linearization_source_coordinates
