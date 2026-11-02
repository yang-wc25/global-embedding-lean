import Probes.ActualIncrementSplitScaleOriginalPrimary
import Probes.ActualIncrementPrimaryObservation
import Probes.ActualSecondaryObservedSupport

/-! The genuine observed linearized metric of the SAME original supported
primary piece equals the two-frame pullback of its actual local tensor.
The observation parameter may be a nontrivial parameter chart; only its
independence of the spatial variable is used. No output tensor identity is
assumed and no canonical source chart substitutes for the chosen chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep Eq M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Eq] [NormedSpace ℝ Eq]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Yobs" => Eq × D
local notation "𝓙" => 𝓘(ℝ,D)

private local instance observedPrimaryTensorSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance observedPrimaryTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance observedPrimaryTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem actual_original_primary_observed_physical_eq
    (F : Ep → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (ν : Λ) (β : Β) (length : ℕ) (tau : ℝ)
    (chart : Ep → OpenPartialHomeomorph M D)
    (hchart : ∀ b, chart b ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (hinverse : g.inverse ν β = fun b x => (chart b).symm x)
    (hTarget : ∀ z ∈ (g.chart ν β).target, z.2 ∈ (chart z.1).target)
    (hInverse : ∀ z ∈ (g.chart ν β).target,
      (g.chart ν β).symm z = (z.1,g.inverse ν β z.1 z.2))
    (kappa : Yobs → Ep × M) (parameter : Eq → Ep) (O : Set Yobs) (hO : IsOpen O)
    (hsource : MapsTo kappa O (g.chart ν β).source)
    (hfirst : ∀ z ∈ O, (kappa z).1 = parameter z.1)
    (hadapt : ∀ z ∈ O, g.phase ν (kappa z) = (g.chart ν β (kappa z)).2 0)
    (htransition : ContDiffOn ℝ ∞ (g.chart ν β ∘ kappa) O)
    (hlocal : ContDiffOn ℝ ∞ (actualSecondaryModulation (fun z : X => z.2 0) tau
      (incrementsGlobalPrimaryLocalZ F hF g input length tau true ν β)
      (incrementsGlobalPrimaryLocalZ F hF g input length tau false ν β)) (g.chart ν β).target) :
    let localWave := actualSecondaryModulation (fun z : X => z.2 0) tau
      (incrementsGlobalPrimaryLocalZ F hF g input length tau true ν β)
      (incrementsGlobalPrimaryLocalZ F hF g input length tau false ν β)
    let piece := fun w : Ep × M =>
      Real.cos (g.phase ν w/tau) • incrementsGlobalPrimaryExtension F hF g input length tau true ν β w -
        Real.sin (g.phase ν w/tau) • incrementsGlobalPrimaryExtension F hF g input length tau false ν β w
    let Elocal := fun z : X => actualCoordinateMetricLinearization (F z.1 ∘ g.inverse ν β z.1)
      (fun x => localWave (z.1,x)) z.2
    let Eobs := fun z : Yobs => actualCoordinateMetricLinearization
      (fun x => F (kappa (z.1,x)).1 (kappa (z.1,x)).2)
      (fun x => piece (kappa (z.1,x))) z.2
    EqOn Eobs (fun z => (Elocal (g.chart ν β (kappa z))).bilinearComp
      (actualJointSpatialJacobian (g.chart ν β ∘ kappa) z)
      (actualJointSpatialJacobian (g.chart ν β ∘ kappa) z)) O := by
  intro localWave piece Elocal Eobs
  let Phi : Yobs → X := g.chart ν β ∘ kappa
  have hcoords (y : Ep × M) (hy : y ∈ (g.chart ν β).source) :
      (g.chart ν β y).1 = y.1 ∧ g.inverse ν β (g.chart ν β y).1 (g.chart ν β y).2 = y.2 := by
    have he : y = ((g.chart ν β y).1,g.inverse ν β (g.chart ν β y).1 (g.chart ν β y).2) :=
      ((g.chart ν β).left_inv hy).symm.trans (hInverse _ ((g.chart ν β).map_source hy))
    exact ⟨(congrArg Prod.fst he).symm,(congrArg Prod.snd he).symm⟩
  have hp : ∀ y ∈ O, (Phi y).1 = parameter y.1 := by
    intro y hy
    exact (hcoords (kappa y) (hsource hy)).1.trans (hfirst y hy)
  have hWcoord : ∀ y ∈ O, piece (kappa y) = localWave (parameter y.1,(Phi y).2) := by
    intro y hy
    have hh : piece (kappa y) = localWave (Phi y) := by
      dsimp only [piece,localWave,actualSecondaryModulation,Phi,Function.comp_apply]
      simp only [incrementsGlobalPrimaryExtension,if_pos (hsource hy),hadapt y hy]
    have hpair : Phi y = (parameter y.1,(Phi y).2) := Prod.ext (hp y hy) rfl
    exact hh.trans (congrArg localWave hpair)
  have hFcoord : ∀ y ∈ O,
      F (kappa y).1 (kappa y).2 = F (parameter y.1) (g.inverse ν β (parameter y.1) (Phi y).2) := by
    intro y hy
    have hh : g.inverse ν β (Phi y).1 (Phi y).2 = (kappa y).2 := (hcoords (kappa y) (hsource hy)).2
    rw [hp y hy] at hh
    rw [hfirst y hy,hh]
  intro z hz
  let S : Set D := (fun x : D => (z.1,x)) ⁻¹' O
  have hS : IsOpen S := hO.preimage (continuous_const.prodMk continuous_id)
  have hzS : z.2 ∈ S := hz
  have htarget : Phi z ∈ (g.chart ν β).target := (g.chart ν β).map_source (hsource hz)
  have htarget' : (parameter z.1,(Phi z).2) ∈ (g.chart ν β).target := by
    rw [← show Phi z = (parameter z.1,(Phi z).2) from Prod.ext (hp z hz) rfl]
    exact htarget
  have hloc : (Phi z).2 ∈ (chart (parameter z.1)).target := by
    simpa only [hp z hz] using hTarget (Phi z) htarget
  let phix : D → D := fun x => (Phi (z.1,x)).2
  let Fx : D → V := F (parameter z.1) ∘ g.inverse ν β (parameter z.1)
  let Ux : D → V := fun x => localWave (parameter z.1,x)
  have hphi : DifferentiableAt ℝ phix z.2 := by
    have hh := actual_joint_contDiffOn_slice (fun y : Yobs => (Phi y).2) O htransition.snd z.1
    exact (hh.contDiffAt (hS.mem_nhds hzS)).differentiableAt (by simp)
  have hFx : DifferentiableAt ℝ Fx (phix z.2) := by
    have hFc : ContDiffOn ℝ ∞ (F (parameter z.1) ∘ (chart (parameter z.1)).symm)
        (chart (parameter z.1)).target :=
      ((hF (parameter z.1)).comp_contMDiffOn
        (contMDiffOn_symm_of_mem_maximalAtlas (hchart (parameter z.1)))).contDiffOn
    have hh := (hFc.contDiffAt ((chart (parameter z.1)).open_target.mem_nhds hloc)).differentiableAt (by simp)
    simpa only [Fx,hinverse,Function.comp_def,phix] using hh
  have hUx : DifferentiableAt ℝ Ux (phix z.2) := by
    have hh := actual_joint_contDiffOn_slice localWave (g.chart ν β).target hlocal (parameter z.1)
    have hopen : IsOpen ((fun x : D => (parameter z.1,x)) ⁻¹' (g.chart ν β).target) :=
      (g.chart ν β).open_target.preimage (continuous_const.prodMk continuous_id)
    exact (hh.contDiffAt (hopen.mem_nhds htarget')).differentiableAt (by simp)
  have hFG : (fun x => F (kappa (z.1,x)).1 (kappa (z.1,x)).2) =ᶠ[𝓝 z.2] Fx ∘ phix := by
    filter_upwards [hS.mem_nhds hzS] with x hx
    exact hFcoord (z.1,x) hx
  have hUG : (fun x => piece (kappa (z.1,x))) =ᶠ[𝓝 z.2] Ux ∘ phix := by
    filter_upwards [hS.mem_nhds hzS] with x hx
    exact hWcoord (z.1,x) hx
  have hlinear : Eobs z = (actualCoordinateMetricLinearization Fx Ux (phix z.2)).bilinearComp
      (fderiv ℝ phix z.2) (fderiv ℝ phix z.2) := by
    dsimp only [Eobs]
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

#print axioms GlobalEmbedding.Continuation.actual_original_primary_observed_physical_eq
