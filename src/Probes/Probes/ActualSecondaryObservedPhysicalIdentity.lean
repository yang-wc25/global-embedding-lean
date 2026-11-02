import Probes.ActualSecondaryConstructedPhysical
import Probes.ActualSecondaryPhysicalTensorEquality
import Probes.ActualSecondaryFiniteTensorIdentity

/-!
# Same-map physical residual in an actual observation chart

The observer preserves the parameter coordinate and differentiates only the
source coordinate. Its genuine transition to the adapted chart is used
throughout. The actual metric variation of the globally supported wave is
proved equal to the two-frame pullback of its constructed physical residual.
This is an exact identity, not an assumed chart comparison of errors.
-/

noncomputable section
open Manifold Set Filter Function GlobalEmbedding.Paper
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ, D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

variable {n j : ℕ} {ell Mg CH delta : ℝ} {W : Set (Ep × M)}

theorem actual_secondary_piece_chart_coordinates
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (d : ActualSecondaryPieceData (I := 𝓙) (m := m) F hF n j ell Mg CH delta W)
    (y : Ep × M) (hy : y ∈ d.chart.source) :
    (d.chart y).1 = y.1 ∧ d.c (d.chart y).1 (d.chart y).2 = y.2 := by
  have h := d.inverse (d.chart y) (d.chart.map_source hy)
  have he : y = ((d.chart y).1, d.c (d.chart y).1 (d.chart y).2) :=
    (d.chart.left_inv hy).symm.trans h
  exact ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩

def actualObservedSecondaryForcingTensor
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (d : ActualSecondaryPieceData (I := 𝓙) (m := m) F hF n j ell Mg CH delta W)
    (kappa : X → Ep × M) (tau : ℝ) : X → Tensor := fun z =>
  if kappa z ∈ d.chart.source then
    (actualSecondaryLocalForcingTensor d.hR d.hI tau (d.chart (kappa z))).bilinearComp
      (actualJointSpatialJacobian (d.chart ∘ kappa) z)
      (actualJointSpatialJacobian (d.chart ∘ kappa) z)
  else 0

def actualObservedSecondaryPhysicalError
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (d : ActualSecondaryPieceData (I := 𝓙) (m := m) F hF n j ell Mg CH delta W)
    (kappa : X → Ep × M) (tau : ℝ) (length : ℕ) : X → Tensor := fun z =>
  actualCoordinateMetricLinearization
    (fun x => F (kappa (z.1,x)).1 (kappa (z.1,x)).2)
    (fun x => d.wave tau length (kappa (z.1,x))) z.2 -
      actualObservedSecondaryForcingTensor F hF d kappa tau z

theorem actual_observed_secondary_physical_error_eq
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (d : ActualSecondaryPieceData (I := 𝓙) (m := m) F hF n j ell Mg CH delta W)
    (chart : Ep → OpenPartialHomeomorph M D) (hc : d.c = fun p x => (chart p).symm x)
    (hchart : ∀ p, chart p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (hOt : ∀ z ∈ d.chart.target, z.2 ∈ (chart z.1).target)
    (kappa : X → Ep × M) (O : Set X) (hO : IsOpen O)
    (hsource : MapsTo kappa O d.chart.source)
    (hfirst : ∀ z ∈ O, (kappa z).1 = z.1)
    (htransition : ContDiffOn ℝ ∞ (d.chart ∘ kappa) O)
    (tau : ℝ) (length : ℕ) (hbudget : j+1+length ≤ n)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH) :
    EqOn (actualObservedSecondaryPhysicalError F hF d kappa tau length)
      (fun z => (actualRemodulatedPhysicalTensor
        (actualSecondaryPhysicalError F hF chart d.hR d.hI tau length)
        (fun y : X => y.2 0) tau (d.chart (kappa z))).bilinearComp
          (actualJointSpatialJacobian (d.chart ∘ kappa) z)
          (actualJointSpatialJacobian (d.chart ∘ kappa) z)) O := by
  let Phi : X → X := d.chart ∘ kappa
  let wave := actualSecondaryWave (I := 𝓙) F hF d.c d.hR d.hI (fun y : X => y.2 0) tau length
  have hwave : ContDiffOn ℝ ∞ wave d.chart.target :=
    (d.local_wave_jets tau length hbudget hell hell1 htau htaul hMg hCH).1
  have hp : ∀ y ∈ O, (Phi y).1 = y.1 := by
    intro y hy
    exact (actual_secondary_piece_chart_coordinates F hF d (kappa y) (hsource hy)).1.trans (hfirst y hy)
  have hWcoord : ∀ y ∈ O, d.wave tau length (kappa y) = wave (y.1, (Phi y).2) := by
    intro y hy
    have hh := actualSecondarySupportedWave_eq_local F hF d.c d.hR d.hI d.chart d.phase
      (fun z : X => z.2 0) tau length (kappa y) (hsource hy)
      (d.adaptation (kappa y) (hsource hy))
    change d.wave tau length (kappa y) = wave (Phi y) at hh
    have hpair : Phi y = (y.1, (Phi y).2) := Prod.ext (hp y hy) rfl
    exact hh.trans (congrArg wave hpair)
  have hFcoord : ∀ y ∈ O,
      F (kappa y).1 (kappa y).2 = F y.1 (d.c y.1 (Phi y).2) := by
    intro y hy
    have hh := actual_secondary_piece_chart_coordinates F hF d (kappa y) (hsource hy)
    have hsecond : d.c y.1 (Phi y).2 = (kappa y).2 := by
      have hh2 : d.c (Phi y).1 (Phi y).2 = (kappa y).2 := hh.2
      rw [hp y hy] at hh2
      exact hh2
    rw [hfirst y hy, hsecond]
  intro z hz
  let S : Set D := (fun x : D => (z.1,x)) ⁻¹' O
  have hS : IsOpen S := hO.preimage (continuous_const.prodMk continuous_id)
  have hzS : z.2 ∈ S := hz
  have htarget : Phi z ∈ d.chart.target := d.chart.map_source (hsource hz)
  have htarget' : (z.1, (Phi z).2) ∈ d.chart.target := by
    have hpair : Phi z = (z.1, (Phi z).2) := Prod.ext (hp z hz) rfl
    rw [← hpair]
    exact htarget
  have hloc : (Phi z).2 ∈ (chart z.1).target := by
    simpa only [hp z hz] using hOt (Phi z) htarget
  let phix : D → D := fun x => (Phi (z.1,x)).2
  let Fx : D → V := fun x => F z.1 (d.c z.1 x)
  let Ux : D → V := fun x => wave (z.1,x)
  have hFxeq : Fx = F z.1 ∘ (chart z.1).symm := by
    funext x
    change F z.1 (d.c z.1 x) = F z.1 ((chart z.1).symm x)
    rw [hc]
  have hphi : DifferentiableAt ℝ phix z.2 := by
    have hh := actual_joint_contDiffOn_slice (fun y : X => (Phi y).2) O htransition.snd z.1
    exact (hh.contDiffAt (hS.mem_nhds hzS)).differentiableAt (by simp)
  have hFx : DifferentiableAt ℝ Fx (phix z.2) := by
    have hFc : ContDiffOn ℝ ∞ (F z.1 ∘ (chart z.1).symm) (chart z.1).target :=
      ((hF z.1).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hchart z.1))).contDiffOn
    have hh := (hFc.contDiffAt ((chart z.1).open_target.mem_nhds hloc)).differentiableAt (by simp)
    simpa only [Fx, hc, Function.comp_def] using hh
  have hUx : DifferentiableAt ℝ Ux (phix z.2) := by
    have hh := actual_joint_contDiffOn_slice wave d.chart.target hwave z.1
    have hopen : IsOpen ((fun x : D => (z.1,x)) ⁻¹' d.chart.target) :=
      d.chart.open_target.preimage (continuous_const.prodMk continuous_id)
    exact (hh.contDiffAt (hopen.mem_nhds htarget')).differentiableAt (by simp)
  have hFG : (fun x => F (kappa (z.1,x)).1 (kappa (z.1,x)).2) =ᶠ[𝓝 z.2] Fx ∘ phix := by
    filter_upwards [hS.mem_nhds hzS] with x hx
    exact hFcoord (z.1,x) hx
  have hUG : (fun x => d.wave tau length (kappa (z.1,x))) =ᶠ[𝓝 z.2] Ux ∘ phix := by
    filter_upwards [hS.mem_nhds hzS] with x hx
    exact hWcoord (z.1,x) hx
  have hlinear : actualCoordinateMetricLinearization
      (fun x => F (kappa (z.1,x)).1 (kappa (z.1,x)).2)
      (fun x => d.wave tau length (kappa (z.1,x))) z.2 =
      (actualCoordinateMetricLinearization Fx Ux (phix z.2)).bilinearComp
        (fderiv ℝ phix z.2) (fderiv ℝ phix z.2) := by
    unfold actualCoordinateMetricLinearization
    rw [hFG.fderiv_eq, hUG.fderiv_eq]
    exact actual_coordinate_metric_linearization_comp Fx Ux phix z.2 hFx hUx hphi
  have hcp : d.c = (fun p => ((chart p).symm : D → M)) := hc
  have hphys := actual_secondary_physical_tensor_eq_linearization F hF chart d.hR d.hI tau length
    (Phi z)
    (by simpa only [hp z hz, ← hFxeq, phix] using hFx)
    (by simpa only [hp z hz, ← hcp, Ux, phix, wave] using hUx)
  rw [← hcp] at hphys
  rw [hp z hz] at hphys
  rw [← hFxeq] at hphys
  change actualRemodulatedPhysicalTensor
      (actualSecondaryPhysicalError F hF chart d.hR d.hI tau length) (fun y : X => y.2 0) tau (Phi z) =
    actualCoordinateMetricLinearization Fx Ux (phix z.2) -
      actualSecondaryLocalForcingTensor d.hR d.hI tau (Phi z) at hphys
  unfold actualObservedSecondaryPhysicalError actualObservedSecondaryForcingTensor
  rw [if_pos (hsource hz), hlinear]
  dsimp only [Phi, Function.comp_apply] at hphys
  dsimp only
  rw [hphys]
  ext v w
  rfl

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_observed_secondary_physical_error_eq
