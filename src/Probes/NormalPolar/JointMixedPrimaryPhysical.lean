import NormalPolar.JointMixedVariablePhysical
import Probes.ActualSecondaryPrimaryRawConsumers
import Probes.Round4ParameterProbeCombinedPrimary

/-!
# The genuine joint-parameter combined primary physical residual

The background and prescribed residuals refer to the same finite formulas
as the common U1 array. Linearity of the real metric linearization is proved
on the original open domain. Thus CP is derived from primitive geometry,
with the true finite accuracy gain, and is not an input estimate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold Filter GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N p r : ℕ} {Ep M Tr Λ Β : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

private local instance combinedRawTensorSemi : SeminormedAddCommGroup Tensor :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance combinedRawTensorNormed : NormedAddCommGroup Tensor :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance combinedRawTensorSpace : NormedSpace ℝ Tensor :=
  ContinuousLinearMap.toNormedSpace

theorem jointMixed_combined_primary_raw_physical_uniform
    (n backgroundLength probeLength j accuracy Rbackground L : ℕ)
    (hbackgroundOrder : j+2+backgroundLength ≤ n) (hprobeOrder : j+probeLength ≤ n)
    (haccuracyBackground : accuracy ≤ backgroundLength) (haccuracyProbe : accuracy ≤ probeLength)
    (reserve Bnd Mg Bchi Bnu Ku Mphase : ℝ)
    (hreserve : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) (hKu : 0 ≤ Ku)
    (weight : Fin r → ℝ) (hweight : ∀ l, weight l ≠ 0) (Tbackground Tprobe : ℕ → ℝ)
    (hTbackground : ∀ k, 0 ≤ Tbackground k) (hTprobe : ∀ k, 0 ≤ Tprobe k) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := IM) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (input inputbar : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (tau ell delta Delta : ℝ) (hdelta : 0 ≤ delta)
    (W : Set (Ep × M)) (K : (Λ ⊕ Fin r) → Set (Ep × M))
    (e : OpenPartialHomeomorph M D) (Omega S : Set X)
    (background : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n backgroundLength j Rbackground L
      reserve Bnd Mg Tbackground F hF g input inputbar W (fun l => K (Sum.inl l)) e Omega S tau ell Delta)
    (backgroundGeometry : ActualOriginalPrimaryPhysicalGeometry F hF g)
    (prescribed : ActualPrescribedObservationProfiles F hF c chi nu a W (fun l => K (Sum.inr l))
      n (j+1) ell Mg Bchi Bnu (fun z : X => (z.1,e.symm z.2)) Omega S Tprobe phase Mphase)
    (prescribedGeometry : ∀ l, ActualPrescribedPhysicalGeometry F hF (c l) (nu l) (a l) (phase l))
    (hcount : ∀ y ∈ S, (Finset.univ.filter (fun l => (y.1,e.symm y.2) ∈ K l)).card ≤ L)
    (u : Ep → Fin p → ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : X => u z.1) Omega)
    (hub : ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (fun y : X => u y.1) z‖ ≤ Ku),
    let vf := fun l => actualProbeNormalAmplitude F (c l) (chi l) (nu l) delta tau (weight l)
    let Fobs := fun z : X => F z.1 (e.symm z.2)
    let U1 := fun z : X => round4ParameterProbeCombinedPrimary F hF g label c vf phase tau delta
      backgroundLength probeLength a input (u z.1) (z.1,e.symm z.2)
    let E := actualJointMetricLinearization Fobs U1
    ContDiffOn ℝ ∞ U1 Omega ∧ ContDiffOn ℝ ∞ E Omega ∧
      ∀ k ≤ j, ∀ y ∈ S, tau^k*‖iteratedFDeriv ℝ k E y‖ ≤ CP*delta*tau*(tau/ell)^accuracy := by
  obtain ⟨CU,CB,hCU,hCB,hbackground⟩ := actual_original_primary_consumers_from_raw
    (M := M) (Ep := Ep) (Tr := Tr) (m := m) (N := N) (Label := Λ) (Sub := Β)
    n backgroundLength j Rbackground L hbackgroundOrder reserve Bnd Mg hreserve hBnd hMg Tbackground hTbackground
  let CP := jointMixedVariablePrescribedPhysicalCost m N p n probeLength j L Tprobe weight Mg Bchi Bnu Ku
  have hCP : 0 ≤ CP := jointMixedVariablePrescribedPhysicalCost_nonneg m N p n probeLength j L
    Tprobe weight Mg Bchi Bnu Ku hTprobe hMg hBchi hBnu hKu
  refine ⟨CB+CP,add_nonneg hCB hCP,?_⟩
  intro F hF g label c chi nu phase a input inputbar tau ell delta Delta hdelta W K e Omega S
    background backgroundGeometry prescribed prescribedGeometry hcount u hu hub vf Fobs U1 E
  let kappa := fun z : X => (z.1,e.symm z.2)
  let bg := fun z : X => delta • incrementsGlobalPrimaryWave F hF g input backgroundLength tau (kappa z)
  let pr := fun z : X => round4PrescribedGlobalWave label F hF c vf phase tau probeLength a (u z.1) (kappa z)
  let EB := actualJointMetricLinearization Fobs bg
  let EP := actualJointMetricLinearization Fobs pr
  have hb := hbackground F hF g input inputbar W (fun l => K (Sum.inl l)) e Omega S tau ell Delta
    background backgroundGeometry delta
  have hLprobe (y : X) (hy : y ∈ S) :
      (Finset.univ.filter (fun l : Fin r => kappa y ∈ K (Sum.inr l))).card ≤ L := by
    apply (Finset.card_le_card_of_injOn (Sum.inr : Fin r → Λ ⊕ Fin r) ?_ ?_).trans (hcount y hy)
    · intro l hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hl).2⟩
    · intro l _ q _ h
      exact Sum.inr.inj h
  have hp := jointMixed_prescribed_variable_physical_from_raw label F hF c chi nu a W (fun l => K (Sum.inr l))
    background.prim.hW n probeLength j hprobeOrder tau ell delta weight Mg Bchi Bnu Ku
    background.htau background.htaul background.hell1 hdelta hweight hMg hBchi hBnu hKu
    kappa id (fun _ => rfl) Omega S background.hO background.hSO background.hkappaO background.hmapWO
    Tprobe hTprobe phase Mphase prescribed prescribedGeometry L hLprobe u hu hub
  have heq : U1 = fun z => bg z+pr z := by
    funext z
    exact round4ParameterProbeCombinedPrimary_eq F hF g label c vf phase tau delta backgroundLength probeLength a input (u z.1) (kappa z)
  have hlinear : EqOn E (fun z => EB z+EP z) Omega := by
    intro z hz
    have hBdiff := ((actual_joint_contDiffOn_slice bg Omega hb.1 z.1).contDiffAt
      ((background.hO.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)).differentiableAt (by simp)
    have hPdiff := ((actual_joint_contDiffOn_slice pr Omega hp.1 z.1).contDiffAt
      ((background.hO.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)).differentiableAt (by simp)
    dsimp only [E]
    rw [heq]
    ext v w
    simp only [EB,EP,actualJointMetricLinearization,actualCoordinateMetricLinearization_apply,
      fderiv_fun_add hBdiff hPdiff,ContinuousLinearMap.add_apply,inner_add_left,inner_add_right]
    ring
  have hE : ContDiffOn ℝ ∞ E Omega := (hb.2.1.add hp.2.1).congr hlinear
  refine ⟨heq ▸ hb.1.add hp.1,hE,?_⟩
  intro k hk y hy
  have htau := background.htau
  have hell : 0 < ell := htau.trans_le background.htaul
  have hratio : tau/ell ≤ 1 := (div_le_one hell).mpr background.htaul
  have hpowB := pow_le_pow_of_le_one (div_nonneg htau.le hell.le) hratio haccuracyBackground
  have hpowP := pow_le_pow_of_le_one (div_nonneg htau.le hell.le) hratio haccuracyProbe
  have hBj : tau^k*‖iteratedFDeriv ℝ k EB y‖ ≤ CB*delta*tau*(tau/ell)^accuracy := by
    have hh := hb.2.2.2 k hk y hy
    rw [abs_of_nonneg hdelta] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hpowB (by positivity))
  have hPj : tau^k*‖iteratedFDeriv ℝ k EP y‖ ≤ CP*delta*tau*(tau/ell)^accuracy :=
    (hp.2.2 k hk y hy).trans (mul_le_mul_of_nonneg_left hpowP (by positivity))
  have hmem := background.hO.mem_nhds (background.hSO hy)
  have hsum := actual_joint_slow_add_jet_bound EB EP k tau _ _ htau.le y
    ((hb.2.1.contDiffAt hmem).of_le (by simp)) ((hp.2.1.contDiffAt hmem).of_le (by simp)) hBj hPj
  have hnear := hlinear.eventuallyEq_of_mem hmem
  rw [(hnear.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hsum.trans_eq (by ring)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.jointMixed_combined_primary_raw_physical_uniform
