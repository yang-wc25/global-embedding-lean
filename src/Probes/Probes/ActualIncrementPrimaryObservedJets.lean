import Probes.ActualIncrementPrimaryObservedPhysical
import Probes.ActualSecondaryGlobalPhysicalSum

/-! Actual original primary physical residual, observed through its real
parameter/source transition. The native tensor has both true spatial
Jacobian slots, and B uses its correct extra slow-scale weight. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {M Ep Eq : Type*} {m N : ℕ}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Eq] [NormedSpace ℝ Eq]
  {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Yobs" => Eq × D

local notation "𝓙" => 𝓘(ℝ,D)

private local instance originalPrimaryTensorSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance originalPrimaryTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance originalPrimaryTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem actual_original_primary_observed_physical_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (ν : Λ) (β : Β) (n length j : ℕ) (horder : j+length ≤ n)
    (chart : Ep → OpenPartialHomeomorph M D)
    (hchart : ∀ b, chart b ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (hinverse : g.inverse ν β = fun b x => (chart b).symm x)
    (hTarget : ∀ z ∈ (g.chart ν β).target, z.2 ∈ (chart z.1).target)
    (hinj : ∀ z ∈ (g.chart ν β).target,
      Function.Injective (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) (g.inverse ν β z.1 z.2)))
    (hfree : ∀ z ∈ (g.chart ν β).target,
      let b := incrementsTransversePairing (F z.1) (hF z.1) (g.inverse ν β z.1 z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (g.inverse ν β z.1) z.2 a.succ)
      (b.comp b.adjoint).IsInvertible)
    (hnormalKernel : ∀ z (hz : z ∈ (g.chart ν β).target),
      incrementsTransversePairing (F z.1) (hF z.1) (g.inverse ν β z.1 z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (g.inverse ν β z.1) z.2 a.succ)
        ⟨g.normal ν (z.1,g.inverse ν β z.1 z.2),g.normal_mem ν β z hz⟩ = 0)
    (S : Set X) (hSO : S ⊆ (g.chart ν β).target)
    (tau ell Mg K : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hK : 0 ≤ K)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (hG : ContDiffOn ℝ ∞ (fun z : X =>
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ g.inverse ν β z.1) z.2)) (g.chart ν β).target)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := 𝓙) (F z.1) (g.inverse ν β z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (g.inverse ν β z.1) z.2)) (g.chart ν β).target)
    (hT : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeTransverseValue (F z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (g.inverse ν β z.1) z.2 0 i : V)) (g.chart ν β).target)
    (hvf : ContDiffOn ℝ ∞ (fun z : X =>
      (incrementsGlobalPrimaryLocalFree F g input tau ν β z.1 z.2 : V)) (g.chart ν β).target)
    (hAb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (g.inverse ν β w.1) w.2) z‖ ≤ Mg)
    (hBb : ∀ k ≤ n, ∀ z ∈ S, ell^(k+1) * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (g.inverse ν β w.1) w.2) z‖ ≤ Mg)
    (hBRb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => fun i : Fin (m+1) =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (g.inverse ν β w.1) w.2 0 i : V)) z‖ ≤ Mg)
    (hvfb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => (incrementsGlobalPrimaryLocalFree F g input tau ν β w.1 w.2 : V)) z‖ ≤ K*tau)
    (hInverse : ∀ z ∈ (g.chart ν β).target,
      (g.chart ν β).symm z = (z.1,g.inverse ν β z.1 z.2))
    (kappa : Yobs → Ep × M) (parameter : Eq → Ep) (O : Set Yobs) (hO : IsOpen O)
    (hsource : MapsTo kappa O (g.chart ν β).source)
    (hfirst : ∀ z ∈ O, (kappa z).1 = parameter z.1)
    (hadapt : ∀ z ∈ O, g.phase ν (kappa z) = (g.chart ν β (kappa z)).2 0)
    (htransition : ContDiffOn ℝ ∞ (g.chart ν β ∘ kappa) O)
    (T : ℕ → ℝ) (hTprof : ∀ i, 0 ≤ T i) (z : Yobs) (hz : z ∈ O)
    (hsample : g.chart ν β (kappa z) ∈ S)
    (htransitionb : ∀ i, 1 ≤ i → i ≤ j+1 →
      ell^(i-1) * ‖iteratedFDeriv ℝ i (g.chart ν β ∘ kappa) z‖ ≤ T i) :
    let piece := fun w : Ep × M =>
      Real.cos (g.phase ν w/tau) • incrementsGlobalPrimaryExtension F hF g input length tau true ν β w -
        Real.sin (g.phase ν w/tau) • incrementsGlobalPrimaryExtension F hF g input length tau false ν β w
    let Eobs := fun y : Yobs => actualCoordinateMetricLinearization
      (fun x => F (kappa (y.1,x)).1 (kappa (y.1,x)).2)
      (fun x => piece (kappa (y.1,x))) y.2
    ContDiffOn ℝ ∞ Eobs O ∧ ∀ r ≤ j,
      tau^r*‖iteratedFDeriv ℝ r Eobs z‖ ≤ actualFastTensorChartTransferCost T r *
        actualPrimaryPhysicalCost m N n length j Mg K 0 * (tau/ell)^length*tau := by
  intro piece Eobs
  have hell : 0 < ell := htau.trans_le htaul
  obtain ⟨hw,hE,hEb⟩ := actual_original_primary_local_physical_split_scale_jets
    F hF g input ν β n length j horder chart hchart hinverse hTarget hinj hfree hnormalKernel
    S hSO tau ell Mg K htau htaul hell1 hMg hK hA hB hG hJ hT hBR hvf hAb hBb hBRb hvfb
  let localWave := actualSecondaryModulation (fun z : X => z.2 0) tau
    (incrementsGlobalPrimaryLocalZ F hF g input length tau true ν β)
    (incrementsGlobalPrimaryLocalZ F hF g input length tau false ν β)
  let Elocal := fun y : X => actualCoordinateMetricLinearization (F y.1 ∘ g.inverse ν β y.1)
    (fun x => localWave (y.1,x)) y.2
  let C := actualPrimaryPhysicalCost m N n length j Mg K 0 * (tau/ell)^length*tau
  have hC : 0 ≤ C := by
    have hc := actualPrimaryPhysicalCost_nonneg m N n length j hMg hK (show (0:ℝ) ≤ 0 from le_rfl)
    dsimp only [C]
    positivity
  have he := actual_original_primary_observed_physical_eq F hF g input ν β length tau
    chart hchart hinverse hTarget hInverse kappa parameter O hO hsource hfirst hadapt htransition hw
  have hc := actual_fast_joint_tensor_chart_transfer T hTprof j (g.chart ν β ∘ kappa) Elocal
    O (g.chart ν β).target hO (g.chart ν β).open_target htransition hE
    (fun y hy => (g.chart ν β).map_source (hsource hy)) z hz tau ell C htau htaul hC
    (fun r hr => hEb r hr _ hsample) htransitionb
  refine ⟨hc.1.congr he,?_⟩
  intro r hr
  have hb := (actual_fast_joint_tensor_chart_transfer T hTprof r (g.chart ν β ∘ kappa) Elocal
    O (g.chart ν β).target hO (g.chart ν β).open_target htransition hE
    (fun y hy => (g.chart ν β).map_source (hsource hy)) z hz tau ell C htau htaul hC
    (fun i hi => hEb i (hi.trans hr) _ hsample)
    (fun i hi hir => htransitionb i hi (by omega))).2
  have hg : Eobs =ᶠ[𝓝 z] (fun y => (Elocal (g.chart ν β (kappa y))).bilinearComp
      (actualJointSpatialJacobian (g.chart ν β ∘ kappa) y)
      (actualJointSpatialJacobian (g.chart ν β ∘ kappa) y)) :=
    he.eventuallyEq_of_mem (hO.mem_nhds hz)
  rw [(hg.iteratedFDeriv ℝ r).eq_of_nhds]
  exact hb.trans_eq (by dsimp only [C]; ring)


/-- Qualitative true tensor transport does not need any sampled jet budget. -/
theorem actual_joint_native_tensor_pullback_contDiffOn
    (phi : Yobs → X) (B : X → D →L[ℝ] D →L[ℝ] ℝ)
    (O : Set Yobs) (Vset : Set X) (hO : IsOpen O)
    (hphi : ContDiffOn ℝ ∞ phi O) (hB : ContDiffOn ℝ ∞ B Vset)
    (hmap : MapsTo phi O Vset) :
    ContDiffOn ℝ ∞ (fun z => (B (phi z)).bilinearComp
      (actualJointSpatialJacobian phi z) (actualJointSpatialJacobian phi z)) O := by
  let flip : (D →L[ℝ] D →L[ℝ] ℝ) ≃ₗᵢ[ℝ] (D →L[ℝ] D →L[ℝ] ℝ) :=
    ContinuousLinearMap.flipₗᵢ ℝ D D ℝ
  have hJ : ContDiffOn ℝ ∞ (actualJointSpatialJacobian phi) O :=
    (incrementsJointSpatialJets_bridge (fun z => (phi z).2) O hO hphi.snd).2.1
  have h1 := (hB.comp hphi hmap).clm_comp hJ
  have h2 := (flip.contDiff.comp_contDiffOn h1).clm_comp hJ
  exact flip.contDiff.comp_contDiffOn h2

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_primary_observed_physical_jets

#print axioms GlobalEmbedding.Continuation.actual_joint_native_tensor_pullback_contDiffOn
