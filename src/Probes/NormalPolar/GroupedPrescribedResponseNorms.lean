import NormalPolar.GroupedPrescribedResponseJets
import NormalPolar.ParameterDisplacementFirstIncrementNorms

/-! The primitive prescribed reconstruction supplies the original atlas
C1 and C2 parameter-response bounds. No native derivative budget is an
input: all lower spatial jets are produced by the complete same wave in
the exact paired direction, then converted in the original gauge. -/
noncomputable section
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators ENNReal Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation GlobalEmbedding.Upgrade
variable {m N p r : ℕ} {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)] {M Ep : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

theorem groupedPrescribed_native_original_norms
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → Ep → D → M) (chi : (l : Fin r) → Sub l → X → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l s b x))
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) X) (W : Set (Ep × M)) (K : Fin r → Set (Ep × M))
    (pieceK : (l : Fin r) → Sub l → Set (Ep × M))
    (hW : IsOpen W) (hsub : ∀ l s, pieceK l s ⊆ K l) (n length : ℕ) (horder : 2+1+length ≤ n)
    (tau ell delta : ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A) (b : Ep)
    (hmap : ∀ x, (b,x) ∈ W)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (phase : Fin r → Ep × M → ℝ) (Mphase : ℝ)
    (profiles : ∀ i, JointGroupedPrescribedObservationProfiles F hF c chi nu a W pieceK n 2 ell Mg Bchi Bnu
      (fun y => (b,(A.chart i).symm y)) (A.chart i).target ((A.chart i) '' A.support i) T phase Mphase)
    (L R : ℕ) (hL : ∀ i y, y ∈ (A.chart i) '' A.support i →
      (Finset.univ.filter (fun l => (b,(A.chart i).symm y) ∈ K l)).card ≤ L)
    (hR : ∀ i l y, y ∈ (A.chart i) '' A.support i →
      (Finset.univ.filter (fun s => (b,(A.chart i).symm y) ∈ pieceK l s)).card ≤ R)
    (u direction : ProbeParameters r) :
    let vf := fun l s => actualProbeNormalAmplitude F (c l s) (chi l s) (nu l s) delta tau (weight l)
    let wave := fun v x => jointGroupedPrescribedWave label F hF c vf phase tau length a
      (probeParameterEmbedding label v) (b,x)
    let response := fun x => fderiv ℝ (fun v => wave v x) u direction
    let C := globalWavePrescribedResponseCost m N n length 2 (L*R) T weight Mg Bchi Bnu Mphase
    probeAtlasCj A 1 response ≤ ENNReal.ofReal (probeAtlasFromNativeConstant (m+1) N 1*C*delta*‖direction‖) ∧
    probeAtlasCj A 2 response ≤ ENNReal.ofReal (probeAtlasFromNativeConstant (m+1) N 2*C*delta/tau*‖direction‖) := by
  intro vf wave response C
  have hS (i : Fin A.count) : (A.chart i) '' A.support i ⊆ (A.chart i).target := by
    rintro y ⟨x,hx,rfl⟩
    exact (A.chart i).map_source (hA.support_subset i hx)
  have hk (i : Fin A.count) : ContinuousOn (fun y => (b,(A.chart i).symm y)) (A.chart i).target :=
    continuousOn_const.prodMk (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i)).continuousOn
  have hraw (i : Fin A.count) := groupedPrescribed_native_directional_jets label F hF c chi nu a W K pieceK hW hsub
    n length 2 horder tau ell delta weight Mg Bchi Bnu htau htaul hell1 hMg hdelta hBchi hBnu
    (fun y => (b,(A.chart i).symm y)) (A.chart i).target ((A.chart i) '' A.support i)
    (A.chart i).open_target (hS i) (hk i) (fun y _ => hmap ((A.chart i).symm y))
    T hT phase Mphase (profiles i) L R (hL i) (hR i) u direction
  have hC : 0 ≤ C := globalWavePrescribedResponseCost_nonneg m N n length 2 (L*R) T weight Mg Bchi Bnu Mphase
    hT hMg hBchi hBnu
  have hchart (i : Fin A.count) : ContDiffOn ℝ ∞ (response ∘ (A.chart i).symm) (A.chart i).target :=
    (hraw i).2.1
  have hjets : ∀ i, ∀ k ≤ 2, ∀ x ∈ A.support i,
      tau^k*‖iteratedFDeriv ℝ k (response ∘ (A.chart i).symm) (A.chart i x)‖ ≤
        (C*‖direction‖)*delta*tau := by
    intro i k hk x hx
    exact ((hraw i).2.2 k hk (A.chart i x) ⟨x,hx,rfl⟩).trans_eq (by ring)
  have hbound (j : ℕ) (hj : j ≤ 2) := probeAtlasCj_le_of_native_chart_weighted_jets
    A hA response hchart j tau delta (C*‖direction‖) htau (htaul.trans hell1) hdelta
    (mul_nonneg hC (norm_nonneg _)) (fun i k hk x hx => hjets i k (hk.trans hj) x hx)
  have he1 : probeAtlasFromNativeConstant (m+1) N 1*((C*‖direction‖)*delta*tau/tau^1) =
      probeAtlasFromNativeConstant (m+1) N 1*C*delta*‖direction‖ := by field_simp
  have he2 : probeAtlasFromNativeConstant (m+1) N 2*((C*‖direction‖)*delta*tau/tau^2) =
      probeAtlasFromNativeConstant (m+1) N 2*C*delta/tau*‖direction‖ := by field_simp
  exact ⟨by simpa only [he1] using hbound 1 (by omega),
    by simpa only [he2] using hbound 2 (by omega)⟩

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.groupedPrescribed_native_original_norms
