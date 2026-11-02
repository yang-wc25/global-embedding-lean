import Probes.ActualCompactParameterCutoff
import Probes.ActualIncrementPreparedParentJets

/-! Actual finite parent cutoffs over a compact parameter evaluation set.
The parameter cutoff is constructed, is one on a fixed open neighborhood,
and has compact support in the true parameter region. Multiplying the SAME
squared source partition gives a genuine ordinary partition as a germ there.
All joint jets are produced with constants before the atlas and later scales.
Compact source pieces suffice; the source manifold need not be compact. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem actual_original_compact_parameter_parent_preparation
    (K Omega : Set Ep) (hK : IsCompact K) (hOmega : IsOpen Omega) (hKO : K ⊆ Omega)
    (B0 Ts : ℕ → ℝ) (hB0 : ∀ j, 0 ≤ B0 j) (hTs : ∀ j, 0 ≤ Ts j) (degree : ℕ) :
    ∃ (beta : Ep → ℝ) (V C : Set Ep) (Bbeta Bjoint : ℕ → ℝ),
      ContDiff ℝ ∞ beta ∧ IsOpen V ∧ K ⊆ V ∧ V ⊆ Omega ∧
      IsCompact C ∧ tsupport beta ⊆ C ∧ C ⊆ Omega ∧
      (∀ p ∈ V, beta p = 1) ∧ (∀ p, beta p ∈ Icc 0 1) ∧
      (∀ j, 0 ≤ Bbeta j) ∧ (∀ j p, ‖iteratedFDeriv ℝ j beta p‖ ≤ Bbeta j) ∧
      (∀ j, 0 ≤ Bjoint j) ∧ ∀ (A : BufferedAtlas M D) (_hA : IsSmoothBufferedAtlas A)
        (RS : TensorRawCutoffPreparation A B0 Ts degree),
      let chi := squareNormalizedCutoff RS.raw
      let theta := fun i (z : Ep × M) => beta z.1 * chi i z.2 ^ 2
      (∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i)) ∧
      (∀ z, ∑ i, theta i z = beta z.1) ∧
      (∀ z : Ep × M, z.1 ∈ V → ∀ᶠ w in 𝓝 z, ∑ i, theta i w = 1) ∧
      (∀ i, tsupport (theta i) ⊆ C ×ˢ A.inner i) ∧
      (∀ i, IsCompact (tsupport (RS.raw i)) → IsCompact (tsupport (theta i))) ∧
      ∀ i j (ell : ℝ), 0 ≤ ell → ell ≤ 1 → ∀ z : X,
        z.2 ∈ bufferedInnerCoordinates A i → (A.chart i).symm z.2 ∈ tsupport (chi i) →
        ell^j*‖iteratedFDeriv ℝ j
          (theta i ∘ (actualOriginalHostJointChart («Ep» := Ep) (A.chart i)).symm) z‖ ≤ Bjoint j := by
  obtain ⟨beta,V,C,Bbeta,hBeta,hV,hKV,hVO,hC,hSupportBeta,hCO,hOne,hRange,hBbeta,hBetaJets⟩ :=
    actual_compact_parameter_cutoff K Omega hK hOmega hKO
  obtain ⟨Bt,hBt,hParent⟩ := actual_uniform_prepared_parent_coordinate_profiles
    (m := m) (d := d) (M := M) B0 Ts hB0 hTs degree
  let PB := fun j => ∑ k ∈ Finset.range (j+1), Bbeta k
  let PT := fun j => ∑ k ∈ Finset.range (j+1), Bt k
  have hPB : ∀ j, 0 ≤ PB j := fun j => Finset.sum_nonneg (fun k _ => hBbeta k)
  have hPT : ∀ j, 0 ≤ PT j := fun j => Finset.sum_nonneg (fun k _ => hBt k)
  let Bjoint := fun j => 2^j*(‖ContinuousLinearMap.mul ℝ ℝ‖*PB j)*PT j
  have hBjoint : ∀ j, 0 ≤ Bjoint j := fun j =>
    mul_nonneg (mul_nonneg (by positivity)
      (mul_nonneg (ContinuousLinearMap.mul ℝ ℝ).opNorm_nonneg (hPB j))) (hPT j)
  refine ⟨beta,V,C,Bbeta,Bjoint,hBeta,hV,hKV,hVO,hC,hSupportBeta,hCO,hOne,hRange,
    hBbeta,hBetaJets,hBjoint,?_⟩
  intro A hA RS chi theta
  obtain ⟨hParentSmooth,hParentJets⟩ := hParent A hA RS
  have hBetaJoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞
      (fun z : Ep × M => beta z.1) := hBeta.contMDiff.comp contMDiff_fst
  have hSum (z : Ep × M) : ∑ i, theta i z = beta z.1 := by
    change (∑ i, beta z.1 * chi i z.2 ^ 2) = beta z.1
    rw [← Finset.mul_sum]
    rw [squareNormalizedCutoff_sum_sq RS.raw z.2
      (zero_lt_one.trans_le (one_le_squareCutoffSum_of_plateau RS.raw z.2 (RS.plateau_cover z.2))),mul_one]
  have hSupport (i : Fin A.count) : tsupport (theta i) ⊆
      tsupport beta ×ˢ tsupport (chi i) := by
    apply closure_minimal _ ((isClosed_tsupport _).prod (isClosed_tsupport _))
    intro z hz
    have hh : beta z.1 ≠ 0 ∧ chi i z.2 ^ 2 ≠ 0 := mul_ne_zero_iff.mp hz
    refine ⟨subset_tsupport _ hh.1,subset_tsupport _ ?_⟩
    intro hzero
    exact hh.2 (by rw [hzero]; norm_num)
  refine ⟨(fun i => hBetaJoint.mul (hParentSmooth i)),hSum,?_,?_,?_,?_⟩
  · intro z hz
    filter_upwards [((hV.preimage continuous_fst).mem_nhds hz)] with w hw
    exact (hSum w).trans (hOne w.1 hw)
  · intro i z hz
    exact ⟨hSupportBeta (hSupport i hz).1,
      RS.inner_support i (squareNormalizedCutoff_tsupport_subset RS.raw i (hSupport i hz).2)⟩
  · intro i hRaw
    apply (hC.prod hRaw).of_isClosed_subset (isClosed_tsupport _)
    intro z hz
    exact ⟨hSupportBeta (hSupport i hz).1,
      squareNormalizedCutoff_tsupport_subset RS.raw i (hSupport i hz).2⟩
  · intro i j ell hell hell1 z hz hzsupp
    let q := actualOriginalHostJointChart («Ep» := Ep) (A.chart i)
    let f : X → ℝ := fun y => beta y.1
    let g : X → ℝ := fun y => chi i ((A.chart i).symm y.2)^2
    let O : Set X := (fun y : X => y.2) ⁻¹' (A.chart i).target
    have hO : IsOpen O := (A.chart i).open_target.preimage continuous_snd
    have hzO : z ∈ O := hz.1
    have hf : ContDiff ℝ ∞ f := hBeta.comp contDiff_fst
    have hg : ContDiffOn ℝ ∞ g O := by
      have hcs : ContMDiffOn 𝓘(ℝ,X) 𝓙 ∞
          (fun y : X => (A.chart i).symm y.2) O :=
        (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i)).comp
          contDiff_snd.contMDiff.contMDiffOn (fun y hy => hy)
      have hqi : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
          (fun y : X => (y.1,(A.chart i).symm y.2)) O :=
        contDiff_fst.contMDiff.contMDiffOn.prodMk hcs
      exact ((hParentSmooth i).comp_contMDiffOn hqi).contDiffOn
    have hfb (k : ℕ) (hk : k ≤ j) : ell^k*‖iteratedFDeriv ℝ k f z‖ ≤ PB j := by
      have hproj := tensor_comp_nonexpansive_linear_jet_le
        (ContinuousLinearMap.fst ℝ Ep D) (ContinuousLinearMap.norm_fst_le ..)
        isOpen_univ hBeta.contDiffOn (Set.mem_univ z.1) k
      have hb := hproj.trans (hBetaJets k z.1)
      calc
        _ ≤ ell^k*Bbeta k := mul_le_mul_of_nonneg_left hb (pow_nonneg hell k)
        _ ≤ Bbeta k := mul_le_of_le_one_left (hBbeta k) (pow_le_one₀ hell hell1)
        _ ≤ PB j := Finset.single_le_sum (fun s _ => hBbeta s) (by simpa using hk)
    have hgb (k : ℕ) (hk : k ≤ j) : ell^k*‖iteratedFDeriv ℝ k g z‖ ≤ PT j := by
      exact (hParentJets i k ell hell hell1 z hz hzsupp).trans
        (Finset.single_le_sum (fun s _ => hBt s) (by simpa using hk))
    have hh := slow_bilinear_jet_bound_norm (ContinuousLinearMap.mul ℝ ℝ) O hO
      f g hf.contDiffOn hg j ell (PB j) (PT j) hell z hzO hfb hgb
    exact hh

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_compact_parameter_parent_preparation
