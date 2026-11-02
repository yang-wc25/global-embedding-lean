import NormalPolar.JointBackgroundGroupedOriginalGerm

/-!
# The actual grouped forcing at every original joint derivative order

All observation orders refer to the same complete prescribed mean. We choose
one germ at order zero and transport the other proved bounds by equality of
the actual whole tensor field. Normalization by delta squared occurs once.
The zero reserve follows from the primitive amplitude cost; it is not an
assumed estimate for the completed mean.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {M P : Type*} {m N d p r count : ℕ}
  [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
variable {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem jointBackground_grouped_actual_prescribed_all_order_germ
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A)
    (Samples : Fin A.count × Fin count → Set (Fin (m+1+d) → ℝ))
    (hCompact : ∀ idx, IsCompact (Samples idx))
    (hOrig : ∀ idx, Samples idx ⊆ incrementsOriginalDifferentiation A B idx)
    (n : ℕ → ℕ) (length : ℕ) (horder : ∀ j, j+2+length ≤ n j)
    (T : ℕ → ℕ → ℝ) (hT : ∀ j k, 0 ≤ T j k)
    (weight : Fin r → ℝ) (Mg Bchi Bnu Mphase Ku : ℕ → ℝ)
    (hMg : ∀ j, 0 ≤ Mg j) (hBchi : ∀ j, 0 ≤ Bchi j)
    (hBnu : ∀ j, 0 ≤ Bnu j) (hMphase : ∀ j, 0 ≤ Mphase j)
    (hKu : ∀ j, 0 ≤ Ku j) (rho : ℝ)
    (hsmall : jointGroupedPrescribedZeroSourceCost Sub m N d p (n 0) length (T 0) weight
      (Mg 0) (Bchi 0) (Bnu 0) (Mphase 0)*(Ku 0)^2 ≤ rho/4) :
    let C := fun j => ((j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j)*
      jointGroupedPrescribedMeanUniformCost Sub m N p (n j) length j (T j) weight
        (Mg j) (Bchi j) (Bnu j) (Mphase j) (Ku j)
    ∀ (label : (Fin r × Bool) ↪ Fin p)
      (F : P → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F b))
      (c : (l : Fin r) → Sub l → P → D → M)
      (chi : (l : Fin r) → Sub l → P × D → ℝ)
      (nu : (l : Fin r) → (s : Sub l) → (b : P) → (x : D) →
        normalSpace (I := 𝓙) (F b) (c l s b x))
      (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (P × M) (P × D))
      (ha : ∀ l s, Round3ParameterChartPreserves (a l s)) (phase : Fin r → P × M → ℝ)
      (tau ell delta : ℝ), 0 < tau → tau ≤ ell → ell ≤ 1 → 0 < delta →
    ∀ (Omega : ℕ → Fin A.count × Fin count → Set X)
      (hOmega : ∀ j idx, IsOpen (Omega j idx))
      (hOmegaSub : ∀ j idx, Omega j idx ⊆ (B idx.2).target ×ˢ (A.chart idx.1).target)
      (hSamples : ∀ j idx, (parameterTensorModelEquiv (m+1) d) ⁻¹' Samples idx ⊆ Omega j idx)
      (profiles : ∀ j idx, JointGroupedPrescribedParameterChartRawData F hF c chi nu phase a
        (B idx.2) (A.chart idx.1) (Omega j idx) ((parameterTensorModelEquiv (m+1) d) ⁻¹' Samples idx)
        (n j) j ell (Mg j) (Bchi j) (Bnu j) (Mphase j) (T j))
      (u : P → Fin p → ℝ)
      (hu : ∀ j idx, ContDiffOn ℝ ∞ (fun z : X => u ((B idx.2).symm z.1)) (Omega j idx))
      (hub : ∀ j idx k, k ≤ j → ∀ z : X,
        parameterTensorModelEquiv (m+1) d z ∈ Samples idx →
        ell^k*‖iteratedFDeriv ℝ k (fun z : X => u ((B idx.2).symm z.1)) z‖ ≤ Ku j),
    let vf := fun l s b x => (-(delta*tau)/(weight l)^2) • (chi l s (b,x) • nu l s b x)
    let mean := fun b x => jointGroupedParameterPrescribedMean label F hF c vf phase tau length a (u b) b x
    let pj := parameterRound2_originalTensorGermSeminorm A B Samples univ hCompact hOrig ell
    ∃ probe Pforce : parameterRound2_originalTensorGermSpace A B Samples univ,
      probe.val = mean ∧ Pforce = (delta^2)⁻¹ • probe ∧
      Pforce.val = (delta^2)⁻¹ • mean ∧
      (∀ j, pj j probe ≤ C j*delta^2) ∧ (∀ j, pj j Pforce ≤ C j) ∧
      pj 0 Pforce ≤ rho/4 := by
  intro C label F hF c chi nu a ha phase tau ell delta htau htaul hell1 hdelta
    Omega hOmega hOmegaSub hSamples profiles u hu hub vf mean pj
  have hRaw (j : ℕ) := jointBackground_grouped_original_mean_raw_germ
    label F hF c chi nu a ha (n j) length j (horder j) tau ell delta weight
    (Mg j) (Bchi j) (Bnu j) (Mphase j) (Ku j) htau htaul hell1 (hMg j)
    hdelta.le (hBchi j) (hBnu j) (hMphase j) (hKu j) A B hA Samples
    (Omega j) (hOmega j) (hOmegaSub j) (hSamples j) (T j) (hT j) phase
    (profiles j) u (hu j) (hub j) univ hCompact hOrig (ne_of_gt hdelta)
  obtain ⟨probe,hvalue,hzero,hnzero⟩ := hRaw 0
  have hbound (j : ℕ) : pj j probe ≤ C j*delta^2 ∧ pj j ((delta^2)⁻¹ • probe) ≤ C j := by
    obtain ⟨other,hother,hb,hn⟩ := hRaw j
    have heq : other=probe := Subtype.ext (hother.trans hvalue.symm)
    simpa only [heq] using And.intro hb hn
  have hCzero : C 0 = jointGroupedPrescribedZeroSourceCost Sub m N d p (n 0) length (T 0) weight
      (Mg 0) (Bchi 0) (Bnu 0) (Mphase 0)*(Ku 0)^2 := by
    dsimp only [C,jointGroupedPrescribedZeroSourceCost]
    rw [jointGroupedPrescribedMeanUniformCost_amplitude_sq]
    ring
  refine ⟨probe,(delta^2)⁻¹ • probe,hvalue,rfl,?_,fun j => (hbound j).1,
    fun j => (hbound j).2,?_⟩
  · change (delta^2)⁻¹ • probe.val = (delta^2)⁻¹ • mean
    rw [hvalue]
  · exact ((hbound 0).2.trans_eq hCzero).trans hsmall

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.jointBackground_grouped_actual_prescribed_all_order_germ
