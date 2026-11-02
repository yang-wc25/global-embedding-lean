import Repair.SourceCollarNovParameterGerm
import Smoothing.Round3ParameterCompactParents

/-! Actual localization of the original square product parents.  The source
and parameter raw preparations remain literal inputs, with the same charts,
sampling domains and numerical profiles.  One common smooth scalar is one
near K.  It changes only auxiliary parents outside that neighborhood; the
support count and every original-sample mixed germ are preserved. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {n d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local instance : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
local instance : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,D)) (n := ∞) P M

theorem sourceCollarNov_actual_parameter_localized_parents
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (A : BufferedAtlas M D) (B : TensorBufferedChartFamily (Fin c) P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (K U : Set P) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (RS : TensorRawCutoffPreparation A BS TS Ds)
    (RP : TensorLocalRawPreparation B K BP TP Dp)
    (Omega : Fin A.count → Set D) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, IsCompact (Omega i)) (hQ : ∀ i, IsCompact (Q i))
    (hOT : ∀ i, Omega i ⊆ (A.chart i).target) (hQT : ∀ i, Q i ⊆ (B.chart i).target)
    (hSource : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i) :
    let theta := round3ParameterProductParent A B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    ∃ (psi : P → ℝ) (V : Set P), IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,ℝ) ∞ psi ∧ EqOn psi 1 V ∧ tsupport psi ⊆ U ∧
      (∀ p, 0 ≤ psi p ∧ psi p ≤ 1) ∧
      (∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓘(ℝ,D)) 𝓘(ℝ,ℝ) ∞
        (sourceCollarNovParameterLocalized psi (theta i))) ∧
      (∀ i, IsCompact (tsupport (sourceCollarNovParameterLocalized psi (theta i)))) ∧
      (∀ i, tsupport (sourceCollarNovParameterLocalized psi (theta i)) ⊆
        tsupport (theta i)) ∧
      (∀ i, tsupport (sourceCollarNovParameterLocalized psi (theta i)) ⊆
        ((B.chart i.2).source ∩ U) ×ˢ A.inner i.1) ∧
      (∀ z : P × M, z.1 ∈ V → ∑ i, sourceCollarNovParameterLocalized psi (theta i) z = 1) ∧
      (∀ z, (Finset.univ.filter (fun i =>
        z ∈ tsupport (sourceCollarNovParameterLocalized psi (theta i)))).card ≤ (Ds+1)*(Dp+1)) ∧
      ∀ i z, z.1 ∈ K → sourceCollarNovParameterLocalized psi (theta i) =ᶠ[𝓝 z] theta i := by
  intro theta
  obtain ⟨W,hW,hKW,hSmooth,hCompact,hSupport,hPart,hCount⟩ :=
    round3Parameter_actual_compact_product_parents BS TS BP TP hBS hTS hBP hTP Ds Dp
      A B hA hB K RS RP Omega Q hOmega hQ hOT hQT hSource hParameter
  obtain ⟨psi,Vpsi,hVpsi,hKVpsi,hVpsiU,hPsi,hOne,hPsiSupport,hRange⟩ :=
    sourceCollarNov_parameter_localization B hB K U hK hU hKU RP
  let V := W ∩ Vpsi
  have hV : IsOpen V := hW.inter hVpsi
  have hKV : K ⊆ V := fun _ hp => ⟨hKW hp,hKVpsi hp⟩
  have hSub (i : Fin A.count × Fin c) :
      tsupport (sourceCollarNovParameterLocalized psi (theta i)) ⊆ tsupport (theta i) :=
    (sourceCollarNov_parameter_localized_tsupport psi (theta i)).trans inter_subset_left
  refine ⟨psi,V,hV,hKV,(inter_subset_right.trans hVpsiU),hPsi,
    (fun _ hp => hOne hp.2),hPsiSupport,hRange,?_,?_,hSub,?_,?_,?_,?_⟩
  · intro i
    have hTheta : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓘(ℝ,D)) 𝓘(ℝ,ℝ) ∞ (theta i) := by
      simpa only [modelWithCornersSelf_prod] using hSmooth i
    exact (hPsi.comp contMDiff_fst).mul hTheta
  · intro i
    exact (hCompact i).of_isClosed_subset (isClosed_tsupport _) (hSub i)
  · intro i z hz
    have hh := hSupport i (hSub i hz)
    exact ⟨⟨B.inner_subset i.2 hh.1,
      hPsiSupport (sourceCollarNov_parameter_localized_tsupport psi (theta i) hz).2⟩,hh.2⟩
  · intro z hz
    have hSum : (∑ i, theta i z) = 1 := hPart z hz.1
    simp only [sourceCollarNovParameterLocalized,← Finset.mul_sum,hSum,hOne hz.2,
      Pi.one_apply,mul_one]
  · intro z
    apply (Finset.card_le_card ?_).trans (hCount z)
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hSub i (Finset.mem_filter.mp hi).2⟩
  · intro i z hz
    exact sourceCollarNov_parameter_localized_germ psi Vpsi K hVpsi hKVpsi hOne (theta i) z hz

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.sourceCollarNov_actual_parameter_localized_parents
