import Probes.Round3ParameterSecondaryCommonRawAtlas
import Probes.Round4PrimaryLocalMultiplicity
import IncrementsCompletion.OriginalEvaluationPoint

/-! The canonical native raw record also counts true physical cutoff
supports. Reuse all of its primitive fields and improve only hCount. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P Β : Type*}
  [TopologicalSpace M] [TopologicalSpace P] [Fintype Β]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

def incrementsCompletion_native_raw_sample_count
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β) F)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (input inputbar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (n length j Rsub Lold Lactive : ℕ) (reserve Bnd Mg : ℝ) (T : ℕ → ℝ)
    (W : Set (P × M)) (primary : Fin Data.primaryCount → Set (P × M))
    (O : Set (Ep × D)) (tau ell Delta : ℝ)
    (hCutoff : g.cutoff = Data.cutoff)
    (hCount : ∀ z ∈ Data.parameterSet ×ˢ (univ : Set M),
      (Finset.univ.filter (fun nu => z ∈ incrementsOriginalRelativeCutoffSupport Data nu)).card ≤ Lactive)
    (raw : ParameterRound2GlobalMeanRawProfiles (Tr := ℝ) n length j Rsub Lold reserve Bnd Mg T
      (fun p => F ((Data.parameterChart i.2).symm p)) (fun p => hF ((Data.parameterChart i.2).symm p)) (round3ParameterNativePrimary F g (Data.parameterChart i.2))
      (fun p => input ((Data.parameterChart i.2).symm p)) (fun p => inputbar ((Data.parameterChart i.2).symm p))
      (round3ParameterNativeDomain (Data.parameterChart i.2) W) (fun nu => round3ParameterNativeDomain (Data.parameterChart i.2) (primary nu))
      (Data.atlas.chart i.1) O ((parameterTensorModelEquiv (m+1) d) ⁻¹'
        incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet i) tau ell Delta) :
    ParameterRound2GlobalMeanRawProfiles (Tr := ℝ) n length j Rsub Lactive reserve Bnd Mg T
      (fun p => F ((Data.parameterChart i.2).symm p)) (fun p => hF ((Data.parameterChart i.2).symm p)) (round3ParameterNativePrimary F g (Data.parameterChart i.2))
      (fun p => input ((Data.parameterChart i.2).symm p)) (fun p => inputbar ((Data.parameterChart i.2).symm p))
      (round3ParameterNativeDomain (Data.parameterChart i.2) W) (fun nu => round3ParameterNativeDomain (Data.parameterChart i.2) (primary nu))
      (Data.atlas.chart i.1) O ((parameterTensorModelEquiv (m+1) d) ⁻¹'
        incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet i) tau ell Delta := by
  refine { raw with hCount := ?_ }
  intro z hz
  let w : Ep × M := (z.1,(Data.atlas.chart i.1).symm z.2)
  have hw : w ∈ round3ParameterNativeDomain (Data.parameterChart i.2) W := raw.hmapWO (raw.hSO hz)
  have hSample := incrementsCompletion_original_evaluation_parameter Data i z hz
  apply (Finset.card_le_card ?_).trans (hCount ((Data.parameterChart i.2).symm w.1,w.2) hSample)
  intro nu hnu
  have hn := (Finset.mem_filter.mp hnu).2
  rw [parameterRound2_global_relativeSupport_eq _ raw.prim.hW] at hn
  have hp := round3Parameter_plain_pullback_tsupport (round3ParameterProductChart (M := M) (Data.parameterChart i.2))
    (g.cutoff nu) w ⟨hw.1,mem_univ _⟩ hn.2
  rw [hCutoff] at hp
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  rw [incrementsBridge_original_relative_support_eq Data hd nu]
  exact ⟨⟨hd.parameter_subset hSample.1,mem_univ _⟩,hp⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_native_raw_sample_count
