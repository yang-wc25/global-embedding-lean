import Probes.Round3PreparedParameterPhaseConditions
import Probes.Round3ParameterFixedProfileRebase

/-! The actual new-map/new-normal record consumes the fixed-reference signed
Good result and the internally produced primary Good result. The original
full phase conditions are returned on the same rebound data. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

 theorem round3_prepared_parameter_rebound_phase_conditions
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (F : P × M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => F (p,x)))
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (V : Set P) (normal : Fin Ref.primaryCount → P × M → Ey)
    (domain : Fin Ref.primaryCount → Set (P × M))
    (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm})
    (hSigned : ∀ (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) z,
      z ∈ tsupport (Ref.cutoff r.val.1.1) ∩ tsupport (Ref.cutoff r.val.1.2) →
      GoodCovector (fun x => F (z.1,x)) (hF z.1) z.2
        ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (round3PreparedPhysicalSignedPhase Ref r z)).toContinuousLinearMap.comp
          (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => round3PreparedPhysicalSignedPhase Ref r (z.1,x)) z.2))) :
    let Data := round3ParameterStageData Ref F H V normal domain neighborhood
    ∀ (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data),
    (∀ nu z, z ∈ domain nu ∩ incrementsOriginalParameterRegion Data →
      GoodCovector (fun x => F (z.1,x)) (hF z.1) z.2 (incrementsOriginalPhaseCovector Data nu z.1 z.2)) →
    IncrementsOriginalPhaseConditions Data hd hs := by
  intro Data hd hs hPrimary
  apply round3_prepared_parameter_phase_conditions_of_actual_good Data hd hs hF hPrimary
  intro r z hz
  have hGlobal (nu) (hnu : z ∈ incrementsOriginalRelativeCutoffSupport Data nu) :
      z ∈ tsupport (Ref.cutoff nu) := by
    obtain ⟨w,hw,rfl⟩ := hnu
    exact tsupport_comp_subset_preimage (Ref.cutoff nu) continuous_subtype_val hw
  exact hSigned r z ⟨hGlobal _ hz.1,hGlobal _ hz.2⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_parameter_rebound_phase_conditions
