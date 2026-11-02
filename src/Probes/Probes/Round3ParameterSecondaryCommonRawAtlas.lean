import Probes.Round3ParameterSecondaryCommonRaw
import Probes.Round3ParameterRawAtlasData

/-! One physical secondary choice and its genuine native primitive families
produce the complete raw atlas used by the global finite increment. The
original total parameter-space samples are retained. No native chart is
chosen independently, and every observer uses the same final input tensor. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
universe uM uP uPrimary uSecondary
variable {m d N : ℕ} {M : Type uM} {P : Type uP} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  {Β : Type uPrimary} {SubSecondary : Type uSecondary} [Fintype Β] [Fintype SubSecondary]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3Parameter_secondary_common_raw_atlas
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F)
    (q : ℕ) (ell : ℝ) (W : Set (P × M))
    (Mrest Kcut Tinv Tobs : ℕ → ℝ) (Rsecondary : ℕ)
    (S : (Fin Data.atlas.count × Fin Data.parameterCount) → Set (Fin (m+1+d) → ℝ))
    (choice : ActualSecondarySignedRecord (Fin Data.primaryCount) → SubSecondary →
      Round3ParameterSecondaryChoice P M m)
    (family : ∀ ip : Fin Data.parameterCount,
      Round3ParameterPreparedSecondaryFamily (SubSecondary := SubSecondary) Data
        (fun p => F ((Data.parameterChart ip).symm p)) (fun p => hF ((Data.parameterChart ip).symm p))
        (round3ParameterNativePrimary F g (Data.parameterChart ip)) q ell
        (round3ParameterNativeDomain (Data.parameterChart ip) W)
        (round3ParameterNativeDomain (Data.parameterChart ip) W)
        Mrest Kcut Tinv Tobs Rsecondary
        (fun i => (parameterTensorModelEquiv (m+1) d) ⁻¹' S (i.1,ip)))
    (hChoice : ∀ ip, (family ip).choice = round3ParameterNativeChoices choice (Data.parameterChart ip))
    (input inputbar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (nInput j Rsub Lprimary : ℕ) (reserve Bnd : ℝ) (T : ℕ → ℝ)
    (primary : Fin Data.primaryCount → Set (P × M)) (delta tau Delta : ℝ)
    (finalRaw : ∀ i : Fin Data.atlas.count × Fin Data.parameterCount,
      ParameterRound2GlobalMeanRawProfiles (Tr := ℝ)
        nInput (q+2) (actualSecondarySolveOrder q j) Rsub Lprimary reserve Bnd (Mrest j) T
        (fun p => F ((Data.parameterChart i.2).symm p)) (fun p => hF ((Data.parameterChart i.2).symm p))
        (round3ParameterNativePrimary F g (Data.parameterChart i.2))
        (fun p => input ((Data.parameterChart i.2).symm p)) (fun p => inputbar ((Data.parameterChart i.2).symm p))
        (round3ParameterNativeDomain (Data.parameterChart i.2) W)
        (fun nu => round3ParameterNativeDomain (Data.parameterChart i.2) (primary nu))
        (Data.atlas.chart i.1)
        (actualRawObserverOpen (Data.atlas.chart i.1) (round3ParameterNativeDomain (Data.parameterChart i.2) W))
        ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i) tau ell Delta) :
    Nonempty (Round3ParameterRawAtlasData (Tr := ℝ) Data.atlas Data.parameterChart F hF g input inputbar
      nInput (actualSecondarySolveOrder q j) j q Rsub Lprimary Rsecondary reserve Bnd (Mrest j) (Kcut j)
      T Tinv Tobs W primary S ell delta tau Delta choice) := by
  have hOne (ip : Fin Data.parameterCount) :
      ∃ raw : ActualOriginalSecondaryRawData (Tr := ℝ)
        (fun p => F ((Data.parameterChart ip).symm p)) (fun p => hF ((Data.parameterChart ip).symm p))
        (round3ParameterNativePrimary F g (Data.parameterChart ip))
        (fun p => input ((Data.parameterChart ip).symm p)) (fun p => inputbar ((Data.parameterChart ip).symm p))
        nInput (actualSecondarySolveOrder q j) j q Rsub Lprimary reserve Bnd (Mrest j) (Kcut j) T Tinv
        (round3ParameterNativeDomain (Data.parameterChart ip) W)
        (fun nu => round3ParameterNativeDomain (Data.parameterChart ip) (primary nu))
        ell delta tau Delta (round3ParameterNativeChoices choice (Data.parameterChart ip)),
      Nonempty (∀ is : Fin Data.atlas.count, ActualOriginalSecondaryObservationData raw Tobs Rsecondary
        (Data.atlas.chart is)
        (actualRawObserverOpen (Data.atlas.chart is) (round3ParameterNativeDomain (Data.parameterChart ip) W))
        ((parameterTensorModelEquiv (m+1) d) ⁻¹' S (is,ip))) := by
    let Fr := fun p => F ((Data.parameterChart ip).symm p)
    let hFr := fun p => hF ((Data.parameterChart ip).symm p)
    let gr := round3ParameterNativePrimary F g (Data.parameterChart ip)
    let Wr := round3ParameterNativeDomain (Data.parameterChart ip) W
    let Sr := fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
      (parameterTensorModelEquiv (m+1) d) ⁻¹' S (i.1,ip)
    let primaryr := fun nu => round3ParameterNativeDomain (Data.parameterChart ip) (primary nu)
    let Kr := fun p => input ((Data.parameterChart ip).symm p)
    let Lr := fun p => inputbar ((Data.parameterChart ip).symm p)
    let raws := fun i : Fin Data.atlas.count × Fin Data.parameterCount => finalRaw (i.1,ip)
    let raw := round3Parameter_secondary_raw_from_common Data Fr hFr gr q ell Wr
      Mrest Kcut Tinv Tobs Rsecondary Sr (family ip) Kr Lr nInput j Rsub Lprimary reserve Bnd T primaryr
      delta tau Delta raws
    have hNative : ∃ raw0 : ActualOriginalSecondaryRawData (Tr := ℝ) Fr hFr gr Kr Lr
        nInput (actualSecondarySolveOrder q j) j q Rsub Lprimary reserve Bnd (Mrest j) (Kcut j) T Tinv
        Wr primaryr ell delta tau Delta (family ip).choice,
        Nonempty (∀ is : Fin Data.atlas.count, ActualOriginalSecondaryObservationData raw0 Tobs Rsecondary
          (Data.atlas.chart is) (actualRawObserverOpen (Data.atlas.chart is) Wr) (Sr (is,ip))) := by
      refine ⟨raw,⟨?_⟩⟩
      intro is
      exact round3Parameter_secondary_observation_from_common Data hd Fr hFr gr q ell Wr
        Mrest Kcut Tinv Tobs Rsecondary Sr (family ip) Kr Lr nInput j Rsub Lprimary reserve Bnd T primaryr
        delta tau Delta raws (is,ip)
    dsimp only [Fr,hFr,gr,Kr,Lr,Wr,primaryr,Sr] at hNative
    rw [hChoice ip] at hNative
    exact hNative
  choose raw obs using hOne
  exact ⟨{
    raw := raw
    observationDomain := fun i => actualRawObserverOpen (Data.atlas.chart i.1)
      (round3ParameterNativeDomain (Data.parameterChart i.2) W)
    observation := fun i => Classical.choice (obs i.2) i.1 }⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_secondary_common_raw_atlas
