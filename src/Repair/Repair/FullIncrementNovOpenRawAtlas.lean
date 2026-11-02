import Repair.FullIncrementNovOpenSourceModel
import Repair.FullIncrementNovOpenMeanRawSupply
import Smoothing.Round3ParameterMeanRawAtlas
import Smoothing.Round3ParameterNativeRestriction

/-! The actual native raw profiles assemble into the existing physical raw
atlas for the internally constructed source-slice model.  This reuses the
verified finite mean and secondary consumers.  The original Data and all
computational primitive fields are unchanged.  Clipping a primary analysis
domain by W is removed by a proved record construction, not a new analytic
assumption or an alteration of any cutoff/support.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

section Unclip
variable {E H M Ep Tr : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {m N : ℕ} {Label Sub : Type*} [Fintype Label] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

def fullIncrementNovMeanPrimitivesUnclip
    (F : Ep → M → Ey) (hF : ∀ p, ContMDiff I 𝓘(ℝ,Ey) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (Λ := Label) (Β := Sub) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primary : Label → Set (Ep × M))
    (hPrimary : ∀ nu, IsOpen (primary nu))
    (h : ParameterRound2GlobalMeanPrimitives F hF g input W (fun nu => W ∩ primary nu)) :
    ParameterRound2GlobalMeanPrimitives F hF g input W primary := {
  h with
  hPrimary := hPrimary
  hPrimarySupport := fun nu z hz => (h.hPrimarySupport nu hz).2
  hSourceW := fun nu beta z hz => ⟨(h.hSourceW nu beta hz).1,(h.hSourceW nu beta hz).2.2⟩
  hPhase := fun nu => (h.hPhase nu).mono (fun z hz => ⟨hz.1,hz⟩)
  hCut := fun nu => (h.hCut nu).mono (fun z hz => ⟨hz.1,hz⟩)
  hNormal := fun nu => (h.hNormal nu).mono (fun z hz => ⟨hz.1,hz⟩)
  hArgument := fun nu => (h.hArgument nu).mono (fun z hz => ⟨hz.1,hz⟩) }

def fullIncrementNovMeanRawProfilesUnclip
    (n length j Rsub Lprimary : ℕ) (reserve Bnd Mg : ℝ) (T : ℕ → ℝ)
    (F : Ep → M → Ey) (hF : ∀ p, ContMDiff I 𝓘(ℝ,Ey) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (Λ := Label) (Β := Sub) F)
    (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primary : Label → Set (Ep × M))
    (hPrimary : ∀ nu, IsOpen (primary nu))
    (e : OpenPartialHomeomorph M D) (O S : Set X) (tau ell Delta : ℝ)
    (data : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary reserve Bnd Mg T
      F hF g input inputbar W (fun nu => W ∩ primary nu) e O S tau ell Delta) :
    ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary reserve Bnd Mg T
      F hF g input inputbar W primary e O S tau ell Delta := {
  data with
  prim := fullIncrementNovMeanPrimitivesUnclip F hF g input W primary hPrimary data.prim
  primbar := fullIncrementNovMeanPrimitivesUnclip F hF g inputbar W primary hPrimary data.primbar }
end Unclip

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {Sub : Type*} [Fintype Sub]

theorem fullIncrementNov_original_neighborhood_eq_native_domain
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (ip : Fin Data.parameterCount) (G : Set (P × M)) :
    actualOriginalParameterNeighborhood Data ip G = round3ParameterNativeDomain (Data.parameterChart ip) G := by
  ext z
  simp only [actualOriginalParameterNeighborhood,round3ParameterNativeDomain,
    mem_inter_iff,mem_prod,mem_univ,mem_preimage,mem_setOf_eq,and_true]

theorem fullIncrementNov_open_raw_physical_atlas
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
      (fun p x => Data.F (p,x)))
    (hTarget : ∀ nu beta z, z ∈ (g.chart nu beta).target → z.1 ∈ Data.parameterOpen)
    (V0 : Set P) (cT : ℝ) (Tinv Forward Meta : ℕ → ℝ) (Rsub : ℕ)
    (prep : ∀ i, FullIncrementNovOpenNativeMeanPreparation Data hd hs hn g
      (V0 ×ˢ (univ : Set M)) cT Tinv Forward Meta Rsub i)
    (G : Set (P × M)) (hG : IsOpen G)
    (input inputbar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (n q j : ℕ) (reserve Bnd Mg : ℝ) (T : ℕ → ℝ) (tau ell Delta : ℝ)
    (raw : FullIncrementNovOpenNativeMeanRawProfiles Data hd hs hn g V0 cT Tinv Forward Meta Rsub prep
      G hG input inputbar n q j reserve Bnd Mg T tau ell Delta) :
    Nonempty (Round3ParameterMeanRawAtlasData (Tr := ℝ) Data.atlas Data.parameterChart
      (fullIncrementNovOriginalSourceSlice Data) (fullIncrementNov_original_source_slice_smooth Data hd hs)
      (round3Parameter_restrictPrimaryFamily (fullIncrementNovOriginalSourceSlice Data)
        (fullIncrementNovOriginalOpenFamily Data g hTarget) G hG)
      input inputbar n q j Rsub Data.primaryCount reserve Bnd Mg T G Data.primaryDomain
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain
        Data.parameterSet) tau ell Delta) := by
  let W := fun ip => actualOriginalParameterNeighborhood Data ip G
  let Obs := fun i : Fin Data.atlas.count × Fin Data.parameterCount => actualRawObserverOpen (Data.atlas.chart i.1) (W i.2)
  refine ⟨{ observationDomain := Obs, target := fun i z hz => hz.1.2, raw := ?_ }⟩
  intro i
  let z := prep i
  let F := actualOriginalOpenParameterSlice Data i
  let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
  let actual := actualOriginalPrimaryFamily Data hd hs hn i z.host z.native z.slices z.data
    (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)).eta z.active
  let primary := fun nu => round3ParameterNativeDomain (Data.parameterChart i.2) (Data.primaryDomain nu)
  have hPrimary (nu) : IsOpen (primary nu) := round3Parameter_nativeDomain_open _ _ (hd.primary_open nu)
  have hClip : (fun nu => W i.2 ∩ (fun w : Ep × M => ((Data.parameterChart i.2).symm w.1,w.2)) ⁻¹' Data.primaryDomain nu) =
      (fun nu => W i.2 ∩ primary nu) := by
    funext nu
    ext w
    simp only [W,primary,actualOriginalParameterNeighborhood,round3ParameterNativeDomain,
      mem_inter_iff,mem_prod,mem_univ,mem_preimage,mem_setOf_eq,and_true]
    tauto
  have hraw := Classical.choice (raw i)
  change ParameterRound2GlobalMeanRawProfiles (Tr := ℝ) n (q+2) j Rsub Data.primaryCount reserve Bnd Mg T
    F hF (parameterRound2_restrictPrimaryFamily F actual (W i.2)
      (actualOriginalParameterNeighborhood_isOpen Data i.2 G hG))
    (actualOriginalParameterTensorSlice Data i input) (actualOriginalParameterTensorSlice Data i inputbar)
    (W i.2) _ (Data.atlas.chart i.1) (Obs i) _ tau ell Delta at hraw
  rw [hClip] at hraw
  let result := fullIncrementNovMeanRawProfilesUnclip n (q+2) j Rsub Data.primaryCount reserve Bnd Mg T
    F hF (parameterRound2_restrictPrimaryFamily F actual (W i.2)
      (actualOriginalParameterNeighborhood_isOpen Data i.2 G hG))
    (actualOriginalParameterTensorSlice Data i input) (actualOriginalParameterTensorSlice Data i inputbar)
    (W i.2) primary hPrimary (Data.atlas.chart i.1) (Obs i) _ tau ell Delta hraw
  have hSame := fullIncrementNov_prepared_open_family_native_eq Data hd hs hn g hTarget
    (V0 ×ˢ (univ : Set M)) cT Tinv Forward Meta Rsub i z
  have hW := fullIncrementNov_original_neighborhood_eq_native_domain Data i.2 G
  rw [round3Parameter_native_primary_restriction_commutes]
  have result' := result
  dsimp only [actual] at result'
  rw [hSame] at result'
  dsimp only [F,hF,actualOriginalParameterTensorSlice] at result'
  simp only [W,hW] at result'
  exact result'

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.fullIncrementNovMeanPrimitivesUnclip
#print axioms GlobalEmbedding.Continuation.fullIncrementNovMeanRawProfilesUnclip
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_open_raw_physical_atlas
