import Repair.FullIncrementNovOpenRawAtlas

/-! The actual final raw producer with its original observation domains retained
in the public result. This prevents an opaque nonempty witness from hiding
the canonical domain required by the genuine secondary raw assembly. -/

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
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {Sub : Type*} [Fintype Sub]

theorem fullIncrementNov_open_canonical_raw_physical_atlas
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
    ∃ out : Round3ParameterMeanRawAtlasData (Tr := ℝ) Data.atlas Data.parameterChart
      (fullIncrementNovOriginalSourceSlice Data) (fullIncrementNov_original_source_slice_smooth Data hd hs)
      (round3Parameter_restrictPrimaryFamily (fullIncrementNovOriginalSourceSlice Data)
        (fullIncrementNovOriginalOpenFamily Data g hTarget) G hG)
      input inputbar n q j Rsub Data.primaryCount reserve Bnd Mg T G Data.primaryDomain
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain
        Data.parameterSet) tau ell Delta,
      out.observationDomain = fun i => actualRawObserverOpen (Data.atlas.chart i.1)
        (round3ParameterNativeDomain (Data.parameterChart i.2) G) := by
  let W := fun ip => actualOriginalParameterNeighborhood Data ip G
  let Obs := fun i : Fin Data.atlas.count × Fin Data.parameterCount => actualRawObserverOpen (Data.atlas.chart i.1) (W i.2)
  refine ⟨{ observationDomain := Obs, target := fun i z hz => hz.1.2, raw := ?_ },?_⟩
  swap
  · funext i
    exact congrArg (actualRawObserverOpen (Data.atlas.chart i.1))
      (fullIncrementNov_original_neighborhood_eq_native_domain Data i.2 G)
  · intro i
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
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_open_canonical_raw_physical_atlas
