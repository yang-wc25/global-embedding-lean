import Smoothing.Round3ParameterMeanRawAtlas
import Smoothing.Round3ParameterNativeRestriction
import Probes.Round3ParameterCanonicalRefinementSupply
import Probes.ActualIncrementRawObserverDomains

/-! Whole-P original native raw profiles are assembled into the actual
single-physical-family mean atlas. Canonical restriction equality is used,
so no independent per-chart mean operator or local increment is introduced. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
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

private theorem meanRawProfile_restricted_heq
    {Sub Label : Type*} [Fintype Sub] [Fintype Label]
    {F F' : Ep → M → Ey} (hEq : F = F')
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
    (hF' : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F' p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (Λ := Label) (Β := Sub) F)
    (g' : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (Λ := Label) (Β := Sub) F')
    (hg : HEq g g')
    (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (n length j Rsub Lprimary : ℕ) (reserve Bnd Mg : ℝ) (T : ℕ → ℝ)
    (W : Set (Ep × M)) (hW : IsOpen W) (primary : Label → Set (Ep × M))
    (obs : OpenPartialHomeomorph M D) (O S : Set X) (tau ell Delta : ℝ) :
    Nonempty (ParameterRound2GlobalMeanRawProfiles (Tr := ℝ) n length j Rsub Lprimary reserve Bnd Mg T
      F hF (parameterRound2_restrictPrimaryFamily F g W hW) input inputbar W primary obs O S tau ell Delta) ↔
    Nonempty (ParameterRound2GlobalMeanRawProfiles (Tr := ℝ) n length j Rsub Lprimary reserve Bnd Mg T
      F' hF' (parameterRound2_restrictPrimaryFamily F' g' W hW) input inputbar W primary obs O S tau ell Delta) := by
  cases hEq
  cases eq_of_heq hg
  rfl

theorem round3Parameter_original_canonical_mean_atlas
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hAll : Data.parameterSet = univ)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (p,x)))
    {Sub : Type*} [Fintype Sub]
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
      (fun p x => Data.F (p,x)))
    (input inputbar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (n q j Rsub Lprimary : ℕ) (reserve Bnd Mg : ℝ) (T : ℕ → ℝ) (tau ell Delta : ℝ)
    (hRaw : ∀ i : Fin Data.atlas.count × Fin Data.parameterCount,
      ∃ g0 : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
        (actualOriginalOpenParameterSlice Data i),
      HEq g0 (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)) ∧
      let W := actualOriginalParameterNeighborhood Data i.2 univ
      let hW := actualOriginalParameterNeighborhood_isOpen Data i.2 univ isOpen_univ
      Nonempty (ParameterRound2GlobalMeanRawProfiles (Tr := ℝ) n (q+2) j Rsub Lprimary reserve Bnd Mg T
        (actualOriginalOpenParameterSlice Data i) (actualOriginalOpenParameterSlice_contMDiff Data hd hs i)
        (parameterRound2_restrictPrimaryFamily (actualOriginalOpenParameterSlice Data i) g0 W hW)
        (actualOriginalParameterTensorSlice Data i input) (actualOriginalParameterTensorSlice Data i inputbar)
        W (fun nu => W ∩ (fun z : Ep × M => ((Data.parameterChart i.2).symm z.1,z.2)) ⁻¹' Data.primaryDomain nu)
        (Data.atlas.chart i.1) (actualRawObserverOpen (Data.atlas.chart i.1) W)
        ((parameterTensorModelEquiv (m+1) d) ⁻¹' incrementsOriginalEvaluation Data.atlas Data.parameterChart
          Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i) tau ell Delta)) :
    ∃ out : Round3ParameterMeanRawAtlasData (Tr := ℝ) Data.atlas Data.parameterChart
      (fun p x => Data.F (p,x)) hF
      (round3Parameter_restrictPrimaryFamily (fun p x => Data.F (p,x)) g univ isOpen_univ)
      input inputbar n q j Rsub Lprimary reserve Bnd Mg T univ Data.primaryDomain
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) tau ell Delta,
      out.observationDomain = fun i => actualRawObserverOpen (Data.atlas.chart i.1)
        (round3ParameterNativeDomain (Data.parameterChart i.2) (univ : Set (P × M))) := by
  let W := fun ip => actualOriginalParameterNeighborhood Data ip univ
  let O := fun i : Fin Data.atlas.count × Fin Data.parameterCount => actualRawObserverOpen (Data.atlas.chart i.1)
    (round3ParameterNativeDomain (Data.parameterChart i.2) (univ : Set (P × M)))
  refine ⟨{ observationDomain := O, target := ?_, raw := ?_ },rfl⟩
  · intro i z hz
    exact hz.1.2
  · intro i
    apply Classical.choice
    obtain ⟨g0,hSame,hraw⟩ := hRaw i
    have h' := (meanRawProfile_restricted_heq
      (round3Parameter_original_open_slice_eq_global Data hd hAll i)
      (actualOriginalOpenParameterSlice_contMDiff Data hd hs i)
      (fun p => hF ((Data.parameterChart i.2).symm p)) g0
      (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)) hSame
      (actualOriginalParameterTensorSlice Data i input) (actualOriginalParameterTensorSlice Data i inputbar)
      n (q+2) j Rsub Lprimary reserve Bnd Mg T (W i.2)
      (actualOriginalParameterNeighborhood_isOpen Data i.2 univ isOpen_univ) _ _ _ _ tau ell Delta).mp hraw
    have hW : W i.2 = round3ParameterNativeDomain (Data.parameterChart i.2) (univ : Set (P × M)) := by
      ext z
      simp only [W,actualOriginalParameterNeighborhood,round3ParameterNativeDomain,mem_inter_iff,mem_prod,
        mem_univ,mem_preimage,mem_setOf_eq,and_true]
    have hPrimary : (fun nu => W i.2 ∩ (fun z : Ep × M => ((Data.parameterChart i.2).symm z.1,z.2)) ⁻¹' Data.primaryDomain nu) =
        (fun nu => round3ParameterNativeDomain (Data.parameterChart i.2) (Data.primaryDomain nu)) := by
      funext nu
      ext z
      simp only [W,actualOriginalParameterNeighborhood,round3ParameterNativeDomain,mem_inter_iff,mem_prod,
        mem_univ,mem_preimage,mem_setOf_eq,and_true]
    rw [hPrimary] at h'
    rw [round3Parameter_native_primary_restriction_commutes]
    have hW' : actualOriginalParameterNeighborhood Data i.2 univ =
        round3ParameterNativeDomain (Data.parameterChart i.2) (univ : Set (P × M)) := hW
    have hi : actualOriginalParameterTensorSlice Data i input = fun p => input ((Data.parameterChart i.2).symm p) := rfl
    have hi' : actualOriginalParameterTensorSlice Data i inputbar = fun p => inputbar ((Data.parameterChart i.2).symm p) := rfl
    simpa only [O,W,hW',hi,hi'] using h'

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_original_canonical_mean_atlas
