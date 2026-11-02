import Probes.ActualIncrementSupportConditioning
import Probes.ActualOriginalHostCompactCutoffs
import Probes.ActualOriginalHostTargetRestriction

/-! Actual compact host support, with Good assumed only on that support,
produces an open conditioned chart. The actual chart and inverse functions,
phase and cutoff are unchanged. In particular this applies to signed secondary
phases whose original Good requirement is confined to a support intersection.
The numerical first/transverse margins are outputs before all later jet orders. -/

noncomputable section
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem actual_original_compact_carrier_conditioned_host
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (c : OpenPartialHomeomorph M D) (hc : c ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (b : OpenPartialHomeomorph X X) (psi : Ep × M → ℝ)
    (e : Ep → OpenPartialHomeomorph M D) (hdata : ActualOriginalHostSliceData c b psi e)
    (W : Set (Ep × M)) (hW : IsOpen W)
    (hFjoint : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ (Function.uncurry F) W)
    (hpsi : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ psi W)
    (hSourceW : (actualHostAdaptedChart c b).source ⊆ W)
    (carrier : Set (Ep × M)) (hCompact : IsCompact carrier)
    (hSupport : carrier ⊆ (actualHostAdaptedChart c b).source)
    (hinj : ∀ z ∈ (actualHostAdaptedChart c b).source,
      Function.Injective (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) z.2))
    (hgood : ∀ z ∈ carrier,
      GoodCovector (F z.1) (hF z.1) z.2
        ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi z)).toContinuousLinearMap.comp
          (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => psi (z.1,x)) z.2))) :
    ∃ (cF cT : ℝ) (b' : OpenPartialHomeomorph X X)
        (e' : Ep → OpenPartialHomeomorph M D),
      0 < cF ∧ 0 < cT ∧ b'.source ⊆ b.source ∧ b'.target ⊆ b.target ∧
      (b' : X → X) = b ∧ (b'.symm : X → X) = b.symm ∧
      ActualOriginalHostSliceData c b' psi e' ∧
      carrier ⊆ (actualHostAdaptedChart c b').source ∧
      (actualHostAdaptedChart c b').source ⊆ W ∧
      (∀ p, ((e' p).symm : D → M) = (e p).symm) ∧
      (∀ z ∈ b'.target, ∀ v : D,
        cF*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e' z.1).symm) z.2 v‖^2) ∧
      ∀ z ∈ b'.target, ∀ v : Tdata,
        cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
          (F z.1) (hF z.1) (e' z.1).symm z.2 v‖^2 := by
  let a := actualHostAdaptedChart c b
  have hg := actual_host_slice_geometry_inputs c hc b psi e hdata
  have hpoint := actual_host_slice_source_point c b psi e hdata
  have hdata0 := hdata
  obtain ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩ := hdata
  let K := a '' carrier
  have hK : IsCompact K := hCompact.image_of_continuousOn (a.continuousOn.mono hSupport)
  have hKO : K ⊆ b.target := by
    rintro _ ⟨z,hz,rfl⟩
    rw [← hat]
    exact a.map_source (hSupport hz)
  have hci : ContMDiffOn 𝓘(ℝ,X) 𝓙 ∞ (fun z => (e z.1).symm z.2) b.target := by
    have hh := (contMDiff_snd.comp_contMDiffOn hai).mono (by rw [hat] : b.target ⊆ a.target)
    apply hh.congr
    intro z hz
    exact (congrArg Prod.snd (hpair z hz)).symm
  have hGoodK (z : X) (hz : z ∈ K) :
      GoodCovector (F z.1) (hF z.1) ((e z.1).symm z.2)
        ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi (z.1,(e z.1).symm z.2))).toContinuousLinearMap.comp
          (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => psi (z.1,x)) ((e z.1).symm z.2))) := by
    have hs : (z.1,(e z.1).symm z.2) ∈ carrier := by
      obtain ⟨w,hw,heq⟩ := hz
      have hback : (z.1,(e z.1).symm z.2) = w := by
        rw [← hpair z (hKO ⟨w,hw,heq⟩),← heq]
        exact a.left_inv (hSupport hw)
      rwa [hback]
    exact hgood _ hs
  obtain ⟨cF,cT,O0,hcF,hcT,hO0,hKO,hOb,hFb,hTb⟩ :=
    actual_increment_support_only_good_open_reserves F hF e he (fun p x => psi (p,x))
      W b.target b.open_target hFjoint hpsi hci (fun z hz => (hg.2.2.2.1 z hz).1)
      (fun z hz => hSourceW (hpoint z hz)) hW
      (fun z hz => hinj _ (hpoint z hz)) hadapt K hK hKO hGoodK
  obtain ⟨b',e',hTarget,hSource,hb,hbi,hdata',hSourceEq,hInverse⟩ :=
    actual_original_host_restrict_target c hc b psi e hdata0 O0 hO0 hOb
  have hSubset : b'.target ⊆ b.target := by rwa [hTarget]
  refine ⟨cF,cT,b',e',hcF,hcT,hSource,hSubset,hb,hbi,hdata',?_,?_,hInverse,?_,?_⟩
  · rw [hSourceEq]
    intro z hz
    exact ⟨hSupport hz,hKO ⟨z,hz,rfl⟩⟩
  · rw [hSourceEq]
    exact inter_subset_left.trans hSourceW
  · intro z hz v
    rw [hInverse z.1]
    exact hFb z (by rwa [hTarget] at hz) v
  · intro z hz v
    rw [hInverse z.1]
    exact hTb z (by rwa [hTarget] at hz) v

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_compact_carrier_conditioned_host
