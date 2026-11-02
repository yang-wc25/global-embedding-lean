import Probes.ActualOriginalCutoffOpenReserves
import Probes.ActualOriginalHostTargetRestriction

/-! A constructed chart with its actual chosen-frame conditioning.

The original immersion/Good hypotheses and the actual compact cutoff carrier
produce the numerical reserves. The same chart is restricted to the proved
conditioning neighborhood; its two native functions and all slice inverse
functions remain unchanged. The actual cutoff stays inside its source.
All choices precede every later derivative order.
-/

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

theorem actual_original_host_cutoff_conditioned_chart
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (c : OpenPartialHomeomorph M D) (hc : c ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (b : OpenPartialHomeomorph X X) (psi : Ep × M → ℝ)
    (e : Ep → OpenPartialHomeomorph M D) (hdata : ActualOriginalHostSliceData c b psi e)
    (W : Set (Ep × M)) (hW : IsOpen W)
    (hFjoint : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ (Function.uncurry F) W)
    (hpsi : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ psi W)
    (hSourceW : (actualHostAdaptedChart c b).source ⊆ W)
    (eta : Ep × M → ℝ) (hCompact : IsCompact (tsupport eta))
    (hSupport : tsupport eta ⊆ (actualHostAdaptedChart c b).source)
    (hinj : ∀ z ∈ (actualHostAdaptedChart c b).source,
      Function.Injective (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) z.2))
    (hgood : ∀ z ∈ (actualHostAdaptedChart c b).source,
      GoodCovector (F z.1) (hF z.1) z.2
        ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi z)).toContinuousLinearMap.comp
          (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => psi (z.1,x)) z.2))) :
    ∃ (cF cT : ℝ) (b' : OpenPartialHomeomorph X X)
        (e' : Ep → OpenPartialHomeomorph M D),
      0 < cF ∧ 0 < cT ∧ b'.source ⊆ b.source ∧ b'.target ⊆ b.target ∧
      (b' : X → X) = b ∧ (b'.symm : X → X) = b.symm ∧
      ActualOriginalHostSliceData c b' psi e' ∧
      tsupport eta ⊆ (actualHostAdaptedChart c b').source ∧
      (actualHostAdaptedChart c b').source ⊆ W ∧
      (∀ p, ((e' p).symm : D → M) = (e p).symm) ∧
      (∀ z ∈ b'.target, ∀ v : D,
        cF*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e' z.1).symm) z.2 v‖^2) ∧
      ∀ z ∈ b'.target, ∀ v : Tdata,
        cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
          (F z.1) (hF z.1) (e' z.1).symm z.2 v‖^2 := by
  obtain ⟨cF,cT,O0,hcF,hcT,hO0,hKO,hOb,hFb,hTb⟩ :=
    actual_original_host_cutoff_open_reserves F hF c hc b psi e hdata W hW hFjoint hpsi
      hSourceW eta hCompact hSupport hinj hgood
  obtain ⟨b',e',hTarget,hSource,hb,hbi,hdata',hSourceEq,hInverse⟩ :=
    actual_original_host_restrict_target c hc b psi e hdata O0 hO0 hOb
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

#print axioms GlobalEmbedding.Continuation.actual_original_host_cutoff_conditioned_chart
