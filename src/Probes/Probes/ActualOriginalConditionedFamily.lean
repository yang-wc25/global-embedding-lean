import Probes.ActualOriginalConditionedHost
import GlobalEmbedding.Offline.CompactGoodDictionaryTemplates

/-! One positive first/transverse conditioning pair for the SAME finite
constructed host packet. The actual cutoffs, phases, native chart functions
and all slice inverse functions are retained. The finite minimum is a proved
base witness, not an original input profile or an all-order estimate. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function
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

theorem actual_original_host_family_conditioning
    {ι : Type*} [Fintype ι]
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (c : ι → OpenPartialHomeomorph M D) (hc : ∀ i, c i ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (b : ι → OpenPartialHomeomorph X X) (psi : ι → Ep × M → ℝ)
    (e : ι → Ep → OpenPartialHomeomorph M D)
    (hdata : ∀ i, ActualOriginalHostSliceData (c i) (b i) (psi i) (e i))
    (W : ι → Set (Ep × M)) (hW : ∀ i, IsOpen (W i))
    (hFjoint : ∀ i, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ (Function.uncurry F) (W i))
    (hpsi : ∀ i, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (psi i) (W i))
    (hSourceW : ∀ i, (actualHostAdaptedChart (c i) (b i)).source ⊆ W i)
    (eta : ι → Ep × M → ℝ) (hCompact : ∀ i, IsCompact (tsupport (eta i)))
    (hSupport : ∀ i, tsupport (eta i) ⊆ (actualHostAdaptedChart (c i) (b i)).source)
    (hinj : ∀ i, ∀ z ∈ (actualHostAdaptedChart (c i) (b i)).source,
      Function.Injective (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) z.2))
    (hgood : ∀ i, ∀ z ∈ (actualHostAdaptedChart (c i) (b i)).source,
      GoodCovector (F z.1) (hF z.1) z.2
        ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi i z)).toContinuousLinearMap.comp
          (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => psi i (z.1,x)) z.2))) :
    ∃ (cF cT : ℝ) (b' : ι → OpenPartialHomeomorph X X)
        (e' : ι → Ep → OpenPartialHomeomorph M D),
      0 < cF ∧ 0 < cT ∧ ∀ i,
        (b' i).source ⊆ (b i).source ∧ (b' i).target ⊆ (b i).target ∧
        (b' i : X → X) = b i ∧ ((b' i).symm : X → X) = (b i).symm ∧
        ActualOriginalHostSliceData (c i) (b' i) (psi i) (e' i) ∧
        tsupport (eta i) ⊆ (actualHostAdaptedChart (c i) (b' i)).source ∧
        (actualHostAdaptedChart (c i) (b' i)).source ⊆ W i ∧
        (∀ p, ((e' i p).symm : D → M) = (e i p).symm) ∧
        (∀ z ∈ (b' i).target, ∀ v : D,
          cF*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e' i z.1).symm) z.2 v‖^2) ∧
        ∀ z ∈ (b' i).target, ∀ v : Tdata,
          cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
            (F z.1) (hF z.1) (e' i z.1).symm z.2 v‖^2 := by
  have hw (i : ι) := actual_original_host_cutoff_conditioned_chart F hF (c i) (hc i)
    (b i) (psi i) (e i) (hdata i) (W i) (hW i) (hFjoint i) (hpsi i) (hSourceW i)
    (eta i) (hCompact i) (hSupport i) (hinj i) (hgood i)
  choose cf ct b' e' hp using hw
  obtain ⟨cF,hcF,hcf⟩ := finite_positive_common_lower_bound cf (fun i => (hp i).1)
  obtain ⟨cT,hcT,hct⟩ := finite_positive_common_lower_bound ct (fun i => (hp i).2.1)
  refine ⟨cF,cT,b',e',hcF,hcT,?_⟩
  intro i
  rcases hp i with ⟨_,_,hs,ht,hb,hbi,hd,hSup,hW',hInv,hFb,hTb⟩
  refine ⟨hs,ht,hb,hbi,hd,hSup,hW',hInv,?_,?_⟩
  · intro z hz v
    exact (mul_le_mul_of_nonneg_right (hcf i) (sq_nonneg _)).trans (hFb z hz v)
  · intro z hz v
    exact (mul_le_mul_of_nonneg_right (hct i) (sq_nonneg _)).trans (hTb z hz v)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_host_family_conditioning
