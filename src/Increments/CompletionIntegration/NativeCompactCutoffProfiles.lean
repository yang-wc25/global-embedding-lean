import Probes.Round3PreparedCompactProfiles
import Probes.Round3PreparedParameterSecondaryHostCutoffProfiles

/-!
# Whole original host-target jets from an actual compact cutoff

The compact object is the support of the already constructed cutoff. The
observation domain is the whole original chart target and is not replaced
by a compact set. Off the image of the physical support the actual pullback
has a zero germ, including at order zero. No bound on its jets is an input.
-/

noncomputable section
open Set Function Filter Manifold IsManifold
open scoped ContDiff Topology Classical

namespace GlobalEmbedding.Continuation

theorem compact_supported_original_chart_profiles
    {A E F : Type*} [TopologicalSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (chart : OpenPartialHomeomorph A E) (f : A → F)
    (hCompact : IsCompact (tsupport f)) (hSupport : tsupport f ⊆ chart.source)
    (hSmooth : ContDiffOn ℝ ∞ (f ∘ chart.symm) chart.target) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ k z, z ∈ chart.target →
        ell^k * ‖iteratedFDeriv ℝ k (f ∘ chart.symm) z‖ ≤ C k ∧
        ell^(k-1) * ‖iteratedFDeriv ℝ k (f ∘ chart.symm) z‖ ≤ C k := by
  let K : Set E := chart '' tsupport f
  have hK : IsCompact K :=
    hCompact.image_of_continuousOn (chart.continuousOn.mono hSupport)
  have hKT : K ⊆ chart.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact chart.map_source (hSupport hx)
  obtain ⟨C, hC, hBound⟩ := round3_prepared_compact_profiles
    (f ∘ chart.symm) chart.target K chart.open_target hK hKT hSmooth
  refine ⟨C, hC, ?_⟩
  intro ell hell hell1 k z hz
  by_cases hzK : z ∈ K
  · exact hBound ell hell hell1 k z hzK
  · have hn : chart.symm z ∉ tsupport f := by
      intro h
      exact hzK ⟨chart.symm z, h, chart.right_inv hz⟩
    have hZero : (f ∘ chart.symm) =ᶠ[𝓝 z] (fun _ : E => (0 : F)) :=
      (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
        (chart.symm.continuousOn.continuousAt (chart.open_target.mem_nhds hz))
    have hJet : iteratedFDeriv ℝ k (f ∘ chart.symm) z = 0 := by
      rw [(hZero.iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds]
      simp
    simp only [hJet, norm_zero, mul_zero]
    exact ⟨hC k, hC k⟩

variable {m d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]

local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

/-- A genuine compact native cutoff supplies every host-coordinate order on
the unchanged, possibly noncompact host target. -/
theorem native_compact_cutoff_whole_host_profiles
    (host : OpenPartialHomeomorph M D) (hHost : host ∈ maximalAtlas 𝓙 ∞ M)
    (rho : Ep × M → ℝ)
    (hRho : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ rho)
    (hCompact : IsCompact (tsupport rho))
    (hSupport : tsupport rho ⊆ (univ : Set Ep) ×ˢ host.source) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ (k : ℕ) (z : X),
        z.2 ∈ host.target →
        ell^k * ‖iteratedFDeriv ℝ k
          (fun y : X => rho (y.1,host.symm y.2)) z‖ ≤ C k := by
  let q := (OpenPartialHomeomorph.refl Ep).prod host
  have hPull : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
      (fun y : X => (y.1,host.symm y.2)) q.target :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk
      ((contMDiffOn_symm_of_mem_maximalAtlas hHost).comp
        contDiff_snd.contMDiff.contMDiffOn (fun _ hz => hz.2))
  have hSmooth : ContDiffOn ℝ ∞ (rho ∘ q.symm) q.target :=
    (hRho.comp_contMDiffOn hPull).contDiffOn
  obtain ⟨C, hC, hBound⟩ := compact_supported_original_chart_profiles q rho
    hCompact hSupport hSmooth
  exact ⟨C, hC, fun ell hell hell1 k z hz =>
    (hBound ell hell hell1 k z ⟨mem_univ _, hz⟩).1⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.compact_supported_original_chart_profiles
#print axioms GlobalEmbedding.Continuation.native_compact_cutoff_whole_host_profiles
