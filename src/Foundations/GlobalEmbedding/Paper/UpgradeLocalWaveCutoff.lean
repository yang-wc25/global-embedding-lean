import GlobalEmbedding.Paper.NormalSpace
import GlobalEmbedding.Paper.SupportedRankLegalVariation
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-! Actual native bump and global literal wave in main.tex840–843/1053–1057.
DAG: upgrade-local-wave-cutoff. Internal local fields are constructed in the
full original consumer; no new generic germ, cutoff or bundle calculus. -/

noncomputable section
open Bundle Filter Manifold Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

/-- Native bump localization of the actual local phase and actual normal section
gives a globally smooth literal legal rank-one tensor with its exact value at x.

Proof: use the native manifold bump neighborhood basis inside U minus y. Near
its support, the actual phase derivative applied to either actual inverse-frame
section is smooth: compose the native tangent map with the smooth actual frame
section and the native real-tangent fibre projection. Native multiplication and
scalar multiplication give the literal tensor coefficient. Off the topological
support the bump and tensor vanish locally, so the zero germ is smooth. This
works in every original tangent chart, without junk-value assumptions off U.
At x the native bump is one. Source: defn:legal and thm:upgrade1053–1057. -/
theorem upgrade_exists_local_wave_cutoff
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {N : ℕ}
    (F : M → EuclideanSpace ℝ (Fin N))
    (U : Set M) (hU : IsOpen U) (x y : M) (hx : x ∈ U) (hxy : x ≠ y)
    (psi : M → ℝ) (hpsi : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ psi U)
    (v : ∀ z : M, normalSpace (I := I) F z)
    (hv : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
      (fun z ↦ (v z : EuclideanSpace ℝ (Fin N))) U) :
    ∃ chi : SmoothBumpFunction I x,
      tsupport (chi : M → ℝ) ⊆ U ∧ y ∉ tsupport (chi : M → ℝ) ∧
      let A (z : M) : SymmetricSquare (TangentSpace I z) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin N) :=
        chi z • supportedRankLegalVariation
          (mfderiv I 𝓘(ℝ, ℝ) psi z).toLinearMap (v z : EuclideanSpace ℝ (Fin N))
      (∀ (a : M) (u w : E),
        ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
          (fun z ↦ A z (symmetricSquareProduct (TangentSpace I z)
            ((trivializationAt E (TangentSpace I) a).symmL ℝ z u)
            ((trivializationAt E (TangentSpace I) a).symmL ℝ z w)))
          (chartAt H a).source) ∧
      A x = supportedRankLegalVariation (mfderiv I 𝓘(ℝ, ℝ) psi x).toLinearMap
        (v x : EuclideanSpace ℝ (Fin N)) := by
  have htarget : U ∩ ({y} : Set M)ᶜ ∈ 𝓝 x :=
    inter_mem (hU.mem_nhds hx)
      (isClosed_singleton.isOpen_compl.mem_nhds (by simpa using hxy))
  obtain ⟨chi, _, hchi⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp htarget
  refine ⟨chi, fun z hz ↦ (hchi hz).1, ?_, ?_⟩
  · intro hy
    exact (hchi hy).2 (by simp)
  · dsimp only
    constructor
    · intro a u w z hz
      let e := trivializationAt E (TangentSpace I) a
      let T (p : M) := chi p • supportedRankLegalVariation
        (mfderiv I 𝓘(ℝ, ℝ) psi p).toLinearMap (v p : EuclideanSpace ℝ (Fin N))
          (symmetricSquareProduct (TangentSpace I p)
            (e.symmL ℝ p u) (e.symmL ℝ p w))
      have hT (p : M) : T p = chi p •
          ((NormedSpace.fromTangentSpace (psi p)
            (mfderiv I 𝓘(ℝ, ℝ) psi p (e.symmL ℝ p u)) *
            NormedSpace.fromTangentSpace (psi p)
              (mfderiv I 𝓘(ℝ, ℝ) psi p (e.symmL ℝ p w))) •
              (v p : EuclideanSpace ℝ (Fin N))) := by
        change chi p • supportedRankLegalVariation
          (show TangentSpace I p →ₗ[ℝ] ℝ from
            (mfderiv I 𝓘(ℝ, ℝ) psi p).toLinearMap) _ _ = _
        rw [supportedRankLegalVariation_product]
        rfl
      have hAt : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ T z := by
        by_cases ht : z ∈ tsupport (chi : M → ℝ)
        · have hzU := (hchi ht).1
          have hpAt := (hpsi z hzU).contMDiffAt (hU.mem_nhds hzU)
          have hvAt := (hv z hzU).contMDiffAt (hU.mem_nhds hzU)
          have hs (k : E) : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
              (fun p ↦ (⟨p, e.symmL ℝ p k⟩ : TangentBundle I M)) z := by
            apply (e.contMDiffAt_section_iff (IB := I) (n := ∞) hz).mpr
            apply contMDiffAt_const.congr_of_eventuallyEq
            filter_upwards [e.open_baseSet.mem_nhds hz] with p hp
            change (e ⟨p, e.symmL ℝ p k⟩).2 = k
            rw [← e.continuousLinearMapAt_apply_of_mem ℝ hp]
            exact e.continuousLinearMapAt_symmL hp k
          have hd (k : E) : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
              (fun p ↦ NormedSpace.fromTangentSpace (psi p)
                (mfderiv I 𝓘(ℝ, ℝ) psi p (e.symmL ℝ p k))) z := by
            have hm := hpAt.contMDiffAt_tangentMap
              (X := (⟨z, e.symmL ℝ z k⟩ : TangentBundle I M)) (m := ∞) (by simp)
            have hc := hm.comp z (hs k)
            exact (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).contMDiffAt.comp z hc
          have hscalar := contDiff_mul.comp_contMDiffAt ((hd u).prodMk_space (hd w))
          have hwave := chi.contMDiffAt.smul (hscalar.smul hvAt)
          exact hwave.congr_of_eventuallyEq (Eventually.of_forall hT)
        · apply contMDiffAt_const.congr_of_eventuallyEq
          filter_upwards [(isClosed_tsupport (chi : M → ℝ)).isOpen_compl.mem_nhds ht]
            with p hp
          rw [hT p, image_eq_zero_of_notMem_tsupport hp, zero_smul]
      exact hAt.contMDiffWithinAt
    · rw [chi.eq_one, one_smul]

#print axioms upgrade_exists_local_wave_cutoff

end GlobalEmbedding.Paper
