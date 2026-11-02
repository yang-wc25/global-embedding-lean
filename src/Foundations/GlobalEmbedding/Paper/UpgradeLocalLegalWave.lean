import GlobalEmbedding.Paper.UpgradeLocalLinearPhase
import GlobalEmbedding.Paper.UpgradeLocalTrueFormCoefficients
import GlobalEmbedding.Paper.UpgradeLocalKernelTransport
import GlobalEmbedding.Paper.UpgradeLocalFreeNormalProjection
import GlobalEmbedding.Paper.UpgradeLocalWaveCutoff
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.TensorProduct.Finite
import GlobalEmbedding.Paper.GoodCovector
import GlobalEmbedding.Paper.SupportedRankLegalVariation
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Actual local legal waves through original good cotangents and legal normals

Source: original main.tex, Definition Legal waves 840–843 and the local
realization step of thm:upgrade 1053–1057. DAG: upgrade-local-legal-wave.
Stage2 full native-object statement draft; ROOT statement review pending.
-/

noncomputable section
open Bundle Filter Manifold Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

/-- An actual smooth immersion, an actual good cotangent at x and any original
legal normal value admit a smooth local phase and legal normal section through
those data, cut off by a native smooth chart bump equal to one near x and whose
topological support avoids y. The resulting LITERAL original quotient tensor is
smooth in every actual local tangent frame. The legal normal field may vanish.

Proof: in the actual tangent chart at x transport xi to a fixed model covector
eta and take the chart-linear phase eta composed with the extended chart. Actual
chart differentiation identifies its differential and fixed coordinate kernel.
Restrict the accepted actual smooth true second-form bundle map to Sym2 ker eta;
native finite coordinates give its actual finite-domain coefficient operator A.
At x Good gives injectivity, which persists on an open chart neighborhood by
native operator injective openness. Hence dpsi remains genuinely Good there.
The actual range of A lies in the actual normal space. The accepted normal
projection PN and actual image projection PA are smooth by the same accepted
Gram formula and manifold Gram coefficients. Apply PN-PA to the supplied ambient
normal value: this is normal and perpendicular to the actual restricted image,
and at x it is the original legal nu. Extend this pointwise normal section by
zero outside the neighborhood; only its smoothness inside is asserted. Shrink
away from y, take a native SmoothBumpFunction whose topological support lies in
the neighborhood, and multiply its literal legal rank-one column by this bump.
Actual derivative-section smoothness gives every tangent-frame coefficient
smooth near the support; outside topological support it vanishes locally.
Native smoothness on topological support proves global coefficient smoothness.
Native bump value one and the two prescribed values give the exact column at x.
No desired local extension, normal trivialization, rank condition or unit/nonzero
normal value is supplied. Source: defn:legal and thm:upgrade1053–1057. -/
theorem upgrade_exists_local_legal_wave
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] [T2Space M] {N : ℕ}
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (x y : M) (hxy : x ≠ y)
    (xi : TangentSpace I x →L[ℝ] ℝ) (hxi : GoodCovector F hF x xi)
    (nu : normalSpace (I := I) F x)
    (hnu : nu ∈ supportedRankLegalValueSpace (trueSecondForm F hF x) xi.toLinearMap) :
    ∃ (U : Set M) (psi : M → ℝ) (v : ∀ z : M, normalSpace (I := I) F z)
      (chi : SmoothBumpFunction I x),
      IsOpen U ∧ x ∈ U ∧ U ⊆ (chartAt H x).source ∧
      tsupport (chi : M → ℝ) ⊆ U ∧ y ∉ tsupport (chi : M → ℝ) ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ psi U ∧
      mfderiv I 𝓘(ℝ, ℝ) psi x = xi ∧ v x = nu ∧
      ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
        (fun z ↦ (v z : EuclideanSpace ℝ (Fin N))) U ∧
      (∀ z ∈ U, GoodCovector F hF z (mfderiv I 𝓘(ℝ, ℝ) psi z) ∧
        v z ∈ supportedRankLegalValueSpace (trueSecondForm F hF z)
          (mfderiv I 𝓘(ℝ, ℝ) psi z).toLinearMap) ∧
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
      A x = supportedRankLegalVariation xi.toLinearMap (nu : EuclideanSpace ℝ (Fin N)) := by
  classical
  let r := Module.finrank ℝ (SymmetricSquare xi.ker)
  let D := EuclideanSpace ℝ (Fin r)
  let bD := Module.finBasisOfFinrankEq ℝ D (show Module.finrank ℝ D = r by simp [D])
  let bQ := Module.finBasis ℝ (SymmetricSquare xi.ker)
  let b : D ≃ₗ[ℝ] SymmetricSquare xi.ker := bD.equivFun.trans bQ.equivFun.symm
  let j : D →ₗ[ℝ] SymmetricSquare E :=
    (symmetricSquareLinearMap xi.ker.subtype).comp b.toLinearMap
  obtain ⟨psi, hpsi, hchain, hpsix⟩ := upgrade_exists_local_linear_phase x xi
  obtain ⟨A, hA, hAval⟩ := upgrade_exists_true_form_coefficients F hF himm x j
  have hC (z : M) (hz : z ∈ (chartAt H x).source) :
      ∃ C : D ≃ₗ[ℝ] SymmetricSquare (mfderiv I 𝓘(ℝ, ℝ) psi z).ker,
        ∀ d, A z d = (trueSecondForm F hF z
          (symmetricSquareLinearMap (mfderiv I 𝓘(ℝ, ℝ) psi z).ker.subtype (C d)) :
            EuclideanSpace ℝ (Fin N)) := by
    obtain ⟨C, hCd⟩ := upgrade_local_kernel_true_form_transport F hF x z hz xi psi
      (hchain z hz) b
    refine ⟨C, fun d ↦ (hAval z d).trans (hCd d)⟩
  have hAx : Function.Injective (A x) := by
    have hCx := hC x (mem_chart_source H x)
    rw [hpsix] at hCx
    obtain ⟨C, hCd⟩ := hCx
    intro d₁ d₂ hd
    apply C.injective
    apply hxi.2
    apply Subtype.ext
    change (trueSecondForm F hF x
      (symmetricSquareLinearMap xi.ker.subtype (C d₁)) : EuclideanSpace ℝ (Fin N)) =
      (trueSecondForm F hF x
        (symmetricSquareLinearMap xi.ker.subtype (C d₂)) : EuclideanSpace ℝ (Fin N))
    exact (hCd d₁).symm.trans (hd.trans (hCd d₂))
  have hAt := hA.contMDiffAt ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
  have hnear : ∀ᶠ z in 𝓝 x, Function.Injective (A z) :=
    hAt.continuousAt.eventually (ContinuousLinearMap.isOpen_injective.mem_nhds hAx)
  have hnear' : ∀ᶠ z in 𝓝 x,
      z ∈ (chartAt H x).source ∧ Function.Injective (A z) := by
    filter_upwards [hnear, (chartAt H x).open_source.mem_nhds (mem_chart_source H x)]
      with z hinj hz
    exact ⟨hz, hinj⟩
  obtain ⟨U, hUdata, hU, hxU⟩ := eventually_nhds_iff.mp hnear'
  have hUsub : U ⊆ (chartAt H x).source := fun z hz ↦ (hUdata z hz).1
  have hUinj : ∀ z ∈ U, Function.Injective (A z) := fun z hz ↦ (hUdata z hz).2
  have hnz (z : M) (hz : z ∈ U) : mfderiv I 𝓘(ℝ, ℝ) psi z ≠ 0 := by
    intro hzero
    apply hxi.1
    apply ContinuousLinearMap.ext
    intro a
    obtain ⟨w, hw⟩ :=
      (isInvertible_mfderiv_extChartAt (I := I) (x := x) (y := z)
        (by simpa using hUsub hz)).surjective a
    have hc := DFunLike.congr_fun ((hchain z (hUsub hz)).symm.trans hzero) w
    change xi (mfderiv I 𝓘(ℝ, E) (extChartAt I x) z w) = 0 at hc
    rw [hw] at hc
    exact hc
  have hgood (z : M) (hz : z ∈ U) :
      GoodCovector F hF z (mfderiv I 𝓘(ℝ, ℝ) psi z) := by
    refine ⟨hnz z hz, ?_⟩
    obtain ⟨C, hCd⟩ := hC z (hUsub hz)
    intro q₁ q₂ hq
    obtain ⟨d₁, rfl⟩ := C.surjective q₁
    obtain ⟨d₂, rfl⟩ := C.surjective q₂
    apply congrArg C
    apply hUinj z hz
    rw [hCd d₁, hCd d₂]
    exact congrArg Subtype.val hq
  have hnu' : nu ∈ supportedRankLegalValueSpace (trueSecondForm F hF x)
      (mfderiv I 𝓘(ℝ, ℝ) psi x).toLinearMap := by
    rw [hpsix]
    exact hnu
  obtain ⟨v, hvx, hv, hlegal⟩ := upgrade_exists_local_free_normal_field F hF himm U x hxU
    psi A (hA.mono hUsub) hUinj (fun z hz ↦ hC z (hUsub hz)) nu hnu'
  obtain ⟨chi, hchi, hy, hglob, hcol⟩ := upgrade_exists_local_wave_cutoff F U hU x y hxU hxy
    psi (hpsi.mono hUsub) v hv
  refine ⟨U, psi, v, chi, hU, hxU, hUsub, hchi, hy, hpsi.mono hUsub, hpsix, hvx, hv,
    fun z hz ↦ ⟨hgood z hz, hlegal z hz⟩, hglob, ?_⟩
  simpa only [hpsix, hvx] using hcol

#print axioms upgrade_exists_local_legal_wave

end GlobalEmbedding.Paper
