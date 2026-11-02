import GlobalEmbedding.Paper.SupportedRankOriginalLiftedData
import GlobalEmbedding.Paper.SupportedRankHyperplaneCoordinates
import GlobalEmbedding.Paper.SupportedRankMixedSpanTransport
import GlobalEmbedding.Paper.SupportedRankActualLegalColumn
import GlobalEmbedding.Paper.SupportedRankPositiveCompression
import GlobalEmbedding.Paper.SupportedRankNormalQuotient
import GlobalEmbedding.Paper.SymmetricSquareMixedOrthogonality

/-!
# The actual original legal kernel variations have the full compressed span

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
lines 1014–1029. All good covectors, legal vectors, actual kernel derivatives and
span dimensions are constructed from the SAME original supported operator B.
-/

noncomputable section
open scoped TensorProduct

namespace GlobalEmbedding.Paper

private theorem normalCountImageFinrank {H F : Type*} [AddCommGroup H] [Module ℝ H]
    [AddCommGroup F] [Module ℝ F] (L : Submodule ℝ H) (M : H →ₗ[ℝ] F) :
    Module.finrank ℝ (L.map M) = Module.finrank ℝ (L.map M.ker.mkQ) := by
  have hmap : ((L.map M.ker.mkQ).map M.quotKerEquivRange.toLinearMap).map
      M.range.subtype = L.map M := by
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    congr 1
  rw [← hmap, Submodule.finrank_map_subtype_eq, M.quotKerEquivRange.finrank_map_eq]

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance normalCountSquareClosed {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] :
    IsClosed (symmetricSquareRelations V : Set (V ⊗[ℝ] V)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance normalCountSquareNormed {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] :
    NormedAddCommGroup (SymmetricSquare V) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations V)

private noncomputable local instance normalCountSquareInner {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] :
    InnerProductSpace ℝ (SymmetricSquare V) :=
  { Submodule.instQuotientInnerProductSpace (symmetricSquareRelations V) with
    toNormedSpace := squareNS V }

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- The literal mixed subspace, regarded as a subspace of the actual kernel complement.
Source: `prop:supported-rank`, the original `Z=e⊙V⊂K⊥`. -/
def supportedRankActualMixedSpace (B : SymmetricSquare V →L[ℝ] W) (e : V) :
    Submodule ℝ B.kerᗮ :=
  (symmetricSquareProduct V e).range.comap B.kerᗮ.subtype

/-- Project the actual kernel-graph derivative to the literal original mixed space.
Source: `prop:supported-rank`, the positive compression of equation (9.4). -/
def supportedRankProjectedKernelVariation (B : SymmetricSquare V →L[ℝ] W)
    (hB : Function.Surjective B) (e : V) :
    (SymmetricSquare V →L[ℝ] W) →L[ℝ]
      B.ker →L[ℝ] supportedRankActualMixedSpace B e :=
  (ContinuousLinearMap.compL ℝ B.ker B.kerᗮ (supportedRankActualMixedSpace B e)
    (supportedRankActualMixedSpace B e).orthogonalProjectionOnto).comp
      (fderiv ℝ (supportedRankKernelGraph B hB) B)

/-- The span consists only of actual good/legal original columns, after the true derivative.
Source: `prop:supported-rank`, the actual legal kernel-variation span. -/
def supportedRankProjectedLegalSpan (B : SymmetricSquare V →L[ℝ] W)
    (hB : Function.Surjective B) (e : V) :
    Submodule ℝ (B.ker →ₗ[ℝ] supportedRankActualMixedSpace B e) :=
  Submodule.span ℝ {f | ∃ ξ : V →ₗ[ℝ] ℝ,
    LinearSecondFormGoodCovector B.toLinearMap ξ ∧
      ∃ ν : W, ν ∈ supportedRankLegalValueSpace B.toLinearMap ξ ∧
        f = (supportedRankProjectedKernelVariation B hB e
          (supportedRankLegalVariation ξ ν).toContinuousLinearMap).toLinearMap}

/-- Original onto/phase/dimension/support data yield at least `q+(n-1)` actual projected
legal directions, with the literal original inverse-Gram compression.

Proof: construct the SAME actual open good family and its `q+d` lifted span. The
native original-hyperplane coordinates identify its columns with the actual mixed
range. The supported-kernel pairing puts that range inside the actual K-perpendicular.
Postcompose with the negative actual inverse-Gram compression, which is a genuine
equivalence by the proved positive-compression theorem. Every resulting generator
is the actual derivative of the explicitly constructed original legal vector. Thus
the transformed full-dimensional span is contained in the actual legal span.
No desired good/span/compression/rank conclusion is supplied as a hypothesis.
Source: `prop:supported-rank`, equation (9.4) and the strong prequotient rank bound. -/
theorem supportedRank_projected_legal_span_finrank
    (B : SymmetricSquare V →L[ℝ] W) (hB : Function.Surjective B)
    (hphase : LinearSecondFormPhaseRegular B.toLinearMap) (hn : 3 ≤ Module.finrank ℝ V)
    (hW : Module.finrank ℝ W =
      Module.finrank ℝ V * (Module.finrank ℝ V - 1) / 2 + 1)
    (U : Submodule ℝ V) (hU : Module.finrank ℝ U + 1 = Module.finrank ℝ V)
    (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (e : V) (he : e ∈ Uᗮ) (he0 : e ≠ 0) :
    Module.finrank ℝ V * (Module.finrank ℝ V - 1) / 2 + (Module.finrank ℝ V - 1) ≤
      Module.finrank ℝ (supportedRankProjectedLegalSpan B hB e) := by
  obtain ⟨_, Ω, _, _, _, _, hgood, hspan⟩ :=
    supportedRank_original_lifted_data B.toLinearMap hB hphase hn hW U hU hK
  let Q := supportedRankKernelQuadratic B.toLinearMap U
  let a := supportedRankQuadraticEvaluation Q
  let d := supportedRankHyperplaneCoordinates U hU e he he0
  have hm : (symmetricSquareProduct V e).range ≤ B.kerᗮ :=
    symmetricSquare_mixed_range_le_orthogonal U B.ker hK e he
  let Z := supportedRankActualMixedSpace B e
  have hde : supportedRankSplitVector d = e :=
    supportedRankHyperplaneCoordinates_vector U hU e he he0
  let em := (supportedRankMixedRangeEquiv d).trans
    (LinearEquiv.ofEq _ (symmetricSquareProduct V e).range (by rw [hde]))
  let ez : (U × ℝ) ≃ₗ[ℝ] Z :=
    em.trans (Submodule.comapSubtypeEquivOfLe hm).symm
  let A := supportedRankKernelComplementMap B
  obtain ⟨c, hc⟩ := (supportedRank_inverseGram_compression_invertible Z A
    (supportedRankKernelComplementMap_bijective B hB).1).2
  let negc : Z ≃ₗ[ℝ] Z := c.toLinearEquiv.trans (LinearEquiv.neg ℝ)
  let E : (B.ker →ₗ[ℝ] U × ℝ) ≃ₗ[ℝ] B.ker →ₗ[ℝ] Z :=
    (LinearEquiv.refl ℝ B.ker).arrowCongr (ez.trans negc)
  let L := supportedRankLiftedSpan a Ω
  have hsubset : L.map E.toLinearMap ≤ supportedRankProjectedLegalSpan B hB e := by
    change (Submodule.span ℝ (Set.range fun p : Ω × ℝ ↦
      supportedRankLiftedColumn a p.1 p.2)).map E.toLinearMap ≤ _
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨f, ⟨p, rfl⟩, rfl⟩
    let v : V := (p.1 : U) + p.2 • e
    have hv : symmetricSquareProduct V e v ∈ B.kerᗮ := hm ⟨v, rfl⟩
    let ν := supportedRankActualLegalVector B hB e v hv
    apply Submodule.subset_span
    refine ⟨innerₗ V v, hgood p.1 p.1.property e he p.2, ν,
      supportedRankActualLegalVector_mem B hB e v hv, ?_⟩
    apply LinearMap.ext
    intro k
    have hsquare : supportedRankCovectorSquare (innerₗ V v) k = a p.1 k := by
      rw [supportedRankCovectorSquare_add_orthogonal U k (hK k.property) e he]
      rw [supportedRankCovectorSquare_inner_eq_operator]
      rfl
    have hd := supportedRankActualLegalVector_kernel_derivative B hB e v hv k
    have hcv (z : Z) : c z = supportedRankPositiveCompression Z (A.adjoint.comp A).inverse z :=
      congrArg (fun C : Z →L[ℝ] Z ↦ C z) hc
    have hzval : (ez ((p.1 : U), p.2) : B.kerᗮ) =
        ⟨symmetricSquareProduct V e v, hv⟩ := by
      apply Subtype.ext
      change symmetricSquareProduct V (supportedRankSplitVector d) (d ((p.1 : U), p.2)) =
        symmetricSquareProduct V e v
      rw [hde]
      rfl
    change -(c (ez (supportedRankLiftedColumn a p.1 p.2 k))) =
      Z.orthogonalProjectionOnto
        ((fderiv ℝ (supportedRankKernelGraph B hB) B)
          (supportedRankLegalVariation (innerₗ V v) ν).toContinuousLinearMap k)
    rw [hd, hsquare]
    change -(c (ez ((a p.1 k) • ((p.1 : U), p.2)))) = _
    rw [map_smul, map_smul, hcv, map_neg, map_smul]
    change -((a p.1 k) • Z.orthogonalProjectionOnto
        ((A.adjoint.comp A).inverse (ez ((p.1 : U), p.2) : B.kerᗮ))) =
      -((a p.1 k) • Z.orthogonalProjectionOnto
        ((A.adjoint.comp A).inverse ⟨symmetricSquareProduct V e v, hv⟩))
    rw [hzval]
  have hdim := E.finrank_map_eq L
  exact hspan.trans (hdim.symm.le.trans (Submodule.finrank_mono hsubset))

/-- Transfer the actual strong compressed legal span to the SAME local equation.

Proof: the preceding theorem supplies `q+d` from ONLY original B-data. Apply the
accepted normal-quotient estimate to the actual kernel of the specified same-chart
normal differential. Native first-isomorphism and submodule-image equivalences
identify that quotient image with its actual normal image. The stated actual
factorization identifies every generator with the original local-equation
derivative, so inclusion in the literal target span completes the dimension bound.
The factorization and kernel estimate are genuine intermediate geometry outputs,
to be discharged by the sole local-chart provider in the full original theorem.
Source: `prop:supported-rank`, SAME-chart normal rank after support-motion loss. -/
theorem supportedRank_actual_equation_legal_span_finrank
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (B : SymmetricSquare V →L[ℝ] W) (hB : Function.Surjective B)
    (hphase : LinearSecondFormPhaseRegular B.toLinearMap) (hn : 3 ≤ Module.finrank ℝ V)
    (hW : Module.finrank ℝ W =
      Module.finrank ℝ V * (Module.finrank ℝ V - 1) / 2 + 1)
    (U : Submodule ℝ V) (hU : Module.finrank ℝ U + 1 = Module.finrank ℝ V)
    (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (e : V) (he : e ∈ Uᗮ) (he0 : e ≠ 0)
    (f : (SymmetricSquare V →L[ℝ] W) → F)
    (M : (B.ker →ₗ[ℝ] supportedRankActualMixedSpace B e) →ₗ[ℝ] F)
    (hfactor : ∀ Δ, (fderiv ℝ f B) Δ =
      M (supportedRankProjectedKernelVariation B hB e Δ).toLinearMap)
    (hker : Module.finrank ℝ M.ker ≤ Module.finrank ℝ V - 1) :
    Module.finrank ℝ V * (Module.finrank ℝ V - 1) / 2 ≤
      Module.finrank ℝ (Submodule.span ℝ
        {v : F | ∃ ξ : V →ₗ[ℝ] ℝ, LinearSecondFormGoodCovector B.toLinearMap ξ ∧
          ∃ ν : W, ν ∈ supportedRankLegalValueSpace B.toLinearMap ξ ∧
            v = (fderiv ℝ f B) (supportedRankLegalVariation ξ ν).toContinuousLinearMap}) := by
  let L := supportedRankProjectedLegalSpan B hB e
  have hL := supportedRank_projected_legal_span_finrank B hB hphase hn hW U hU hK e he he0
  have hq := supportedRank_normal_quotient_bound L M.ker
    (Module.finrank ℝ V * (Module.finrank ℝ V - 1) / 2)
    (Module.finrank ℝ V - 1) hL hker
  have hdim := @normalCountImageFinrank
    (B.ker →ₗ[ℝ] supportedRankActualMixedSpace B e) F _ _ _ _ L M
  have hsubset : L.map M ≤ Submodule.span ℝ
      {v : F | ∃ ξ : V →ₗ[ℝ] ℝ, LinearSecondFormGoodCovector B.toLinearMap ξ ∧
        ∃ ν : W, ν ∈ supportedRankLegalValueSpace B.toLinearMap ξ ∧
          v = (fderiv ℝ f B) (supportedRankLegalVariation ξ ν).toContinuousLinearMap} := by
    dsimp only [L, supportedRankProjectedLegalSpan]
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨y, ⟨ξ, hg, ν, hν, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨ξ, hg, ν, hν, (hfactor _).symm⟩
  exact hq.trans (hdim.symm.le.trans (Submodule.finrank_mono hsubset))

#print axioms supportedRankActualMixedSpace
#print axioms supportedRankProjectedKernelVariation
#print axioms supportedRankProjectedLegalSpan
#print axioms supportedRank_projected_legal_span_finrank
#print axioms supportedRank_actual_equation_legal_span_finrank
#print axioms normalCountImageFinrank
#print axioms normalCountSquareClosed
#print axioms normalCountSquareNormed
#print axioms normalCountSquareInner

end GlobalEmbedding.Paper
