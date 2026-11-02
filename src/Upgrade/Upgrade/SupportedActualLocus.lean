import Upgrade.SupportedActualForm
import GlobalEmbedding.Paper.SupportedKernelClosedLocus
import GlobalEmbedding.Paper.LinearSecondFormOperatorOpen
import GlobalEmbedding.Paper.PhaseRegular

/-!
# Relative closedness of the actual supported bad set

The target is the original supported-kernel predicate of `trueSecondForm`.
Fixed normal coordinates are constructed locally from the current immersion;
the already accepted full supported-locus closedness is then pulled back.
There is no global normal frame and no replacement smooth second-form field.
In dimension three the second theorem keeps the literal joint incidence with
coincidence; it does not assert removal of all supported kernels.
-/

noncomputable section
open Bundle Filter Manifold Set Module
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {N : ℕ}

omit [FiniteDimensional ℝ E] in
/-- The original phase condition gives phase regularity of the very same
true second form, viewed only as a linear map on the native tangent model. -/
theorem trueSecondForm_linearPhaseRegular
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (hphase : PhaseRegular F hF) (x : M) :
    LinearSecondFormPhaseRegular
      (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := I) F x from trueSecondForm F hF x) := by
  obtain ⟨ξ, hξ⟩ := hphase x
  refine ⟨ξ.toLinearMap, ?_, hξ.2⟩
  intro hz
  apply hξ.1
  apply ContinuousLinearMap.ext
  intro v
  exact DFunLike.congr_fun hz v

/-- The original supported-kernel set is relatively closed in the actual
full-rank locus of a smooth phase-regular immersion. No dimension inequality
or orientability is needed for this geometric preparation. -/
theorem isClosed_actual_supported_in_fullRank
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (hphase : PhaseRegular F hF) :
    IsClosed {z : {z : M | Function.Surjective (trueSecondForm F hF z)} |
      HasSupportedKernel (trueSecondForm F hF z.val)} := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  change ¬ HasSupportedKernel (trueSecondForm F hF x.val) at hx
  obtain ⟨U, C, hU, hxU, _, hCs, hCx, _, hgeometry⟩ :=
    exists_actual_supported_coordinate_field F hF himm x.val
  let ambient : Set (SymmetricSquare E →L[ℝ] normalSpace (I := I) F x.val) :=
    {B | Function.Surjective B ∧ LinearSecondFormPhaseRegular B.toLinearMap}
  have hCxAmbient : C x.val ∈ ambient := by
    rw [hCx]
    exact ⟨x.property, trueSecondForm_linearPhaseRegular F hF hphase x.val⟩
  have hopen : IsOpen {B : ambient | ¬ HasSupportedKernel B.val.toLinearMap} :=
    isClosed_supportedKernel_surjective_phaseRegular.isOpen_compl
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp hopen
  have hCxO : C x.val ∈ O := by
    have hnot : (⟨C x.val, hCxAmbient⟩ : ambient) ∈
        {B : ambient | ¬ HasSupportedKernel B.val.toLinearMap} := by
      change ¬ HasSupportedKernel (C x.val).toLinearMap
      exact fun h ↦ hx ((hgeometry x.val hxU).1.mp h)
    rw [← hOeq] at hnot
    exact hnot
  have hambient : IsOpen ambient := isOpen_surjective_linearSecondFormPhaseRegular
  have hCcont : ContinuousAt C x.val :=
    (hCs.contMDiffAt (hU.mem_nhds hxU)).continuousAt
  have hnear : ∀ᶠ z : {z : M | Function.Surjective (trueSecondForm F hF z)} in 𝓝 x,
      C z.val ∈ O ∩ ambient :=
    (hCcont.comp continuous_subtype_val.continuousAt).eventually
      ((hO.inter hambient).mem_nhds ⟨hCxO, hCxAmbient⟩)
  have hnearU : ∀ᶠ z : {z : M | Function.Surjective (trueSecondForm F hF z)} in 𝓝 x,
      z.val ∈ U := continuous_subtype_val.continuousAt.eventually (hU.mem_nhds hxU)
  filter_upwards [hnear, hnearU] with z hz hzU
  change ¬ HasSupportedKernel (trueSecondForm F hF z.val)
  intro hs
  have hnot : ¬ HasSupportedKernel (C z.val).toLinearMap := by
    have hmem : (⟨C z.val, hz.2⟩ : ambient) ∈ Subtype.val ⁻¹' O := hz.1
    rw [hOeq] at hmem
    exact hmem
  exact hnot ((hgeometry z.val hzU).1.mpr hs)

/-- The exact supported-coincidence bad set is relatively closed on the
full-rank first-endpoint locus. Cross-component pairs are included; neither
connectedness nor a diagonal restriction is introduced here. -/
theorem isClosed_actual_supported_coincidence_in_fullRank
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (hphase : PhaseRegular F hF) :
    IsClosed {z : {x : M | Function.Surjective (trueSecondForm F hF x)} × M |
      HasSupportedKernel (trueSecondForm F hF z.1.val) ∧ F z.1.val = F z.2} := by
  have hs := (isClosed_actual_supported_in_fullRank F hF himm hphase).preimage
    (continuous_fst : Continuous (Prod.fst :
      {x : M | Function.Surjective (trueSecondForm F hF x)} × M → _))
  exact hs.inter (isClosed_eq
    (hF.continuous.comp (continuous_subtype_val.comp continuous_fst))
    (hF.continuous.comp continuous_snd))

#print axioms trueSecondForm_linearPhaseRegular
#print axioms isClosed_actual_supported_in_fullRank
#print axioms isClosed_actual_supported_coincidence_in_fullRank

end GlobalEmbedding.Upgrade
