import Upgrade.CompactBadSet
import GlobalEmbedding.Paper.UpgradeLocalTrueFormCoefficients
import GlobalEmbedding.Paper.SaturationEuclideanModel

/-!
# Closedness of the actual low-rank second-form locus

The rank in this file is the rank of the original `trueSecondForm F hF x`.
Moving source frames are included through the actual tangent trivialization.
Local operator coefficients are obtained from the accepted fixed-frame
smoothness theorem; no continuous second-form surrogate is assumed.
-/

noncomputable section

open Set Bundle Manifold Topology GlobalEmbedding.Paper
open scoped ContDiff

namespace GlobalEmbedding.Upgrade

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {N : ℕ}

/-- The actual true second form in a fixed tangent chart, using the original
canonical finite-dimensional coordinate basis only on its symmetric-square
source.  The normal value is included in the original Euclidean ambient. -/
def trueSecondFormChartOperator
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (center z : M) :
    (Fin (Module.finrank ℝ (SymmetricSquare E)) → ℝ) →L[ℝ]
      EuclideanSpace ℝ (Fin N) :=
  LinearMap.toContinuousLinearMap
    ((normalSpace (I := I) F z).subtype.comp ((trueSecondForm F hF z).comp
      ((symmetricSquareLinearMap
        ((trivializationAt E (TangentSpace I) center).symmL ℝ z).toLinearMap).comp
          (Module.finBasis ℝ (SymmetricSquare E)).equivFun.symm.toLinearMap)))

/-- The literal actual coefficient map is smooth and has exactly the rank of
`trueSecondForm` at every chart point.  The moving source frame is an equivalence
and ambient normal inclusion is injective. -/
theorem trueSecondFormChartOperator_properties
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (x : M) :
    ContMDiffOn I
      𝓘(ℝ, (Fin (Module.finrank ℝ (SymmetricSquare E)) → ℝ) →L[ℝ]
        EuclideanSpace ℝ (Fin N)) ∞ (trueSecondFormChartOperator F hF x)
      (chartAt H x).source ∧
    ∀ z ∈ (chartAt H x).source,
      Module.finrank ℝ (trueSecondFormChartOperator F hF x z).range =
        Module.finrank ℝ (trueSecondForm F hF z).range := by
  let D := Fin (Module.finrank ℝ (SymmetricSquare E)) → ℝ
  let b : D ≃ₗ[ℝ] SymmetricSquare E := (Module.finBasis ℝ (SymmetricSquare E)).equivFun.symm
  obtain ⟨A, hA, hcoeff⟩ := upgrade_exists_true_form_coefficients F hF himm x b.toLinearMap
  have heq : A = trueSecondFormChartOperator F hF x := by
    funext z
    apply ContinuousLinearMap.ext
    intro d
    exact hcoeff z d
  refine ⟨heq ▸ hA, ?_⟩
  intro z hz
  let e₀ := trivializationAt E (TangentSpace I) x
  have hz₀ : z ∈ e₀.baseSet := hz
  let e : E ≃ₗ[ℝ] TangentSpace I z := (e₀.linearEquivAt ℝ z hz₀).symm
  have he : e.toLinearMap = (e₀.symmL ℝ z).toLinearMap := by
    ext v
    exact (e₀.symmL_apply hz₀ v).symm
  let c : D ≃ₗ[ℝ] SymmetricSquare (TangentSpace I z) :=
    b.trans (saturationSymmetricSquareEquiv e)
  have hc : c.toLinearMap = (symmetricSquareLinearMap
      (e₀.symmL ℝ z).toLinearMap).comp b.toLinearMap := by
    change (saturationSymmetricSquareEquiv e).toLinearMap.comp b.toLinearMap = _
    rw [saturationSymmetricSquareEquiv_toLinearMap, he]
  have hlinear : (trueSecondFormChartOperator F hF x z).toLinearMap =
      (normalSpace (I := I) F z).subtype.comp
        ((trueSecondForm F hF z).comp c.toLinearMap) := by
    rw [hc]
    rfl
  change Module.finrank ℝ
    (LinearMap.range (trueSecondFormChartOperator F hF x z).toLinearMap) = _
  rw [hlinear, LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top _ c.range]
  exact Submodule.finrank_map_subtype_eq _ _

/-- Existential form of the literal actual chart coefficient construction. -/
theorem exists_trueSecondForm_rank_coefficients
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (x : M) :
    ∃ A : M → (Fin (Module.finrank ℝ (SymmetricSquare E)) → ℝ) →L[ℝ]
        EuclideanSpace ℝ (Fin N),
      ContMDiffOn I
        𝓘(ℝ, (Fin (Module.finrank ℝ (SymmetricSquare E)) → ℝ) →L[ℝ]
          EuclideanSpace ℝ (Fin N)) ∞ A (chartAt H x).source ∧
      ∀ z ∈ (chartAt H x).source,
        Module.finrank ℝ (A z).range = Module.finrank ℝ (trueSecondForm F hF z).range :=
  ⟨trueSecondFormChartOperator F hF x, trueSecondFormChartOperator_properties F hF himm x⟩

/-- Lower rank bounds for the genuine second form are open in the source.
This is local in the actual tangent frame and requires no normal trivialization
or orientation. -/
theorem isOpen_trueSecondForm_finrank_ge
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (r : ℕ) :
    IsOpen {x | r ≤ Module.finrank ℝ (trueSecondForm F hF x).range} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  change r ≤ Module.finrank ℝ (trueSecondForm F hF x).range at hx
  obtain ⟨A, hA, hrank⟩ := exists_trueSecondForm_rank_coefficients F hF himm x
  have hxchart : x ∈ (chartAt H x).source := mem_chart_source H x
  have hAx : ContinuousAt A x :=
    (hA.contMDiffAt ((chartAt H x).open_source.mem_nhds hxchart)).continuousAt
  have hrankOpen : IsOpen {B :
      (Fin (Module.finrank ℝ (SymmetricSquare E)) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin N) |
        r ≤ Module.finrank ℝ B.range} := by
    convert isOpen_setOfPred_nat_le_rank (𝕜 := ℝ)
      (E := Fin (Module.finrank ℝ (SymmetricSquare E)) → ℝ)
      (F := EuclideanSpace ℝ (Fin N)) r using 1
    ext B
    change r ≤ Module.finrank ℝ B.range ↔ (r : Cardinal) ≤ Module.rank ℝ B.range
    rw [← Module.finrank_eq_rank]
    norm_cast
  have hAxrank : r ≤ Module.finrank ℝ (A x).range := by
    rwa [hrank x hxchart]
  have hnear : ∀ᶠ z in 𝓝 x, r ≤ Module.finrank ℝ (A z).range :=
    hAx.eventually (hrankOpen.mem_nhds hAxrank)
  filter_upwards [hnear, (chartAt H x).open_source.mem_nhds hxchart] with z hz hzchart
  rwa [hrank z hzchart] at hz

/-- The actual low-rank locus is closed; under phase regularity at critical
dimension it is the rank-q locus used by the upgrade. -/
theorem isClosed_trueSecondForm_finrank_le
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (q : ℕ) :
    IsClosed {x | Module.finrank ℝ (trueSecondForm F hF x).range ≤ q} := by
  have heq : {x | Module.finrank ℝ (trueSecondForm F hF x).range ≤ q} =
      {x | q + 1 ≤ Module.finrank ℝ (trueSecondForm F hF x).range}ᶜ := by
    ext x
    simp only [mem_ofPred_eq, mem_compl_iff]
    omega
  rw [heq]
  exact (isOpen_trueSecondForm_finrank_ge F hF himm (q + 1)).isClosed_compl

/-- Compactness of the original low-rank coincidence incidence on the same
distant pair set.  In particular, source pairs in different components are
included automatically. -/
theorem isCompact_trueSecondForm_lowRank_coincidence
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (q : ℕ) {P : Set (M × M)} (hP : IsCompact P) :
    IsCompact {z ∈ P | Module.finrank ℝ (trueSecondForm F hF z.1).range ≤ q ∧
      F z.1 = F z.2} := by
  exact hP.inter_right
    (((isClosed_trueSecondForm_finrank_le F hF himm q).preimage continuous_fst).inter
      (isClosed_eq (hF.continuous.comp continuous_fst)
        (hF.continuous.comp continuous_snd)))

end GlobalEmbedding.Upgrade
