import Upgrade.CompactOriginalC2Geometry
import Upgrade.CompactBadSet
import Upgrade.CompactTrueRank

/-!
# Actual rank exclusion from the original C² norm

The fixed projected Hessian is identified with the same actual second form
and therefore has exactly its rank. Compactness then gives original-norm
tolerances which exclude new low-rank points and joint coincidences outside
any already chosen open cover. No coefficient-gap or incidence-rank input is
left in these protection theorems.
-/

noncomputable section
open Set Bundle Manifold Module GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Upgrade

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The actual fixed projected Hessian has exactly the rank of the original
true second form. Both the real source-coordinate isomorphism and normal
inclusion are accounted for; no matrix-rank hypothesis is supplied. -/
theorem probeAtlasProjectedSecondForm_finrank
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source) :
    finrank ℝ (probeAtlasProjectedSecondForm A F i x).range =
      finrank ℝ (trueSecondForm F hF x).range := by
  let e := probeAtlasInverseFrameEquiv A hA i x hx
  let s := saturationSymmetricSquareEquiv e.toLinearEquiv
  let B : SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x := trueSecondForm F hF x
  have hs : s.toLinearMap = symmetricSquareLinearMap (probeAtlasFrame A i x).toLinearMap := by
    rw [saturationSymmetricSquareEquiv_toLinearMap]
    exact congrArg symmetricSquareLinearMap
      (congrArg ContinuousLinearMap.toLinearMap
        (probeAtlasInverseFrameEquiv_toContinuousLinearMap A hA i x hx))
  have hlinear : (probeAtlasProjectedSecondForm A F i x).toLinearMap =
      (normalSpace (I := IM) F x).subtype.comp
        (B.comp s.toLinearMap) := by
    rw [hs, probeAtlasProjectedSecondForm_eq_trueSecondForm A hA F hF i x hx]
    rfl
  change finrank ℝ (LinearMap.range (probeAtlasProjectedSecondForm A F i x).toLinearMap) = _
  have hr : (B.comp s.toLinearMap).range = B.range :=
    LinearMap.range_comp_of_range_eq_top B s.range
  rw [hlinear, LinearMap.range_comp, hr]
  exact Submodule.finrank_map_subtype_eq _ _

/-- A compact region of actual rank above `q` stays so for every smooth map
inside one original C² ball. The tolerance is obtained from actual compact
fixed-atlas data, rather than requiring an independent coefficient estimate. -/
theorem exists_originalC2_rank_reserve [T2Space M]
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i) (hdim : 2 ≤ n)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) (q : ℕ) {C : Set M} (hC : IsCompact C)
    (hhigh : ∀ x ∈ C, q < finrank ℝ (trueSecondForm F hF x).range) :
    ∃ e > 0, ∀ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G),
      probeAtlasCj A 2 (G - F) ≤ ENNReal.ofReal e →
        ∀ x ∈ C, q < finrank ℝ (trueSecondForm G hG x).range := by
  let J := Σ i : Fin A.count, ↥(C ∩ A.support i)
  let : ∀ i, CompactSpace ↥(C ∩ A.support i) := fun i ↦
    isCompact_iff_compactSpace.mp (hC.inter (hcompact i))
  let S : J → SymmetricSquare E →L[ℝ] V := fun z ↦
    probeAtlasProjectedSecondForm A F z.1 z.2
  have hS : Continuous S := continuous_sigma_iff.mpr fun i ↦
    ((continuousOn_probeAtlasProjectedSecondForm A hA F hF himm i).mono
      (fun _ hx ↦ hA.support_subset i hx.2)).domRestrict
  obtain ⟨d, hd, hstable⟩ := compact_no_new_incidence
    (isCompact_univ : IsCompact (univ : Set J)) isOpen_empty
    (show IsClosed {B : SymmetricSquare E →L[ℝ] V | finrank ℝ B.range ≤ q} from
      isClosed_operator_finrank_le q) hS.continuousOn
    (fun z _ hlow ↦ by
      have heq := probeAtlasProjectedSecondForm_finrank A hA F hF z.1 z.2
        (hA.support_subset z.1 z.2.property.2)
      have hh := hhigh z.2 z.2.property.1
      change finrank ℝ (S z).range ≤ q at hlow
      change finrank ℝ (S z).range = _ at heq
      rw [heq] at hlow
      exact False.elim (Nat.not_le_of_gt hh hlow))
  obtain ⟨e, he, herr⟩ := exists_originalC2_normal_and_form_budget
    A hA hcompact hcover hdim F hF himm hphase hd
  refine ⟨e, he, ?_⟩
  intro G hG hbudget x hx
  obtain ⟨i, hxi⟩ := hcover x
  by_contra hbad
  have hlow : finrank ℝ (probeAtlasProjectedSecondForm A G i x).range ≤ q := by
    rw [probeAtlasProjectedSecondForm_finrank A hA G hG i x (hA.support_subset i hxi)]
    exact Nat.le_of_not_gt hbad
  apply hstable (fun z : J ↦ probeAtlasProjectedSecondForm A G z.1 z.2) ?_
    ⟨i, x, hx, hxi⟩ (mem_univ _) hlow
  intro z _
  exact (show dist (probeAtlasProjectedSecondForm A G z.1 z.2) (S z) < d by
    rw [dist_eq_norm]
    exact (herr G hG hbudget).2 z.1 z.2 z.2.property.2)

end GlobalEmbedding.Upgrade
