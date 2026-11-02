import NormalPolar.OriginalWaveSeedRefinement
import Mathlib.Topology.Homeomorph.Lemmas

/-! Actual finite adapted charts and an ordinary partition for a compact
signed-phase carrier. The auxiliary indicator is used only to specify that
carrier to the finite-cover theorem; no derivative of it is taken. The
produced cutoffs are genuine smooth functions. No one-chart carrier premise,
raw coefficient bound, secondary wave or final estimate is an input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "IM" => 𝓘(ℝ,D)
local notation "IZM" => (ModelWithCorners.prod 𝓘(ℝ,Z) IM)

private theorem jointSeedSection {X : Type*} [TopologicalSpace X] (x : X) :
    (Homeomorph.uniqueProd Z X).symm x = (default,x) := by
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · simpa only [Homeomorph.coe_uniqueProd] using (Homeomorph.uniqueProd Z X).apply_symm_apply x

def jointSecondarySeedSpatialChart (a : OpenPartialHomeomorph (Z × M) (Z × D)) :
    OpenPartialHomeomorph M D :=
  (Homeomorph.uniqueProd Z M).symm.toOpenPartialHomeomorph.trans
    (a.trans (Homeomorph.uniqueProd Z D).toOpenPartialHomeomorph)

theorem jointSecondarySeedSpatialChart_apply (a : OpenPartialHomeomorph (Z × M) (Z × D)) (x : M) :
    jointSecondarySeedSpatialChart a x = (a (default,x)).2 := by
  simp only [jointSecondarySeedSpatialChart,OpenPartialHomeomorph.trans_apply,
    Homeomorph.toOpenPartialHomeomorph_apply,jointSeedSection,Homeomorph.coe_uniqueProd]

theorem jointSecondarySeedSpatialChart_inverse (a : OpenPartialHomeomorph (Z × M) (Z × D)) (y : D) :
    (jointSecondarySeedSpatialChart a).symm y = (a.symm (default,y)).2 := by
  simp only [jointSecondarySeedSpatialChart,OpenPartialHomeomorph.coe_trans_symm,Function.comp_apply,
    Homeomorph.toOpenPartialHomeomorph_symm_apply,Homeomorph.symm_symm,jointSeedSection,Homeomorph.coe_uniqueProd]

theorem jointSecondarySeedSpatialChart_source (a : OpenPartialHomeomorph (Z × M) (Z × D)) (x : M) :
    x ∈ (jointSecondarySeedSpatialChart a).source ↔ (default,x) ∈ a.source := by
  simp [jointSecondarySeedSpatialChart,OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source,Homeomorph.toOpenPartialHomeomorph_apply,jointSeedSection]

theorem jointSecondarySeedSpatialChart_target (a : OpenPartialHomeomorph (Z × M) (Z × D)) (y : D) :
    y ∈ (jointSecondarySeedSpatialChart a).target ↔ (default,y) ∈ a.target := by
  simp [jointSecondarySeedSpatialChart,OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target,Homeomorph.toOpenPartialHomeomorph_symm_apply,jointSeedSection]

theorem jointSecondarySeedSpatialChart_maximal (a : OpenPartialHomeomorph (Z × M) (Z × D))
    (ha : ContMDiffOn IZM 𝓘(ℝ,Z × D) ∞ a a.source)
    (hi : ContMDiffOn 𝓘(ℝ,Z × D) IZM ∞ a.symm a.target) :
    jointSecondarySeedSpatialChart a ∈ maximalAtlas IM ∞ M := by
  apply (mem_maximalAtlas_iff_contMDiffOn _).mpr
  constructor
  · have heq : (jointSecondarySeedSpatialChart a : M → D) = fun x => (a (default,x)).2 :=
      funext (jointSecondarySeedSpatialChart_apply a)
    rw [heq]
    have hs : ContMDiff IM IZM ∞ (fun x : M => ((default : Z),x)) := contMDiff_const.prodMk contMDiff_id
    exact (ContinuousLinearMap.snd ℝ Z D).contMDiff.comp_contMDiffOn
      (ha.comp hs.contMDiffOn (fun x hx => (jointSecondarySeedSpatialChart_source a x).mp hx))
  · have heq : ((jointSecondarySeedSpatialChart a).symm : D → M) = fun y => (a.symm (default,y)).2 :=
      funext (jointSecondarySeedSpatialChart_inverse a)
    rw [heq]
    have hs : ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,Z × D) ∞ (fun y : D => ((default : Z),y)) :=
      (contDiff_const.prodMk contDiff_id).contMDiff
    exact contMDiff_snd.comp_contMDiffOn
      (hi.comp hs.contMDiffOn (fun y hy => (jointSecondarySeedSpatialChart_target a y).mp hy))

structure JointSecondarySignedRefinement (phase : M → ℝ) (K O : Set M) where
  count : ℕ
  chart : Fin count → OpenPartialHomeomorph M D
  cutoff : Fin count → M → ℝ
  source_domain : ∀ i, (chart i).source ⊆ O
  maximal : ∀ i, chart i ∈ maximalAtlas IM ∞ M
  adaptation : ∀ i x, x ∈ (chart i).source → phase x = chart i x 0
  inverse_phase : ∀ i y, y ∈ (chart i).target → phase ((chart i).symm y) = y 0
  cutoff_smooth : ∀ i, ContMDiff IM 𝓘(ℝ,ℝ) ∞ (cutoff i)
  cutoff_nonneg : ∀ i x, 0 ≤ cutoff i x
  cutoff_support : ∀ i, tsupport (cutoff i) ⊆ (chart i).source
  partition : ∀ x ∈ K, ∑ i, cutoff i x = 1

/-- The actual carrier may be any closed subset of the original compact
manifold, including an intersection of two original primary carriers. -/
theorem jointSecondary_exists_signed_refinement
    (phase : M → ℝ) (K O : Set M) (hK : IsClosed K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hphase : ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ phase O)
    (hcritical : ∀ x ∈ K, mfderiv IM 𝓘(ℝ,ℝ) phase x ≠ 0) :
    Nonempty (JointSecondarySignedRefinement (m := m) phase K O) := by
  let W : Set (Z × M) := univ ×ˢ univ
  let C : Set (Z × M) := univ ×ˢ K
  let chi : Z × M → ℝ := C.indicator (fun _ => 1)
  let psi : Z × M → ℝ := fun z => phase z.2
  let U : Set (Z × M) := univ ×ˢ O
  let A : Set (Z × M) := Subtype.val '' tsupport (fun z : W => chi z.val)
  have hts : tsupport (fun z : W => chi z.val) = Subtype.val ⁻¹' C := by
    have hs : Function.support (fun z : W => chi z.val) = Subtype.val ⁻¹' C := by
      ext z
      by_cases hz : z.val ∈ C <;> simp [chi,Function.mem_support,hz]
    rw [tsupport,hs]
    exact ((isClosed_univ.prod hK).preimage continuous_subtype_val).closure_eq
  have hparent : A ⊆ U := by
    rintro z ⟨y,hy,rfl⟩
    have hC : y.val ∈ C := by rwa [hts] at hy
    exact ⟨mem_univ _,hKO hC.2⟩
  have hactive (z : Z × M) (hz : z.2 ∈ K) : z ∈ A := by
    refine ⟨⟨z,by simp [W]⟩,?_,rfl⟩
    rw [hts]
    exact ⟨mem_univ _,hz⟩
  have hpsi : ContMDiffOn IZM 𝓘(ℝ,ℝ) ∞ psi (W ∩ U) :=
    hphase.comp contMDiff_snd.contMDiffOn (fun z hz => hz.2.2)
  have hnc : ∀ z ∈ A ∩ (univ ×ˢ (univ : Set M)),
      mfderiv IM 𝓘(ℝ,ℝ) (fun x : M => psi (z.1,x)) z.2 ≠ 0 := by
    rintro z ⟨⟨y,hy,rfl⟩,_⟩
    rw [hts] at hy
    exact hcritical y.val.2 hy.2
  obtain ⟨r,a,L,rho,Lambda,hL,hLc,hAL,hLa,hactiveChart,hcharts,hsub,hsum,
      hLambda,hKL,hLambdaSub,hcover,hretain,hrecover⟩ :=
    increments_exists_finite_adapted_cover_partition_of_mfderiv_ne_zero
      (F := ℝ) (univ : Set Z) isOpen_univ (univ : Set Z) isCompact_univ Subset.rfl
      chi psi U (isOpen_univ.prod hO) hparent hpsi hnc
  refine ⟨{
    count := r
    chart := fun i => jointSecondarySeedSpatialChart (a i)
    cutoff := fun i x => rho i (default,x)
    source_domain := ?_
    maximal := fun i => jointSecondarySeedSpatialChart_maximal (a i) (hcharts i).2.1 (hcharts i).2.2.1
    adaptation := ?_
    inverse_phase := ?_
    cutoff_smooth := ?_
    cutoff_nonneg := fun i x => rho.nonneg i (default,x)
    cutoff_support := ?_
    partition := ?_ }⟩
  · intro i x hx
    exact ((hcharts i).1 ((jointSecondarySeedSpatialChart_source (a i) x).mp hx)).2.2
  · intro i x hx
    rw [jointSecondarySeedSpatialChart_apply]
    exact ((hcharts i).2.2.2.1 (default,x) ((jointSecondarySeedSpatialChart_source (a i) x).mp hx)).2.symm
  · intro i y hy
    rw [jointSecondarySeedSpatialChart_inverse]
    exact ((hcharts i).2.2.2.2 (default,y) ((jointSecondarySeedSpatialChart_target (a i) y).mp hy)).2
  · intro i
    exact (rho i).contMDiff.comp (contMDiff_const.prodMk contMDiff_id)
  · intro i x hx
    apply (jointSecondarySeedSpatialChart_source (a i) x).mpr
    exact hsub i (tsupport_comp_subset_preimage (rho i)
      (continuous_const.prodMk continuous_id) hx)
  · intro x hx
    exact hsum (default,x) (hcover ⟨hactive (default,x) hx,hKL (mem_univ _),mem_univ _⟩)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_exists_signed_refinement
