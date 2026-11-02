import GlobalEmbedding.Paper.IncrementsModeAdaptedPhaseGram
import GlobalEmbedding.Paper.IncrementsJointSpatialJets

/-!
# ORIGINAL joint adapted-chart geometry: proposed actual-field ABI

Source: `main.tex`, lem:increments, lines 594–648, actual (6.2)/finite parameters.
DAG: `increments-joint-actual-geometry-regularity`. Exclusive worker W2.
STAGE2 ONLY, pending ROOT statement lock. The sole named sorry is expected.
No new geometry/section/norm/partial-derivative/mode-reconstruction definition.
-/

noncomputable section
open Manifold Set
open scoped ContDiff
namespace GlobalEmbedding.Paper

variable {m N : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ, D)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) M]

/-- ORIGINAL joint input geometry gives joint regularity of the SAME literal
spatial jets and coefficient fields. The actual parameter-dependent adapted chart
family is an explicit internal input still to be constructed upstream; arbitrary
extChartAt is not asserted adapted. No desired coefficient/Gram/margin is an input.

Proof plan, pending ROOT lock: compose the genuine joint F with the genuine joint
inverse-chart map, retaining the parameter. The sole local joint-to-slice bridge
identifies actual first/second spatial jets and proves their joint regularity.
Native maximal-chart derivative cancellation and ORIGINAL immersion give injection
and range equality of the spatial frame. Accepted Gram/projection smoothness gives
actual tangent reconstruction and normal projection. Accepted trueSecondForm_chart
for each actual maximal chart identifies the true-B rows with projected spatial
Hessians. Actual adaptation identifies the phase covector with transported first
coordinate; algebraic Good and the accepted sorted symmetric-product independence
give injection of the SAME transverse columns. Existing63ac Gram identity and
accepted Gram regularity give SAME included J; native finite row/CLM composition
gives T0 and real/complex A/B. This does not prove original adapted-chart existence,
uniform input-profile bounds, a validity threshold or any W5 R/Z/support theorem.
Source: the actual geometric coefficients in original (6.2), finite parameters. -/
theorem incrementsJointActualGeometry_contDiffOn
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (ψ : Ep → M → ℝ) (U : Set (Ep × M)) (O : Set (Ep × D)) (hO : IsOpen O)
    (hFjoint : ContMDiffOn ((𝓘(ℝ, Ep)).prod 𝓙) 𝓘(ℝ, V) ∞ (Function.uncurry F) U)
    (hψjoint : ContMDiffOn ((𝓘(ℝ, Ep)).prod 𝓙) 𝓘(ℝ, ℝ) ∞ (Function.uncurry ψ) U)
    (hcjoint : ContMDiffOn 𝓘(ℝ, Ep × D) 𝓙 ∞ (fun z ↦ (e z.1).symm z.2) O)
    (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hmap : MapsTo (fun z : Ep × D ↦ (z.1, (e z.1).symm z.2)) O U)
    (hU : IsOpen U)
    (hinj : ∀ z ∈ O, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ, V) (F z.1) ((e z.1).symm z.2)))
    (hadapt : ∀ z ∈ O, ψ z.1 ((e z.1).symm z.2) = z.2 0)
    (hgood : ∀ z ∈ O, GoodCovector (F z.1) (hF z.1) ((e z.1).symm z.2)
      ((tangentSpaceCastModel 𝓘(ℝ, ℝ) (ψ z.1 ((e z.1).symm z.2))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ, ℝ) (ψ z.1) ((e z.1).symm z.2)))) :
    ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2) O ∧
    ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2) O ∧
    ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2)) O ∧
    ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).starProjection) O ∧
    (∀ i j : Fin (m + 1), ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2 i j : V)) O) ∧
    ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2)) O ∧
    ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      incrementsModeTransverseValue (F z.1) (e z.1).symm z.2) O ∧
    ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      incrementsModeFirstOrderA (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2) O ∧
    ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      incrementsModeFirstOrderB (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2) O ∧
    ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      incrementsModeComplexFirstOrderA (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2) O ∧
    ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      incrementsModeComplexFirstOrderB (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2) O := by
  have hpc : ContMDiffOn 𝓘(ℝ, Ep × D) ((𝓘(ℝ, Ep)).prod 𝓙) ∞
      (fun z : Ep × D ↦ (z.1, (e z.1).symm z.2)) O :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk hcjoint
  have hFc : ContDiffOn ℝ ∞
      (fun z : Ep × D ↦ F z.1 ((e z.1).symm z.2)) O :=
    (hFjoint.comp hpc hmap).contDiffOn
  obtain ⟨hSlice, hFirst, hSecond⟩ := incrementsJointSpatialJets_bridge _ O hO hFc
  have he1 (p : Ep) : e p ∈ IsManifold.maximalAtlas 𝓙 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) (he p)
  have he2 (p : Ep) : e p ∈ IsManifold.maximalAtlas 𝓙 2 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) (he p)
  have hec (p : Ep) : (e p).MDifferentiable 𝓙 𝓙 := by
    constructor
    · intro q hq
      exact (mdifferentiableAt_of_mem_maximalAtlas (he1 p) hq).mdifferentiableWithinAt
    · intro q hq
      exact (mdifferentiableAt_symm_of_mem_maximalAtlas (he1 p) hq).mdifferentiableWithinAt
  have hpush (z : Ep × D) (hz : z ∈ O) :
      fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 =
        ((tangentSpaceCastModel 𝓘(ℝ, V) (F z.1 ((e z.1).symm z.2))).toContinuousLinearMap.comp
          (mfderiv 𝓙 𝓘(ℝ, V) (F z.1) ((e z.1).symm z.2))).comp
            (mfderiv 𝓙 𝓙 (e z.1).symm z.2) := by
    have hc := (hec z.1).mdifferentiableAt_symm (hcoord z hz)
    have h := mfderiv_comp z.2 ((hF z.1).mdifferentiable (by simp) _) hc
    rw [mfderiv_eq_fderiv] at h
    apply ContinuousLinearMap.ext
    intro v
    have hv := congrArg (fun L ↦
      tangentSpaceCastModel 𝓘(ℝ, V) (F z.1 ((e z.1).symm z.2))
        (L ((tangentSpaceCastModel 𝓙 z.2).symm v))) h
    exact hv
  have hAi (z : Ep × D) (hz : z ∈ O) :
      Function.Injective (fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2) := by
    rw [hpush z hz]
    exact (tangentSpaceCastModel 𝓘(ℝ, V) (F z.1 ((e z.1).symm z.2))).injective.comp
      ((hinj z hz).comp ((hec z.1).symm.mfderiv (hcoord z hz)).injective)
  have hnormal (z : Ep × D) (hz : z ∈ O) :
      normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2) =
        (LinearMap.range (fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2).toLinearMap)ᗮ := by
    rw [hpush z hz]
    unfold normalSpace
    congr 1
    let R := (tangentSpaceCastModel 𝓘(ℝ, V)
      (F z.1 ((e z.1).symm z.2))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ, V) (F z.1) ((e z.1).symm z.2))
    let C : D →L[ℝ] TangentSpace 𝓙 ((e z.1).symm z.2) :=
      mfderiv 𝓙 𝓙 (e z.1).symm z.2
    have hC : Function.Surjective C :=
      ((hec z.1).symm.mfderiv (hcoord z hz)).surjective
    have hr := LinearMap.range_comp C.toLinearMap R.toLinearMap
    rw [LinearMap.range_eq_top.mpr hC, Submodule.map_top] at hr
    exact hr.symm
  have hG : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2)) O :=
    (freeGramRightInverse_contMDiffOn (I := 𝓘(ℝ, Ep × D))
      _ hFirst.contMDiffOn hAi).contDiffOn
  have hN : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).starProjection) O := by
    exact (smooth_frame_normal_projection _ hFirst hAi).congr
      (fun z hz ↦ congrArg (fun W : Submodule ℝ V ↦ W.starProjection) (hnormal z hz))
  have hBformula (z : Ep × D) (hz : z ∈ O) (i j : Fin (m + 1)) :
      (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2 i j : V) =
      (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).starProjection
        (fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
    have hcv (k : Fin (m + 1)) :
        mfderiv 𝓙 𝓙 (e z.1) ((e z.1).symm z.2)
          (incrementsModeCoordinateDirections (I := 𝓙) (e z.1).symm z.2 k) =
            EuclideanSpace.single k 1 := by
      change mfderiv 𝓙 𝓙 (e z.1) ((e z.1).symm z.2)
        (mfderiv 𝓙 𝓙 (e z.1).symm z.2 (EuclideanSpace.single k 1)) = _
      exact congrArg (fun L ↦ L (EuclideanSpace.single k 1))
        ((hec z.1).comp_symm_deriv (hcoord z hz))
    dsimp only [incrementsModeSecondForm]
    rw [← trueSecondForm_chart (F z.1) (hF z.1) ((e z.1).symm z.2)
      (e z.1) (he2 z.1) ((e z.1).map_target (hcoord z hz))]
    change (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).starProjection
      (fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) ((e z.1) ((e z.1).symm z.2))
        (mfderiv 𝓙 𝓙 (e z.1) ((e z.1).symm z.2)
          (incrementsModeCoordinateDirections (I := 𝓙) (e z.1).symm z.2 i))
        (mfderiv 𝓙 𝓙 (e z.1) ((e z.1).symm z.2)
          (incrementsModeCoordinateDirections (I := 𝓙) (e z.1).symm z.2 j))) = _
    rw [hcv i, hcv j, (e z.1).right_inv (hcoord z hz)]
  have hB (i j : Fin (m + 1)) : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2 i j : V)) O :=
    (hN.clm_apply ((hSecond.clm_apply contDiffOn_const).clm_apply contDiffOn_const)).congr
      (fun z hz ↦ hBformula z hz i j)
  have hCi (z : Ep × D) (hz : z ∈ O) : Function.Injective
      (incrementsModeAmbientTransverseFrame (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2) := by
    classical
    let c : D → M := (e z.1).symm
    let L : D →L[ℝ] TangentSpace 𝓙 (c z.2) := mfderiv 𝓙 𝓙 c z.2
    let ξ : TangentSpace 𝓙 (c z.2) →L[ℝ] ℝ :=
      (tangentSpaceCastModel 𝓘(ℝ, ℝ) (ψ z.1 (c z.2))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ, ℝ) (ψ z.1) (c z.2))
    have hψp : MDifferentiableAt 𝓙 𝓘(ℝ, ℝ) (ψ z.1) (c z.2) := by
      have hp := (hψjoint.contMDiffAt (hU.mem_nhds (hmap hz))).comp
        (c z.2) (contMDiffAt_const.prodMk contMDiffAt_id)
      exact hp.mdifferentiableAt (by simp)
    have hphi : fderiv ℝ (ψ z.1 ∘ c) z.2 = EuclideanSpace.proj 0 := by
      have hO' : IsOpen {x : D | (z.1, x) ∈ O} :=
        hO.preimage (continuous_const.prodMk continuous_id)
      have heq : (fun x ↦ ψ z.1 (c x)) =ᶠ[nhds z.2] (fun x : D ↦ x 0) :=
        Filter.eventuallyEq_of_mem (hO'.mem_nhds hz) (fun x hx ↦ hadapt (z.1, x) hx)
      exact heq.fderiv_eq.trans
        (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (m + 1)) 0).fderiv
    have hξL : ξ.comp L = EuclideanSpace.proj 0 := by
      have hm := mfderiv_comp z.2 hψp ((hec z.1).mdifferentiableAt_symm (hcoord z hz))
      rw [mfderiv_eq_fderiv, hphi] at hm
      apply ContinuousLinearMap.ext
      intro v
      have hv := congrArg (fun A ↦ tangentSpaceCastModel 𝓘(ℝ, ℝ) (ψ z.1 (c z.2))
        (A ((tangentSpaceCastModel 𝓙 z.2).symm v))) hm
      exact hv.symm
    let D0 := EuclideanSpace ℝ (Fin m)
    let ins : D0 →ₗ[ℝ] D :=
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.toLinearMap.comp
        ((0 : D0 →ₗ[ℝ] ℝ).vecCons (EuclideanSpace.equiv (Fin m) ℝ).toLinearMap)
    let a : D0 →ₗ[ℝ] ξ.ker := (L.toLinearMap.comp ins).codRestrict ξ.ker (by
      intro v
      change ξ (L (ins v)) = 0
      change (ξ.comp L) (ins v) = 0
      rw [hξL]
      rfl)
    have hai : Function.Injective a := by
      intro u v huv
      have h : ins u = ins v := ((hec z.1).symm.mfderiv (hcoord z hz)).injective
        (congrArg Subtype.val huv)
      ext k
      exact congrArg (fun w : D ↦ w k.succ) h
    obtain ⟨p, hp⟩ := a.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hai)
    have hpa (v : D0) : p (a v) = v :=
      congrArg (fun A : D0 →ₗ[ℝ] D0 ↦ A v) hp
    let P := {q : Fin m × Fin m // q.1 ≤ q.2}
    have hli : LinearIndependent ℝ (fun q : P ↦
        symmetricSquareProduct ξ.ker (a (EuclideanSpace.single q.val.1 1))
          (a (EuclideanSpace.single q.val.2 1))) := by
      apply LinearIndependent.of_comp (symmetricSquareLinearMap p)
      change LinearIndependent ℝ (fun q : P ↦ symmetricSquareProduct D0
        (p (a (EuclideanSpace.single q.val.1 1))) (p (a (EuclideanSpace.single q.val.2 1))))
      simpa only [hpa] using increments_symmetric_coordinate_products_linearIndependent m
    have hg : Function.Injective ((trueSecondForm (F z.1) (hF z.1) (c z.2)).comp
        (symmetricSquareLinearMap ξ.ker.subtype)) := (hgood z hz).2
    have hb := hli.map' _ (LinearMap.ker_eq_bot.mpr hg)
    have ha_single (i : Fin m) : (a (EuclideanSpace.single i 1)).val =
        incrementsModeCoordinateDirections (I := 𝓙) c z.2 i.succ := by
      change L (ins (EuclideanSpace.single i 1)) = L (EuclideanSpace.single i.succ 1)
      congr 1
      ext k
      refine Fin.cases ?_ (fun j ↦ ?_) k
      · change (0 : ℝ) = _
        simp
      · change (EuclideanSpace.single i 1) j = _
        simp
    have hcols : LinearIndependent ℝ (fun q : P ↦
        incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) c z.2
          q.val.1.succ q.val.2.succ) := by
      convert hb using 1
      funext q
      symm
      change trueSecondForm (F z.1) (hF z.1) (c z.2)
        (symmetricSquareProduct (TangentSpace 𝓙 (c z.2))
          (a (EuclideanSpace.single q.val.1 1)).val
          (a (EuclideanSpace.single q.val.2 1)).val) = _
      rw [ha_single, ha_single]
      rfl
    intro u v huv
    have hs : (∑ q : P, (u q - v q) •
        incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) c z.2
          q.val.1.succ q.val.2.succ) = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero]
      have h := sub_eq_zero.mpr huv
      simpa [incrementsModeAmbientTransverseFrame, sub_smul, Finset.sum_sub_distrib] using h
    ext q
    exact sub_eq_zero.mp ((Fintype.linearIndependent_iff.mp hcols) _ hs q)
  let P := {q : Fin m × Fin m // q.1 ≤ q.2}
  have hC : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      incrementsModeAmbientTransverseFrame (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2) O := by
    apply contDiffOn_clm_apply.mpr
    intro t
    have hs : ContDiffOn ℝ ∞ (fun z : Ep × D ↦ ∑ q : P,
        t q • (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2
          q.val.1.succ q.val.2.succ : V)) O :=
      ContDiffOn.sum fun q _ ↦ (hB q.val.1.succ q.val.2.succ).const_smul (t q)
    simpa [incrementsModeAmbientTransverseFrame] using hs
  have hJ : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2)) O := by
    have hR := (freeGramRightInverse_contMDiffOn (I := 𝓘(ℝ, Ep × D))
      _ hC.contMDiffOn hCi).contDiffOn
    exact hR.congr (fun z _ ↦ incrementsModeCoordinateJ_ambient (I := 𝓙)
      (F z.1) (hF z.1) (e z.1).symm z.2)
  have hGamma (i j : Fin (m + 1)) : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      incrementsModeGamma (F z.1) (e z.1).symm z.2 i j) O := by
    have hK := (smooth_frame_gram_coefficients (I := 𝓘(ℝ, Ep × D))
      _ hFirst.contMDiffOn hAi).contDiffOn
    exact hK.clm_apply ((hSecond.clm_apply contDiffOn_const).clm_apply contDiffOn_const)
  have hT : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      incrementsModeTransverseValue (F z.1) (e z.1).symm z.2) O := by
    apply contDiffOn_clm_apply.mpr
    intro u
    have hr : ContDiffOn ℝ ∞ (fun z : Ep × D ↦ fun q : P ↦
        -inner ℝ (incrementsModeGamma (F z.1) (e z.1).symm z.2
          q.val.1.succ q.val.2.succ) u) O :=
      contDiffOn_pi.mpr fun q ↦
        ((hGamma q.val.1.succ q.val.2.succ).inner ℝ contDiffOn_const).neg
    exact (EuclideanSpace.equiv P ℝ).symm.contDiff.comp_contDiffOn hr
  have hA : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      incrementsModeFirstOrderA (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2) O := by
    apply contDiffOn_clm_apply.mpr
    intro jet
    let d : Fin (m + 1) → (D →L[ℝ] D) →L[ℝ] ℝ :=
      Fin.cases (incrementsModeJetComponent 0 0)
        (fun a ↦ incrementsModeJetComponent 0 a.succ + incrementsModeJetComponent a.succ 0)
    have hr : ContDiffOn ℝ ∞ (fun z : Ep × D ↦ fun i : Fin (m + 1) ↦
        d i jet - incrementsModeRowWeight i *
        inner ℝ (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1)
          (e z.1).symm z.2 0 i : V)
          (((normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).subtypeL.comp
            (incrementsModeCoordinateJ (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2))
              (incrementsModeTransverseJet jet))) O := by
      apply contDiffOn_pi.mpr
      intro i
      exact contDiffOn_const.sub (contDiffOn_const.mul
        ((hB 0 i).inner ℝ (hJ.clm_apply contDiffOn_const)))
    exact (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.contDiff.comp_contDiffOn hr
  have hB0 : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      incrementsModeFirstOrderB (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2) O := by
    apply contDiffOn_clm_apply.mpr
    intro u
    have hr : ContDiffOn ℝ ∞ (fun z : Ep × D ↦ fun i : Fin (m + 1) ↦
        -(incrementsModeRowWeight i *
          inner ℝ (incrementsModeGamma (F z.1) (e z.1).symm z.2 0 i) u) -
        incrementsModeRowWeight i *
          inner ℝ (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1)
            (e z.1).symm z.2 0 i : V)
            (((normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).subtypeL.comp
              (incrementsModeCoordinateJ (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2))
                (incrementsModeTransverseValue (F z.1) (e z.1).symm z.2 u))) O := by
      apply contDiffOn_pi.mpr
      intro i
      exact (contDiffOn_const.mul ((hGamma 0 i).inner ℝ contDiffOn_const)).neg.sub
        (contDiffOn_const.mul ((hB 0 i).inner ℝ (hJ.clm_apply (hT.clm_apply contDiffOn_const))))
    exact (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.contDiff.comp_contDiffOn hr
  refine ⟨hFirst, hSecond, hG, hN, hB, hJ, hT, hA, hB0, ?_, ?_⟩
  · exact (((contDiffOn_const.clm_comp hA).clm_comp contDiffOn_const).add
      (((contDiffOn_const.clm_comp hA).clm_comp contDiffOn_const).const_smul Complex.I))
  · exact ((contDiffOn_const.clm_comp (hB0.clm_comp contDiffOn_const)).add
      ((contDiffOn_const.clm_comp (hB0.clm_comp contDiffOn_const)).const_smul Complex.I))

end GlobalEmbedding.Paper
