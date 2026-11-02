import GlobalEmbedding.Offline.CoincidenceAvoidanceEmbedding
import GlobalEmbedding.Paper.NormalProjectionTangent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Tangent and actual parameter-normal rank of the coincidence derivative

Source: `thm:upgrade`, final value-coincidence step, and original node
`upgrade-remove-value-coincidences`.

The goal of this file is the actual joint differential of the SAME map
`euclideanCoincidenceMap G`, not a supplied matrix or an abstract substitute
for the coincidence equation. The actual normal rank of the parameter
difference remains the upstream paired-probe construction's obligation.

This is an isolated offline candidate, not a main-library acceptance receipt.
-/

noncomputable section

open Function Filter Manifold Set GlobalEmbedding.Paper
open scoped Topology ContDiff

namespace GlobalEmbedding.Offline

section RankNullity

variable {A B C V W : Type*}
  [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]
  [AddCommGroup C] [Module ℝ C] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ V]

/-- A projection that kills an injective tangent image detects independent
additional directions inside the SAME joint image. This is the rank-nullity
calculation used below on the actual coincidence differential.

Proof: restrict the projection to the joint image. Its kernel contains an
injective copy of the tangent domain; its range contains the projected
parameter image. Add these two lower bounds using native rank-nullity.
Source: the `n` tangent plus `n+1` normal directions in `thm:upgrade`. -/
theorem finrank_joint_range_ge_tangent_add_projected_parameter
    (J : C →ₗ[ℝ] V) (T : A →ₗ[ℝ] V) (P : B →ₗ[ℝ] V) (Q : V →ₗ[ℝ] W)
    (hT : Injective T) (hTJ : LinearMap.range T ≤ LinearMap.range J)
    (hPJ : LinearMap.range P ≤ LinearMap.range J) (hQT : Q.comp T = 0) :
    Module.finrank ℝ A + Module.finrank ℝ (LinearMap.range (Q.comp P)) ≤
      Module.finrank ℝ (LinearMap.range J) := by
  let S := LinearMap.range J
  let Qs : S →ₗ[ℝ] W := Q.domRestrict S
  let Ts : A →ₗ[ℝ] S := T.codRestrict S (fun a ↦ hTJ ⟨a, rfl⟩)
  have hTker (a : A) : Ts a ∈ LinearMap.ker Qs := by
    change Q (T a) = 0
    exact DFunLike.congr_fun hQT a
  let Tk : A →ₗ[ℝ] LinearMap.ker Qs := Ts.codRestrict _ hTker
  have hTk : Injective Tk := by
    intro a a' haa
    apply hT
    exact congrArg (fun v : LinearMap.ker Qs ↦ ((v : S) : V)) haa
  have hkernel : Module.finrank ℝ A ≤ Module.finrank ℝ (LinearMap.ker Qs) :=
    LinearMap.finrank_le_finrank_of_injective hTk
  have hrange : LinearMap.range (Q.comp P) ≤ LinearMap.range Qs := by
    rintro w ⟨b, rfl⟩
    exact ⟨⟨P b, hPJ ⟨b, rfl⟩⟩, rfl⟩
  have hprojected := Submodule.finrank_mono hrange
  have hnullity := Qs.finrank_range_add_finrank_ker
  change Module.finrank ℝ A + Module.finrank ℝ (LinearMap.range (Q.comp P)) ≤
    Module.finrank ℝ S
  omega

end RankNullity

section VectorValuedRank

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Taking the native vector-valued derivative only applies the canonical
target tangent equivalence, so it leaves the dimension of the actual manifold
differential image unchanged. Source: converting the actual coincidence
calculation to the exact rank interface of the accepted avoidance theorem. -/
theorem finrank_range_mvfderiv_eq_mfderiv (f : M → V) (x : M) :
    Module.finrank ℝ (LinearMap.range (mvfderiv I f x).toLinearMap) =
      Module.finrank ℝ (LinearMap.range (mfderiv I 𝓘(ℝ, V) f x).toLinearMap) := by
  change Module.finrank ℝ (LinearMap.range
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).toLinearEquiv.toLinearMap.comp
      (mfderiv I 𝓘(ℝ, V) f x).toLinearMap)) = _
  rw [LinearMap.range_comp]
  exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).toLinearEquiv.finrank_map_eq _

end VectorValuedRank

section ActualPartialDerivatives

variable {p N : ℕ} {E M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

local instance rankPairChartedSpace : ChartedSpace (E × E) (M × M) :=
  prodChartedSpace E M E M

/-- The actual parameter difference projected to the original normal space at
the first point of the SAME family member. Both source values are retained,
including the second point's global repair remainder. -/
def coincidenceParameterNormalDerivative
    (G : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N))
    (u : Fin p → ℝ) (x y : M) :
    (Fin p → ℝ) →L[ℝ] normalSpace (I := 𝓘(ℝ, E)) (G u) x :=
  (normalSpace (I := 𝓘(ℝ, E)) (G u) x).orthogonalProjectionOnto.comp
    (fderiv ℝ (fun v ↦ G v x - G v y) u)

/-- Holding the parameter and second point fixed gives exactly the first
source differential, followed by the existing Euclidean coordinate map.
Subtracting the second value contributes zero. No derivative identity is an
input. Source: the tangent columns of the actual coincidence equation. -/
theorem mfderiv_coincidence_first_source
    (G : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N))
    (u : Fin p → ℝ) (x y : M)
    (hG : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (G u) x) :
    (tangentSpaceCastModel 𝓘(ℝ, Fin N → ℝ) (euclideanCoincidenceMap G (u, x, y))).toContinuousLinearMap.comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin N → ℝ)
        (fun z ↦ euclideanCoincidenceMap G (u, z, y)) x) =
      (EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap.comp
        ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (G u x)).toContinuousLinearMap.comp
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (G u) x)) := by
  have heq : (fun z ↦ euclideanCoincidenceMap G (u, z, y)) =
      (EuclideanSpace.equiv (Fin N) ℝ) ∘ (G u - fun _ ↦ G u y) := rfl
  change mvfderiv 𝓘(ℝ, E) (fun z ↦ euclideanCoincidenceMap G (u, z, y)) x =
    (EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap.comp (mvfderiv 𝓘(ℝ, E) (G u) x)
  rw [heq]
  rw [mvfderiv_comp x (EuclideanSpace.equiv (Fin N) ℝ).mdifferentiableAt
    (hG.sub mdifferentiableAt_const), mvfderiv_eq_fderiv,
    (EuclideanSpace.equiv (Fin N) ℝ).hasFDerivAt.fderiv]
  change (EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap.comp
    (mvfderiv 𝓘(ℝ, E) (G u - fun _ ↦ G u y) x) = _
  rw [mvfderiv_sub hG mdifferentiableAt_const, mvfderiv_const, sub_zero]

omit [TopologicalSpace M] in
/-- The actual parameter slice derivative is the derivative of the full
two-value difference, followed by the same Euclidean coordinate equivalence.
Source: the actual parameter columns, including both global remainders. -/
theorem mfderiv_coincidence_parameter
    (G : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N))
    (u : Fin p → ℝ) (x y : M)
    (hG : DifferentiableAt ℝ (fun v ↦ G v x - G v y) u) :
    (tangentSpaceCastModel 𝓘(ℝ, Fin N → ℝ) (euclideanCoincidenceMap G (u, x, y))).toContinuousLinearMap.comp
      (mfderiv 𝓘(ℝ, Fin p → ℝ) 𝓘(ℝ, Fin N → ℝ)
        (fun v ↦ euclideanCoincidenceMap G (v, x, y)) u) =
      ((EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap.comp
        (fderiv ℝ (fun v ↦ G v x - G v y) u)).comp
          (tangentSpaceCastModel 𝓘(ℝ, Fin p → ℝ) u).toContinuousLinearMap := by
  have heq : (fun v ↦ euclideanCoincidenceMap G (v, x, y)) =
      (EuclideanSpace.equiv (Fin N) ℝ) ∘ (fun v ↦ G v x - G v y) := rfl
  change mvfderiv 𝓘(ℝ, Fin p → ℝ) (fun v ↦ euclideanCoincidenceMap G (v, x, y)) u = _
  rw [heq, mvfderiv_eq_fderiv]
  rw [((EuclideanSpace.equiv (Fin N) ℝ).hasFDerivAt.comp u hG.hasFDerivAt).fderiv]
  ext v
  rfl

/-- The ACTUAL joint coincidence differential contains all `dim M` tangent
directions and as many additional directions as the actual parameter difference
has after projection to the original normal space at the first point.

The normal derivative is the literal `PN_x ∘ D_u(G(u,x)-G(u,y))`; neither the
second value nor its remainder is dropped. The three differentiability inputs
are discharged from a jointly smooth family by the subsequent consumer.
No joint-rank premise or desired matrix is supplied.

Proof: native chain rules for the first-source and parameter inclusions put
both actual partial images in the joint image. The first partial is injective
by the actual immersion, and its normal projection is zero by the ORIGINAL
normal-projection theorem. Native rank-nullity adds the two dimensions.
Source: the final value-coincidence rank calculation in `thm:upgrade`.
-/
theorem coincidence_joint_rank_ge_tangent_add_normal
    [FiniteDimensional ℝ E]
    (G : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N))
    (u : Fin p → ℝ) (x y : M)
    (hD : MDifferentiableAt ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E × E)) 𝓘(ℝ, Fin N → ℝ)
      (euclideanCoincidenceMap G) (u, x, y))
    (hGx : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (G u) x)
    (hGu : DifferentiableAt ℝ (fun v ↦ G v x - G v y) u)
    (himm : Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (G u) x)) :
    Module.finrank ℝ E +
        Module.finrank ℝ (LinearMap.range (coincidenceParameterNormalDerivative (E := E) G u x y).toLinearMap) ≤
      Module.finrank ℝ (LinearMap.range
        (mfderiv ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E × E)) 𝓘(ℝ, Fin N → ℝ)
          (euclideanCoincidenceMap G) (u, x, y)).toLinearMap) := by
  let J := mvfderiv ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E × E))
    (euclideanCoincidenceMap G) (u, x, y)
  let T := mvfderiv 𝓘(ℝ, E) (fun z ↦ euclideanCoincidenceMap G (u, z, y)) x
  let P := mvfderiv 𝓘(ℝ, Fin p → ℝ) (fun v ↦ euclideanCoincidenceMap G (v, x, y)) u
  let Q := (normalSpace (I := 𝓘(ℝ, E)) (G u) x).orthogonalProjectionOnto.comp
    (EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap
  have hpair : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E × E) (fun z : M ↦ (z, y)) x := by
    rw [modelWithCornersSelf_prod]
    exact mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hsource : MDifferentiableAt 𝓘(ℝ, E)
      ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E × E))
      (fun z : M ↦ (u, z, y)) x := mdifferentiableAt_const.prodMk hpair
  have hparam : MDifferentiableAt 𝓘(ℝ, Fin p → ℝ)
      ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E × E))
      (fun v : Fin p → ℝ ↦ (v, x, y)) u :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hTJ : LinearMap.range T.toLinearMap ≤ LinearMap.range J.toLinearMap := by
    rintro w ⟨v, rfl⟩
    refine ⟨mfderiv 𝓘(ℝ, E) ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E × E))
      (fun z : M ↦ (u, z, y)) x v, ?_⟩
    exact (DFunLike.congr_fun (mvfderiv_comp x hD hsource) v).symm
  have hPJ : LinearMap.range P.toLinearMap ≤ LinearMap.range J.toLinearMap := by
    rintro w ⟨v, rfl⟩
    refine ⟨mfderiv 𝓘(ℝ, Fin p → ℝ) ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E × E))
      (fun v : Fin p → ℝ ↦ (v, x, y)) u v, ?_⟩
    exact (DFunLike.congr_fun (mvfderiv_comp u hD hparam) v).symm
  have hTformula := mfderiv_coincidence_first_source G u x y hGx
  have hPformula := mfderiv_coincidence_parameter G u x y hGu
  have hTinj : Injective T.toLinearMap := by
    change Injective (mvfderiv 𝓘(ℝ, E) (fun z ↦ euclideanCoincidenceMap G (u, z, y)) x)
    change Injective ((tangentSpaceCastModel 𝓘(ℝ, Fin N → ℝ)
      (euclideanCoincidenceMap G (u, x, y))).toContinuousLinearMap.comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin N → ℝ) (fun z ↦ euclideanCoincidenceMap G (u, z, y)) x))
    rw [hTformula]
    exact (EuclideanSpace.equiv (Fin N) ℝ).injective.comp
      ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (G u x)).injective.comp himm)
  have hQT : Q.toLinearMap.comp T.toLinearMap = 0 := by
    apply LinearMap.ext
    intro v
    change (normalSpace (I := 𝓘(ℝ, E)) (G u) x).orthogonalProjectionOnto
      ((EuclideanSpace.equiv (Fin N) ℝ).symm (T v)) = 0
    have hv := DFunLike.congr_fun hTformula v
    change T v = (EuclideanSpace.equiv (Fin N) ℝ)
      (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (G u x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (G u) x v)) at hv
    rw [hv, ContinuousLinearEquiv.symm_apply_apply]
    exact normal_projection_mfderiv_eq_zero (G u) x v
  have hQP : Q.toLinearMap.comp P.toLinearMap =
      (coincidenceParameterNormalDerivative (E := E) G u x y).toLinearMap.comp
        (tangentSpaceCastModel 𝓘(ℝ, Fin p → ℝ) u).toLinearEquiv.toLinearMap := by
    apply LinearMap.ext
    intro v
    change (normalSpace (I := 𝓘(ℝ, E)) (G u) x).orthogonalProjectionOnto
      ((EuclideanSpace.equiv (Fin N) ℝ).symm (P v)) = _
    have hv := DFunLike.congr_fun hPformula v
    change P v = (EuclideanSpace.equiv (Fin N) ℝ)
      (fderiv ℝ (fun v ↦ G v x - G v y) u
        (tangentSpaceCastModel 𝓘(ℝ, Fin p → ℝ) u v)) at hv
    rw [hv, ContinuousLinearEquiv.symm_apply_apply]
    rfl
  have hPRange : LinearMap.range (Q.toLinearMap.comp P.toLinearMap) =
      LinearMap.range (coincidenceParameterNormalDerivative (E := E) G u x y).toLinearMap := by
    rw [hQP]
    exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr
      (tangentSpaceCastModel 𝓘(ℝ, Fin p → ℝ) u).surjective)
  have hrank := finrank_joint_range_ge_tangent_add_projected_parameter
    J.toLinearMap T.toLinearMap P.toLinearMap Q.toLinearMap hTinj hTJ hPJ hQT
  rw [hPRange] at hrank
  have hdim : Module.finrank ℝ (TangentSpace 𝓘(ℝ, E) x) = Module.finrank ℝ E :=
    (tangentSpaceCastModel 𝓘(ℝ, E) x).toLinearEquiv.finrank_eq
  rw [hdim] at hrank
  exact hrank.trans_eq (finrank_range_mvfderiv_eq_mfderiv (euclideanCoincidenceMap G) (u, x, y))

/-- Joint smoothness of the same family discharges every differentiability
premise of the actual rank calculation. A lower bound `r` for the actual
normal projection of the full parameter difference gives joint rank at least
`dim M+r` at the same point.

The normal rank is the upstream probe output; no actual joint-rank condition
is assumed. Source: the value-coincidence rank interface in `thm:upgrade`.
-/
theorem coincidence_joint_rank_of_parameter_normal_rank
    [FiniteDimensional ℝ E]
    (G : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N))
    (Pdom : Set (Fin p → ℝ)) (hPdom : IsOpen Pdom)
    (hG : ContMDiffOn ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (Function.uncurry G) (Pdom ×ˢ Set.univ))
    (u : Fin p → ℝ) (hu : u ∈ Pdom) (x y : M)
    (himm : Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (G u) x))
    (r : ℕ)
    (hnormal : r ≤ Module.finrank ℝ (LinearMap.range
      (coincidenceParameterNormalDerivative (E := E) G u x y).toLinearMap)) :
    Module.finrank ℝ E + r ≤ Module.finrank ℝ (LinearMap.range
      (mfderiv ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E × E)) 𝓘(ℝ, Fin N → ℝ)
        (euclideanCoincidenceMap G) (u, x, y)).toLinearMap) := by
  have hGAt (z : M) : ContMDiffAt ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (Function.uncurry G) (u, z) :=
    hG.contMDiffAt ((hPdom.prod isOpen_univ).mem_nhds ⟨hu, Set.mem_univ z⟩)
  have hD : MDifferentiableAt ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E × E))
      𝓘(ℝ, Fin N → ℝ) (euclideanCoincidenceMap G) (u, x, y) :=
    ((contMDiffOn_euclideanCoincidenceMap G Pdom hG).contMDiffAt
      ((hPdom.prod isOpen_univ).mem_nhds ⟨hu, Set.mem_univ (x, y)⟩)).mdifferentiableAt (by simp)
  have hGx := ((hGAt x).curry_right).mdifferentiableAt (by simp)
  have hGu : DifferentiableAt ℝ (fun v ↦ G v x - G v y) u :=
    (((hGAt x).curry_left.sub (hGAt y).curry_left).contDiffAt).differentiableAt (by simp)
  exact (Nat.add_le_add_left hnormal _).trans
    (coincidence_joint_rank_ge_tangent_add_normal G u x y hD hGx hGu himm)

/-- In particular, the actual immersion and `n+1` actual parameter-normal
directions give joint coincidence rank at least `2n+1`, strictly greater than
the pair-source dimension `2n`. Source: the exact rank threshold for the
accepted finite-parameter avoidance theorem in the final value operation. -/
theorem coincidence_joint_rank_gt_pair_dimension
    [FiniteDimensional ℝ E]
    (G : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N))
    (Pdom : Set (Fin p → ℝ)) (hPdom : IsOpen Pdom)
    (hG : ContMDiffOn ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (Function.uncurry G) (Pdom ×ˢ Set.univ))
    (u : Fin p → ℝ) (hu : u ∈ Pdom) (x y : M)
    (himm : Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (G u) x))
    (hnormal : Module.finrank ℝ E + 1 ≤ Module.finrank ℝ (LinearMap.range
      (coincidenceParameterNormalDerivative (E := E) G u x y).toLinearMap)) :
    2 * Module.finrank ℝ E + 1 ≤ Module.finrank ℝ (LinearMap.range
      (mfderiv ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E × E)) 𝓘(ℝ, Fin N → ℝ)
        (euclideanCoincidenceMap G) (u, x, y)).toLinearMap) := by
  have h := coincidence_joint_rank_of_parameter_normal_rank G Pdom hPdom hG
    u hu x y himm (Module.finrank ℝ E + 1) hnormal
  omega

section Avoidance

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [SecondCountableTopology M]

/-- The actual normal parameter-rank provider now suffices for the ORIGINAL
accepted avoidance theorem applied to the SAME coincidence map. No joint-rank
hypothesis and no already good parameter are assumed.
Source: the final value-coincidence avoidance operation in `thm:upgrade`. -/
theorem exists_parameter_without_offDiagonal_coincidences_of_normal_rank
    (G : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N))
    (Pdom : Set (Fin p → ℝ)) (hPdom : IsOpen Pdom) (hPne : Pdom.Nonempty)
    (V : Set (M × M))
    (hG : ContMDiffOn ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (Function.uncurry G) (Pdom ×ˢ Set.univ))
    (himm : ∀ u ∈ Pdom, ∀ x, Injective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (G u) x))
    (hnormal : ∀ u ∈ Pdom, ∀ x y, (x, y) ∉ V → G u x = G u y →
      Module.finrank ℝ E + 1 ≤ Module.finrank ℝ (LinearMap.range
        (coincidenceParameterNormalDerivative (E := E) G u x y).toLinearMap)) :
    ∃ u ∈ Pdom, ∀ x y, (x, y) ∉ V → G u x ≠ G u y := by
  apply exists_parameter_without_offDiagonal_coincidences G Pdom hPdom hPne V
    (contMDiffOn_euclideanCoincidenceMap G Pdom hG)
    (k := 2 * Module.finrank ℝ E + 1) (by omega)
  rintro ⟨u, x, y⟩ hu hV hcoin
  exact coincidence_joint_rank_gt_pair_dimension G Pdom hPdom hG u hu x y
    (himm u hu x) (hnormal u hu x y hV hcoin)

end Avoidance

end ActualPartialDerivatives

section PaperNormEndpoint

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [CompactSpace M]

local instance normalRankCoordinatePairChartedSpace :
    ChartedSpace ((Fin n → ℝ) × (Fin n → ℝ)) (M × M) :=
  prodChartedSpace (Fin n → ℝ) M (Fin n → ℝ) M

/-- A fixed actual compact immersion supplies an original finite-atlas C¹
tolerance and diagonal neighborhood. Any SAME-metric jointly smooth family
inside that tolerance, whose ACTUAL normal parameter difference has rank at
least `n+1` at relevant coincidences, contains an actual smooth immersive
closed embedding with the same metric.

No joint coincidence rank, local injectivity, or already good parameter is a
premise: the preceding native derivative calculation, the original C¹ diagonal
separation theorem, and accepted avoidance prove them. The actual parameter
normal-rank provider is the remaining paired-probe obligation; this does not
claim the full geometric upgrade theorem has been constructed.
Source: the final analytic consumer of `upgrade-remove-value-coincidences`.
-/
theorem exists_paperAtlasC1_sameMetric_embedding_from_normal_rank
    (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f)
    (hinj : ∀ x, Injective
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f x)) :
    ∃ centers : Finset M, ∃ r : M → ℝ, ∃ delta : ℝ, ∃ V : Set (M × M),
      0 < delta ∧
      (∀ x, 0 < r x ∧ Metric.closedBall (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) (r x) ⊆
        interior (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target) ∧
      IsOpen V ∧ Set.diagonal M ⊆ V ∧
      (∀ x y, (x, y) ∈ V → (y, x) ∈ V) ∧ IsCompact Vᶜ ∧
      (∀ z ∈ Vᶜ, z.1 ≠ z.2) ∧
      ∀ (p : ℕ) (Pdom : Set (Fin p → ℝ)), IsOpen Pdom → Pdom.Nonempty →
        ∀ G : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N),
        ContMDiffOn ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, Fin n → ℝ))
          𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (Function.uncurry G) (Pdom ×ˢ Set.univ) →
        (∀ u ∈ Pdom, ∀ x, inducedMetric (I := 𝓘(ℝ, Fin n → ℝ)) (G u) x =
          inducedMetric (I := 𝓘(ℝ, Fin n → ℝ)) f x) →
        (∀ u ∈ Pdom,
          let e := EuclideanSpace.equiv (Fin N) ℝ
          let cf : centers → (Fin n → ℝ) → Fin N → ℝ :=
            fun x ↦ e ∘ f ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x.1).symm
          let cg : centers → (Fin n → ℝ) → Fin N → ℝ :=
            fun x ↦ e ∘ G u ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x.1).symm
          let O : centers → Set (Fin n → ℝ) :=
            fun x ↦ interior (extChartAt 𝓘(ℝ, Fin n → ℝ) x.1).target
          let S : centers → Set (Fin n → ℝ) :=
            fun x ↦ Metric.closedBall (extChartAt 𝓘(ℝ, Fin n → ℝ) x.1 x.1) (r x.1)
          (paperAtlasCj 1 (fun x ↦ cg x - cf x) O S).toReal < delta) →
        (∀ u ∈ Pdom, ∀ x y, (x, y) ∉ V → G u x = G u y →
          n + 1 ≤ Module.finrank ℝ (LinearMap.range
            (coincidenceParameterNormalDerivative (E := Fin n → ℝ) G u x y).toLinearMap)) →
        ∃ u ∈ Pdom,
          ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (G u) ∧
          (∀ x, Injective
            (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (G u) x)) ∧
          Topology.IsClosedEmbedding (G u) ∧
          (∀ x, inducedMetric (I := 𝓘(ℝ, Fin n → ℝ)) (G u) x =
            inducedMetric (I := 𝓘(ℝ, Fin n → ℝ)) f x) := by
  obtain ⟨centers, r, delta, V, hdelta, hball, hV, hdiag, hsym, hcompact, hoff, hcriterion⟩ :=
    exists_paperAtlasC1_sameMetric_embedding_criterion f hf hinj
  refine ⟨centers, r, delta, V, hdelta, hball, hV, hdiag, hsym, hcompact, hoff, ?_⟩
  intro p Pdom hP hPne G hG hmetric hclose hnormal
  apply hcriterion p Pdom hP hPne G hG hmetric hclose (2 * n + 1) (by omega)
  rintro ⟨u, x, y⟩ hu hxy hcoin
  have himm := immersion_of_inducedMetric_eq f (G u) x (hmetric u hu x) (hinj x)
  have hnormal' : Module.finrank ℝ (Fin n → ℝ) + 1 ≤ Module.finrank ℝ
      (LinearMap.range (coincidenceParameterNormalDerivative (E := Fin n → ℝ) G u x y).toLinearMap) := by
    simpa only [Module.finrank_fin_fun] using hnormal u hu x y hxy hcoin
  simpa only [Module.finrank_fin_fun] using
    coincidence_joint_rank_gt_pair_dimension G Pdom hP hG u hu x y himm hnormal'

end PaperNormEndpoint

#print axioms finrank_joint_range_ge_tangent_add_projected_parameter
#print axioms finrank_range_mvfderiv_eq_mfderiv
#print axioms mfderiv_coincidence_first_source
#print axioms mfderiv_coincidence_parameter
#print axioms coincidence_joint_rank_ge_tangent_add_normal
#print axioms coincidence_joint_rank_of_parameter_normal_rank
#print axioms coincidence_joint_rank_gt_pair_dimension
#print axioms exists_parameter_without_offDiagonal_coincidences_of_normal_rank
#print axioms exists_paperAtlasC1_sameMetric_embedding_from_normal_rank

end GlobalEmbedding.Offline
