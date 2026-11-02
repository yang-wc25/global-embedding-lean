import GlobalEmbedding.Paper.UpgradeRankQLegalOperatorPacket
import GlobalEmbedding.Paper.UpgradeLocalLegalWave
import GlobalEmbedding.Paper.PhaseRegular
import GlobalEmbedding.Paper.ImmersionNormalRank
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Order.Filter.Finite

/-!
# Finite actual local legal waves with an onto rank-normal response

Source: original main.tex, thm:upgrade1053–1057 and defn:legal840–843.
DAG: upgrade-rank-q-finite-local-legal-waves. This bounded consumer joins the
accepted finite operator packet and complete actual local legal-wave theorem.
It constructs only an actual second-form tensor family, not an immersion family
with prescribed metric, a probe realization, or a Schur/incidence theorem.
-/

noncomputable section

open Bundle Filter Manifold Module Set
open scoped BigOperators ContDiff Topology

namespace GlobalEmbedding.Paper

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

/-- At an original rank-q point of an actual phase-regular Euclidean immersion,
n actual legal waves realize an onto derivative of the SAME rank-normal block.
Each wave uses its actual local phase, normal field and native chart bump, has
support away from y, and has globally smooth coefficients in every actual tangent
frame. The finite cutoffs are simultaneously one near x and zero near y. The
parameter tensor is their literal finite sum. Its value at x, projected into the
actual original normal space, gives the genuine parameter-dependent block.

Proof: view the SAME algebraic true second form on the original Euclidean model
and use its existing canonical quotient norm for native continuous-linear maps.
No norm or inner product is assigned to the tangent bundle. The accepted actual
immersion normal-rank theorem and the original N=s_n+1 give normal dimension
q+1. Original phase regularity supplies the actual linear phase condition.
Apply the sole accepted finite legal operator packet once, obtaining n actual
good covectors, legal normal values and its surjective normal-block derivative.
Convert the selected finite-dimensional covectors natively to actual continuous
cotangents. Apply the sole accepted local legal-wave theorem to every selected
pair and the SAME x,y, retaining each exact column at x and all actual local
legality and global-frame smoothness fields. Native finite-filter intersection
gives simultaneous bump value one near x and zero near y. Native finite sums and
scalar multiplication prove smoothness of the literal parameter tensor in every
actual frame. Exact columns at x and the native normal projection fixing actual
normal values identify its projected parameter map with the accepted packet.
Rewrite this equality in that packet's genuine derivative conclusion, keeping
the SAME actual kernel and range-perpendicular line throughout. No desired
span, basis, local wave or surjectivity is supplied as a premise.
Source: thm:upgrade1053–1057, defn:legal840–843. -/
theorem upgradeRankQ_exists_finite_local_legal_waves
    {n N : ℕ} {H M : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] [T2Space M]
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n)
    (hN : N = n * (n + 1) / 2 + 1)
    (x y : M) (hxy : x ≠ y)
    (hrank : finrank ℝ (trueSecondForm F hF x).range = n * (n - 1) / 2) :
    let B : SymmetricSquare (EuclideanSpace ℝ (Fin n)) →L[ℝ] normalSpace (I := I) F x :=
      LinearMap.toContinuousLinearMap (trueSecondForm F hF x)
    let K := B.toLinearMap.ker
    let L := B.toLinearMap.rangeᗮ
    ∃ (xi : Fin n → TangentSpace I x →L[ℝ] ℝ)
      (nu : Fin n → normalSpace (I := I) F x)
      (U : Fin n → Set M) (psi : Fin n → M → ℝ)
      (v : Fin n → ∀ z : M, normalSpace (I := I) F z)
      (chi : Fin n → SmoothBumpFunction I x),
      (∀ i, GoodCovector F hF x (xi i) ∧
        nu i ∈ supportedRankLegalValueSpace (trueSecondForm F hF x) (xi i).toLinearMap ∧
        IsOpen (U i) ∧ x ∈ U i ∧ U i ⊆ (chartAt H x).source ∧
        tsupport (chi i : M → ℝ) ⊆ U i ∧ y ∉ tsupport (chi i : M → ℝ) ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (psi i) (U i) ∧
        mfderiv I 𝓘(ℝ, ℝ) (psi i) x = xi i ∧ v i x = nu i ∧
        ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
          (fun z ↦ (v i z : EuclideanSpace ℝ (Fin N))) (U i) ∧
        (∀ z ∈ U i, GoodCovector F hF z (mfderiv I 𝓘(ℝ, ℝ) (psi i) z) ∧
          v i z ∈ supportedRankLegalValueSpace (trueSecondForm F hF z)
            (mfderiv I 𝓘(ℝ, ℝ) (psi i) z).toLinearMap)) ∧
      (∀ᶠ z in 𝓝 x, ∀ i, chi i z = 1) ∧
      (∀ᶠ z in 𝓝 y, ∀ i, chi i z = 0) ∧
      let A (i : Fin n) (z : M) : SymmetricSquare (TangentSpace I z) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin N) :=
        chi i z • supportedRankLegalVariation
          (mfderiv I 𝓘(ℝ, ℝ) (psi i) z).toLinearMap (v i z : EuclideanSpace ℝ (Fin N))
      let S (t : Fin n → ℝ) (z : M) := ∑ i, t i • A i z
      (∀ i, A i x = supportedRankLegalVariation (xi i).toLinearMap
        (nu i : EuclideanSpace ℝ (Fin N))) ∧
      (∀ (i : Fin n) (a : M) (u w : EuclideanSpace ℝ (Fin n)),
        ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
          (fun z ↦ A i z (symmetricSquareProduct (TangentSpace I z)
            ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) a).symmL ℝ z u)
            ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) a).symmL ℝ z w)))
          (chartAt H a).source) ∧
      (∀ (t : Fin n → ℝ) (a : M) (u w : EuclideanSpace ℝ (Fin n)),
        ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
          (fun z ↦ S t z (symmetricSquareProduct (TangentSpace I z)
            ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) a).symmL ℝ z u)
            ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) a).symmL ℝ z w)))
          (chartAt H a).source) ∧
      let P : (Fin n → ℝ) → (SymmetricSquare (EuclideanSpace ℝ (Fin n)) →L[ℝ]
          normalSpace (I := I) F x) := fun t ↦
        (normalSpace (I := I) F x).orthogonalProjectionOnto.comp
          (LinearMap.toContinuousLinearMap (S t x))
      let R : (Fin n → ℝ) → (K →L[ℝ] L) := fun t ↦
        L.orthogonalProjectionOnto.comp ((B + P t).comp K.subtypeL)
      DifferentiableAt ℝ R 0 ∧ Function.Surjective (fderiv ℝ R 0) := by
  classical
  dsimp only
  let B : SymmetricSquare (EuclideanSpace ℝ (Fin n)) →L[ℝ] normalSpace (I := I) F x :=
    LinearMap.toContinuousLinearMap (trueSecondForm F hF x)
  let K := B.toLinearMap.ker
  let L := B.toLinearMap.rangeᗮ
  have hW : finrank ℝ (normalSpace (I := I) F x) = n * (n - 1) / 2 + 1 := by
    rw [immersion_normal_rank F x (himm x), finrank_euclideanSpace_fin, hN]
    have heq : n * (n + 1) = n * (n - 1) + 2 * n := by
      calc
        n * (n + 1) = n * ((n - 1) + 2) := by congr 1; omega
        _ = n * (n - 1) + 2 * n := by ring
    omega
  have hphaseB : LinearSecondFormPhaseRegular B.toLinearMap := by
    obtain ⟨eta, heta⟩ := hphase x
    refine ⟨eta.toLinearMap, ?_, heta.2⟩
    intro hz
    apply heta.1
    apply ContinuousLinearMap.ext
    intro a
    exact DFunLike.congr_fun hz a
  have hBrange : B.toLinearMap.range = (trueSecondForm F hF x).range := by rfl
  have hp := upgradeRankQ_exists_legal_operator_packet B hphaseB
    (by simpa only [finrank_euclideanSpace_fin] using hn)
    (by simpa only [finrank_euclideanSpace_fin] using hW)
    (by rw [hBrange, finrank_euclideanSpace_fin]; exact hrank)
  dsimp only at hp
  rw [finrank_euclideanSpace_fin] at hp
  obtain ⟨eta, etaNu, hgood, P, hPt, hRdiff, hRonto⟩ := hp
  let xi : Fin n → TangentSpace I x →L[ℝ] ℝ := fun i ↦
    (eta i).toContinuousLinearMap
  let nu : Fin n → normalSpace (I := I) F x := fun i ↦ (etaNu i : normalSpace F x)
  have hxi (i : Fin n) : GoodCovector F hF x (xi i) := by
    refine ⟨?_, (hgood i).1.2⟩
    intro hz
    apply (hgood i).1.1
    exact congrArg ContinuousLinearMap.toLinearMap hz
  have hnu (i : Fin n) : nu i ∈
      supportedRankLegalValueSpace (trueSecondForm F hF x) (xi i).toLinearMap :=
    (hgood i).2
  have hw (i : Fin n) :=
    upgrade_exists_local_legal_wave F hF himm x y hxy (xi i) (hxi i) (nu i) (hnu i)
  choose U psi v chi hU hxU hUsub hchi hy hpsi hpsix hvx hv hlegal hglob hcol using hw
  let A (i : Fin n) (z : M) : SymmetricSquare (TangentSpace I z) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin N) :=
    chi i z • supportedRankLegalVariation
      (mfderiv I 𝓘(ℝ, ℝ) (psi i) z).toLinearMap (v i z : EuclideanSpace ℝ (Fin N))
  let S (t : Fin n → ℝ) (z : M) := ∑ i, t i • A i z
  have hone : ∀ᶠ z in 𝓝 x, ∀ i, chi i z = 1 :=
    Filter.eventually_all.mpr fun i ↦ (chi i).eventuallyEq_one
  have hzero : ∀ᶠ z in 𝓝 y, ∀ i, chi i z = 0 := by
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [(isClosed_tsupport (chi i : M → ℝ)).isOpen_compl.mem_nhds (hy i)]
      with z hz
    exact image_eq_zero_of_notMem_tsupport hz
  let Pw : (Fin n → ℝ) → (SymmetricSquare (EuclideanSpace ℝ (Fin n)) →L[ℝ]
      normalSpace (I := I) F x) := fun t ↦
    (normalSpace (I := I) F x).orthogonalProjectionOnto.comp
      (LinearMap.toContinuousLinearMap (S t x))
  have hSx (t : Fin n → ℝ) : Pw t = P t := by
    rw [hPt]
    apply ContinuousLinearMap.ext
    intro q
    change (normalSpace (I := I) F x).orthogonalProjectionOnto ((∑ i, t i • A i x) q) =
      (∑ i, t i • (supportedRankLegalVariation (eta i)
        (etaNu i : normalSpace F x)).toContinuousLinearMap) q
    have heval : (∑ i, t i • A i x) q = ∑ i, (t i • A i x) q :=
      LinearMap.sum_apply _ _ _
    rw [heval, map_sum]
    simp only [sum_apply, smul_apply]
    apply Finset.sum_congr rfl
    intro i hi
    have hcolq : A i x q = supportedRankCovectorSquare (eta i) q •
        (nu i : EuclideanSpace ℝ (Fin N)) :=
      DFunLike.congr_fun (hcol i) q
    have hproj : (normalSpace (I := I) F x).orthogonalProjectionOnto (A i x q) =
        supportedRankCovectorSquare (eta i) q • nu i := by
      apply (congrArg (normalSpace (I := I) F x).orthogonalProjectionOnto hcolq).trans
      rw [map_smul, (normalSpace (I := I) F x).orthogonalProjectionOnto_mem_subspace_eq_self]
    exact (congrArg (normalSpace (I := I) F x).orthogonalProjectionOnto
      (LinearMap.smul_apply (t i) (A i x) q)).trans
        (((normalSpace (I := I) F x).orthogonalProjectionOnto.map_smul (t i) (A i x q)).trans
          (congrArg (fun w : normalSpace (I := I) F x ↦ t i • w) hproj))
  refine ⟨xi, nu, U, psi, v, chi, ?_, hone, hzero, hcol, hglob, ?_, ?_⟩
  · intro i
    exact ⟨hxi i, hnu i, hU i, hxU i, hUsub i, hchi i, hy i, hpsi i, hpsix i,
      hvx i, hv i, hlegal i⟩
  · intro t a u w
    have hscalar (i : Fin n) : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun _ : M ↦ t i) (chartAt H a).source := contMDiffOn_const
    have hs := contMDiffOn_finsetSum (s := (chartAt H a).source) (t := Finset.univ)
      (fun i _ ↦ (hscalar i).smul (hglob i a u w))
    apply hs.congr
    intro z hz
    let Qz := symmetricSquareProduct (TangentSpace I z)
      ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) a).symmL ℝ z u)
      ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) a).symmL ℝ z w)
    change (∑ i, t i • A i z) Qz = ∑ i, t i • A i z Qz
    have heval : (∑ i, t i • A i z) Qz = ∑ i, (t i • A i z) Qz :=
      LinearMap.sum_apply _ _ _
    exact heval.trans (Finset.sum_congr rfl fun i _ ↦ LinearMap.smul_apply (t i) (A i z) Qz)
  · change DifferentiableAt ℝ
        (fun t ↦ L.orthogonalProjectionOnto.comp ((B + Pw t).comp K.subtypeL)) 0 ∧
      Function.Surjective (fderiv ℝ
        (fun t ↦ L.orthogonalProjectionOnto.comp ((B + Pw t).comp K.subtypeL)) 0)
    have hPw : Pw = (fun t ↦ P t) := funext hSx
    rw [hPw]
    exact ⟨hRdiff, hRonto⟩

#print axioms upgradeRankQ_exists_finite_local_legal_waves

end GlobalEmbedding.Paper
