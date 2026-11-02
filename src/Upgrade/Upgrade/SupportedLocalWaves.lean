import Upgrade.SupportedLegalPacket
import GlobalEmbedding.Paper.UpgradeLocalLegalWave
import GlobalEmbedding.Paper.PhaseRegular
import GlobalEmbedding.Paper.ImmersionNormalRank
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Order.Filter.Finite

/-!
# Actual finite supported-normal wave packet on the original immersion

Source: `thm:upgrade`, main.tex 1073--1083. This is the missing geometric
input between the accepted strong supported-rank theorem and paired probes.
Every selected actual normal equation column is realized by a genuine local
legal wave on the SAME immersion, with its cutoff supported away from the
second point. The equation is the one constructed by supported-rank.
-/

noncomputable section
open Bundle Filter Manifold Module Set
open scoped BigOperators ContDiff Topology

namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

/-- A supported full-rank point of an actual phase-regular immersion supplies
q independent actual supported-normal columns, realized by finite legal waves
with support away from any specified distinct partner. No orientation or global
normal frame is selected. Native finite intersections make all cutoffs one near
x and zero near y. These are second-form-normal directions; when n=3 this
asserts exactly the geometric input for joint supported-coincidence removal,
not elimination of the supported locus. -/
theorem exists_supported_finite_local_legal_waves
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
    (honto : Function.Surjective (trueSecondForm F hF x))
    (hsupported : HasSupportedKernel (trueSecondForm F hF x)) :
    let B : SymmetricSquare (EuclideanSpace ℝ (Fin n)) →L[ℝ] normalSpace (I := I) F x :=
      LinearMap.toContinuousLinearMap (trueSecondForm F hF x)
    let q := n * (n - 1) / 2
    ∃ chart : SupportedLocusLocalEquations
        {C : SymmetricSquare (EuclideanSpace ℝ (Fin n)) →L[ℝ] normalSpace (I := I) F x |
          Function.Surjective C ∧ LinearSecondFormPhaseRegular C.toLinearMap}
        {C : SymmetricSquare (EuclideanSpace ℝ (Fin n)) →L[ℝ] normalSpace (I := I) F x |
          HasSupportedKernel C.toLinearMap} B,
      ∃ (xi : Fin q → TangentSpace I x →L[ℝ] ℝ)
        (nu : Fin q → normalSpace (I := I) F x)
        (U : Fin q → Set M) (psi : Fin q → M → ℝ)
        (v : Fin q → ∀ z : M, normalSpace (I := I) F z)
        (chi : Fin q → SmoothBumpFunction I x),
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
      let A (i : Fin q) (z : M) : SymmetricSquare (TangentSpace I z) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin N) :=
        chi i z • supportedRankLegalVariation
          (mfderiv I 𝓘(ℝ, ℝ) (psi i) z).toLinearMap (v i z : EuclideanSpace ℝ (Fin N))
      (∀ i, A i x = supportedRankLegalVariation (xi i).toLinearMap
        (nu i : EuclideanSpace ℝ (Fin N))) ∧
      (∀ (i : Fin q) (a : M) (u w : EuclideanSpace ℝ (Fin n)),
        ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
          (fun z ↦ A i z (symmetricSquareProduct (TangentSpace I z)
            ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) a).symmL ℝ z u)
            ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) a).symmL ℝ z w)))
          (chartAt H a).source) ∧
      LinearIndependent ℝ (fun i ↦ (fderiv ℝ chart.equation B)
        ((normalSpace (I := I) F x).orthogonalProjectionOnto.comp
          (LinearMap.toContinuousLinearMap (A i x)))) := by
  classical
  dsimp only
  let B : SymmetricSquare (EuclideanSpace ℝ (Fin n)) →L[ℝ] normalSpace (I := I) F x :=
    LinearMap.toContinuousLinearMap (trueSecondForm F hF x)
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
  have hp := exists_supported_legal_equation_packet B honto hphaseB hsupported
    (by simpa only [finrank_euclideanSpace_fin] using hn)
    (by simpa only [finrank_euclideanSpace_fin] using hW)
  dsimp only at hp
  rw [finrank_euclideanSpace_fin] at hp
  obtain ⟨chart, eta, nu, hgood, hli⟩ := hp
  let xi : Fin (n * (n - 1) / 2) → TangentSpace I x →L[ℝ] ℝ := fun i ↦
    (eta i).toContinuousLinearMap
  have hxi (i : Fin (n * (n - 1) / 2)) : GoodCovector F hF x (xi i) := by
    refine ⟨?_, (hgood i).1.2⟩
    intro hz
    apply (hgood i).1.1
    exact congrArg ContinuousLinearMap.toLinearMap hz
  have hnu (i : Fin (n * (n - 1) / 2)) : nu i ∈
      supportedRankLegalValueSpace (trueSecondForm F hF x) (xi i).toLinearMap :=
    (hgood i).2
  have hw (i : Fin (n * (n - 1) / 2)) :=
    upgrade_exists_local_legal_wave F hF himm x y hxy (xi i) (hxi i) (nu i) (hnu i)
  choose U psi v chi hU hxU hUsub hchi hy hpsi hpsix hvx hv hlegal hglob hcol using hw
  let A (i : Fin (n * (n - 1) / 2)) (z : M) : SymmetricSquare (TangentSpace I z) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin N) :=
    chi i z • supportedRankLegalVariation
      (mfderiv I 𝓘(ℝ, ℝ) (psi i) z).toLinearMap (v i z : EuclideanSpace ℝ (Fin N))
  have hone : ∀ᶠ z in 𝓝 x, ∀ i, chi i z = 1 :=
    Filter.eventually_all.mpr fun i ↦ (chi i).eventuallyEq_one
  have hzero : ∀ᶠ z in 𝓝 y, ∀ i, chi i z = 0 := by
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [(isClosed_tsupport (chi i : M → ℝ)).isOpen_compl.mem_nhds (hy i)]
      with z hz
    exact image_eq_zero_of_notMem_tsupport hz
  have hproj (i : Fin (n * (n - 1) / 2)) :
      (normalSpace (I := I) F x).orthogonalProjectionOnto.comp
        (LinearMap.toContinuousLinearMap
          (show SymmetricSquare (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ]
            EuclideanSpace ℝ (Fin N) from A i x)) =
          (supportedRankLegalVariation (eta i) (nu i)).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro a
    change (normalSpace (I := I) F x).orthogonalProjectionOnto (A i x a) =
      supportedRankCovectorSquare (eta i) a • nu i
    rw [show A i x a = supportedRankCovectorSquare (eta i) a •
        (nu i : EuclideanSpace ℝ (Fin N)) from DFunLike.congr_fun (hcol i) a]
    rw [map_smul, (normalSpace (I := I) F x).orthogonalProjectionOnto_mem_subspace_eq_self]
  refine ⟨chart, xi, nu, U, psi, v, chi, ?_, hone, hzero, hcol, hglob, ?_⟩
  · intro i
    exact ⟨hxi i, hnu i, hU i, hxU i, hUsub i, hchi i, hy i, hpsi i, hpsix i,
      hvx i, hv i, hlegal i⟩
  · change LinearIndependent ℝ (fun i ↦ (fderiv ℝ chart.equation B)
        ((normalSpace (I := I) F x).orthogonalProjectionOnto.comp
          (LinearMap.toContinuousLinearMap
            (show SymmetricSquare (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ]
              EuclideanSpace ℝ (Fin N) from A i x))))
    simpa only [hproj] using hli

#print axioms exists_supported_finite_local_legal_waves

end GlobalEmbedding.Upgrade
