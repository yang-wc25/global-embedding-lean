import GlobalEmbedding.Paper.UpgradeRankQFiniteLocalLegalWaves
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Same-wave duplicated principal rank/value packet

Source: original main.tex1049–1052 and1057–1068.
DAG: upgrade-rank-q-duplicated-principal-packet. Principal finite columns only;
actual normalized probe derivatives and their errors remain upstream obligations.
-/

noncomputable section

open Bundle Filter Manifold Module Set
open scoped BigOperators ContDiff Topology

namespace GlobalEmbedding.Paper

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

/-- Original rank-q data admit a SAME actual finite legal-wave packet whose
principal duplicated columns separate the rank and value outputs. Each wave has
its own fixed positive unequal pair of weights. No selected normal is assumed
nonzero. The explicit scalar combinations are valid at every source point and
have one common finite coefficient bound. At x the literal principal columns,
projected to the SAME original K-to-L block and L value component, span their
whole product with dimension n+1.

Proof: call the sole accepted complete finite actual-wave theorem once and
retain all its same-data fields and actual parameter normal-block derivative.
The accepted original pointwise theorem gives dim K=n, dim L=1 and every-good
legal space equal to L. For each wave put c_j=lambda_j^-2 and Delta=c_0-c_1.
Positive unequal weights make Delta nonzero. The native two-by-two determinant
formula makes [[1,1],[-c_0,-c_1]] a unit. Direct scalar/module algebra gives the
rank-only combination (-c_1/Delta)C_0+(c_0/Delta)C_1=(A,0) and the value-only
combination (-1/Delta)C_0+(1/Delta)C_1=(0,chi nu), including where nu vanishes.
One plus the finite sum of absolute coefficients bounds all these fixed scalars.
Let D_i be the actual projected K-to-L block of A_i(x). Native finite synthesis
of D_i equals the SAME original parameter block since B kills K. Its derivative
is itself, so the already proved actual derivative onto implies span D_i=top.
Every selected value lies in L by the sole pointwise legal-space identity. They
cannot all vanish, since that would kill every D_i and contradict surjectivity
onto the n-dimensional Hom(K,L). In the actual one-dimensional L, a nonzero
selected value spans L. Project the explicit two-copy combinations: they put
(D_i,0) and (0,nu_i) in the span of the literal principal joint columns. Thus that
span is the whole product; native Hom and product dimensions give n+1.

These are principal tensor/value columns defined from actual waves. The original
prop-probes caller still must realize them as normalized radial derivatives with
its global errors. No actual exact-metric immersion family, error estimate,
Schur incidence or source-tangent joint rank 2n+1 is asserted here. The positive
unequal weights are that internal caller interface, not a new hypothesis on the
original upgrade target. Source: main.tex1049–1052 and1057–1068. -/
theorem upgradeRankQ_exists_duplicated_principal_packet
    {n N : ℕ} {H M : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] [T2Space M]
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n)
    (hN : N = n * (n + 1) / 2 + 1)
    (lambda : Fin n → Fin 2 → ℝ) (hlambda : ∀ i j, 0 < lambda i j)
    (hne : ∀ i, lambda i 0 ≠ lambda i 1)
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
      DifferentiableAt ℝ R 0 ∧ Function.Surjective (fderiv ℝ R 0) ∧
      let c (i : Fin n) (j : Fin 2) : ℝ := (lambda i j ^ 2)⁻¹
      let delta (i : Fin n) : ℝ := c i 0 - c i 1
      let C (i : Fin n) (j : Fin 2) (z : M) :
          (SymmetricSquare (TangentSpace I z) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) ×
            EuclideanSpace ℝ (Fin N) :=
        (A i z, -(c i j) • (chi i z • (v i z : EuclideanSpace ℝ (Fin N))))
      (∀ i, delta i ≠ 0 ∧ IsUnit (!![(1 : ℝ), 1; -(c i 0), -(c i 1)])) ∧
      (∀ i z, (-(c i 1) / delta i) • C i 0 z + (c i 0 / delta i) • C i 1 z =
        (A i z, 0)) ∧
      (∀ i z, (-1 / delta i) • C i 0 z + (1 / delta i) • C i 1 z =
        (0, chi i z • (v i z : EuclideanSpace ℝ (Fin N)))) ∧
      (∃ bound : ℝ, 0 < bound ∧ ∀ i,
        |c i 1 / delta i| ≤ bound ∧ |c i 0 / delta i| ≤ bound ∧
          |1 / delta i| ≤ bound) ∧
      let J (ij : Fin n × Fin 2) : (K →L[ℝ] L) × L :=
        (L.orthogonalProjectionOnto.comp
          (((normalSpace (I := I) F x).orthogonalProjectionOnto.comp
            (LinearMap.toContinuousLinearMap
              (show SymmetricSquare (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ]
                EuclideanSpace ℝ (Fin N) from (C ij.1 ij.2 x).1))).comp K.subtypeL),
          L.orthogonalProjectionOnto
            ((normalSpace (I := I) F x).orthogonalProjectionOnto (C ij.1 ij.2 x).2))
      Submodule.span ℝ (Set.range J) = ⊤ ∧
        finrank ℝ (Submodule.span ℝ (Set.range J)) = n + 1 := by
  classical
  let : FiniteDimensional ℝ (SymmetricSquare (EuclideanSpace ℝ (Fin n))) := inferInstance
  let : T2Space (SymmetricSquare (EuclideanSpace ℝ (Fin n))) := inferInstance
  let : FiniteDimensional ℝ (normalSpace (I := I) F x) :=
    Module.Finite.of_injective (normalSpace (I := I) F x).subtype
      (normalSpace (I := I) F x).injective_subtype
  let : T2Space (normalSpace (I := I) F x) := inferInstance
  let : NormedAddCommGroup (SymmetricSquare (EuclideanSpace ℝ (Fin n))) :=
    operatorSquareNormed
  let : NormedSpace ℝ (SymmetricSquare (EuclideanSpace ℝ (Fin n))) :=
    squareNS (EuclideanSpace ℝ (Fin n))
  let : NormedAddCommGroup (normalSpace (I := I) F x) :=
    Submodule.normedAddCommGroup (normalSpace (I := I) F x)
  let : NormedSpace ℝ (normalSpace (I := I) F x) := inferInstance
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
    apply DFunLike.ext
    intro a
    exact DFunLike.congr_fun hz a
  have hBrange : B.toLinearMap.range = (trueSecondForm F hF x).range := by rfl
  have hdimV : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hq : finrank ℝ (EuclideanSpace ℝ (Fin n)) *
      (finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1) / 2 = n * (n - 1) / 2 :=
    congrArg (fun r : ℕ ↦ r * (r - 1) / 2) hdimV
  have hnV : 3 ≤ finrank ℝ (EuclideanSpace ℝ (Fin n)) := hdimV.symm ▸ hn
  have hWV := hW.trans (congrArg (fun r : ℕ ↦ r + 1) hq).symm
  have hrB := (congrArg (fun R : Submodule ℝ (normalSpace (I := I) F x) ↦ finrank ℝ R)
    hBrange).trans hrank
  have hrV := hrB.trans hq.symm
  have hpointwise := upgradeRankQ_pointwise_legal_span
    (V := EuclideanSpace ℝ (Fin n)) (W := normalSpace (I := I) F x)
    B.toLinearMap hphaseB hnV hWV hrV
  have hdK : finrank ℝ K = n := hpointwise.1.trans hdimV
  have hdL := hpointwise.2.1
  have hE := hpointwise.2.2.1
  have hb := upgradeRankQ_exists_finite_local_legal_waves F hF himm hphase hn hN x y hxy hrank
  obtain ⟨xi, nu, U, psi, v, chi, hbase⟩ := hb
  have hfields := hbase.1
  have hone := hbase.2.1
  have hzero := hbase.2.2.1
  have hcol := hbase.2.2.2.1
  have hglob := hbase.2.2.2.2.1
  have hsglob := hbase.2.2.2.2.2.1
  have hRdiff := hbase.2.2.2.2.2.2.1
  have hRonto := hbase.2.2.2.2.2.2.2
  have hnuL (i : Fin n) : nu i ∈ L := by
    have hg : LinearSecondFormGoodCovector B.toLinearMap (xi i).toLinearMap := by
      refine ⟨?_, (hfields i).1.2⟩
      intro hz
      apply (hfields i).1.1
      apply DFunLike.ext
      intro a
      exact DFunLike.congr_fun hz a
    have hm : nu i ∈ supportedRankLegalValueSpace B.toLinearMap (xi i).toLinearMap :=
      (hfields i).2.1
    have hh : nu i ∈ B.toLinearMap.rangeᗮ :=
      (congrArg (fun R : Submodule ℝ (normalSpace (I := I) F x) ↦ nu i ∈ R)
        (hE (xi i).toLinearMap hg)).mp hm
    exact hh
  let A (i : Fin n) (z : M) : SymmetricSquare (TangentSpace I z) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin N) :=
    chi i z • supportedRankLegalVariation
      (mfderiv I 𝓘(ℝ, ℝ) (psi i) z).toLinearMap (v i z : EuclideanSpace ℝ (Fin N))
  let S (t : Fin n → ℝ) (z : M) := ∑ i, t i • A i z
  let Pw : (Fin n → ℝ) → (SymmetricSquare (EuclideanSpace ℝ (Fin n)) →L[ℝ]
      normalSpace (I := I) F x) := fun t ↦
    (normalSpace (I := I) F x).orthogonalProjectionOnto.comp
      (LinearMap.toContinuousLinearMap (S t x))
  let Rw : (Fin n → ℝ) → (K →L[ℝ] L) := fun t ↦
    L.orthogonalProjectionOnto.comp ((B + Pw t).comp K.subtypeL)
  let c (i : Fin n) (j : Fin 2) : ℝ := (lambda i j ^ 2)⁻¹
  let delta (i : Fin n) := c i 0 - c i 1
  let C (i : Fin n) (j : Fin 2) (z : M) :
      (SymmetricSquare (TangentSpace I z) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) ×
        EuclideanSpace ℝ (Fin N) :=
    (A i z, -(c i j) • (chi i z • (v i z : EuclideanSpace ℝ (Fin N))))
  have hd (i : Fin n) : delta i ≠ 0 := by
    intro hz
    have he : c i 0 = c i 1 := sub_eq_zero.mp hz
    have hs : lambda i 0 ^ 2 = lambda i 1 ^ 2 := inv_inj.mp he
    apply hne i
    exact (sq_eq_sq₀ (hlambda i 0).le (hlambda i 1).le).mp hs
  have hmatrix (i : Fin n) : IsUnit (!![(1 : ℝ), 1; -(c i 0), -(c i 1)]) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    have he : Matrix.det (!![(1 : ℝ), 1; -(c i 0), -(c i 1)]) = delta i := by
      rw [Matrix.det_fin_two_of]
      simp only [one_mul, sub_eq_add_neg, neg_neg, delta, add_comm]
    rw [he]
    exact hd i
  have hs0 (i : Fin n) : -(c i 1) / delta i + c i 0 / delta i = 1 := by
    calc
      _ = (c i 0 - c i 1) / delta i := by
        rw [sub_div, neg_div, sub_eq_add_neg, add_comm]
      _ = 1 := div_self (hd i)
  have hs1 (i : Fin n) :
      (-(c i 1) / delta i) * -(c i 0) + (c i 0 / delta i) * -(c i 1) = 0 := by
    ring
  have hs2 (i : Fin n) : (-1 / delta i : ℝ) + 1 / delta i = 0 := by
    rw [neg_div, neg_add_cancel]
  have hs3 (i : Fin n) :
      (-1 / delta i) * -(c i 0) + (1 / delta i) * -(c i 1) = 1 := by
    calc
      _ = (c i 0 - c i 1) / delta i := by
        ring
      _ = 1 := div_self (hd i)
  have hm0 (V : Type) [AddCommGroup V] [Module ℝ V] (w : V) (i : Fin n) :
      (-(c i 1) / delta i) • w + (c i 0 / delta i) • w = w := by
    rw [← add_smul, hs0 i, one_smul]
  have hm1 (V : Type) [AddCommGroup V] [Module ℝ V] (w : V) (i : Fin n) :
      (-(c i 1) / delta i) • (-(c i 0) • w) +
        (c i 0 / delta i) • (-(c i 1) • w) = 0 := by
    rw [smul_smul, smul_smul, ← add_smul, hs1 i, zero_smul]
  have hm2 (V : Type) [AddCommGroup V] [Module ℝ V] (w : V) (i : Fin n) :
      (-1 / delta i) • w + (1 / delta i) • w = 0 := by
    rw [← add_smul, hs2 i, zero_smul]
  have hm3 (V : Type) [AddCommGroup V] [Module ℝ V] (w : V) (i : Fin n) :
      (-1 / delta i) • (-(c i 0) • w) + (1 / delta i) • (-(c i 1) • w) = w := by
    rw [smul_smul, smul_smul, ← add_smul, hs3 i, one_smul]
  have hsepB (i : Fin n) (z : M) :
      (-(c i 1) / delta i) • C i 0 z + (c i 0 / delta i) • C i 1 z = (A i z, 0) := by
    exact Prod.ext (hm0 _ (A i z) i)
      (hm1 _ (chi i z • (v i z : EuclideanSpace ℝ (Fin N))) i)
  have hsepV (i : Fin n) (z : M) :
      (-1 / delta i) • C i 0 z + (1 / delta i) • C i 1 z =
        (0, chi i z • (v i z : EuclideanSpace ℝ (Fin N))) := by
    exact Prod.ext (hm2 _ (A i z) i)
      (hm3 _ (chi i z • (v i z : EuclideanSpace ℝ (Fin N))) i)
  let b (i : Fin n) := |c i 1 / delta i| + |c i 0 / delta i| + |1 / delta i|
  have hb0 (i : Fin n) : 0 ≤ b i := by dsimp only [b]; positivity
  have hsum0 : 0 ≤ ∑ i, b i := Finset.sum_nonneg fun i _ ↦ hb0 i
  have hbound : ∃ bound : ℝ, 0 < bound ∧ ∀ i,
      |c i 1 / delta i| ≤ bound ∧ |c i 0 / delta i| ≤ bound ∧ |1 / delta i| ≤ bound := by
    refine ⟨1 + ∑ i, b i, add_pos_of_pos_of_nonneg zero_lt_one hsum0, ?_⟩
    intro i
    have hi : b i ≤ ∑ j, b j := Finset.single_le_sum (fun j _ ↦ hb0 j) (Finset.mem_univ i)
    dsimp only [b] at hi
    have h0 := abs_nonneg (c i 1 / delta i)
    have h1 := abs_nonneg (c i 0 / delta i)
    have h2 := abs_nonneg (1 / delta i)
    have hlim : b i ≤ 1 + ∑ j, b j := hi.trans (le_add_of_nonneg_left zero_le_one)
    exact ⟨((le_add_of_nonneg_right h1).trans (le_add_of_nonneg_right h2)).trans hlim,
      ((le_add_of_nonneg_left h0).trans (le_add_of_nonneg_right h2)).trans hlim,
      (le_add_of_nonneg_left (add_nonneg h0 h1)).trans hlim⟩
  have hBkill : ∀ k : K, B k.val = 0 := fun k ↦ k.property
  refine ⟨xi, nu, U, psi, v, chi, hfields, hone, hzero, hcol, hglob, hsglob,
    hRdiff, hRonto, fun i ↦ ⟨hd i, hmatrix i⟩, hsepB, hsepV, hbound, ?_⟩
  -- Prove the algebra with all normed-module data as explicit parameters. The application
  -- below supplies the existing native K/L instances; no new norm or carrier is constructed.
  have hcore : ∀
      (K1 L1 : Type) [NormedAddCommGroup K1] [NormedSpace ℝ K1]
      [FiniteDimensional ℝ K1] [NormedAddCommGroup L1] [NormedSpace ℝ L1]
      [FiniteDimensional ℝ L1]
      (D : Fin n → K1 →L[ℝ] L1) (ell : Fin n → L1)
      (Rw1 : (Fin n → ℝ) → (K1 →L[ℝ] L1)),
      finrank ℝ K1 = n → finrank ℝ L1 = 1 →
      (∀ i, ell i = 0 → D i = 0) →
      (∀ t, Rw1 t = ∑ i, t i • D i) →
      Function.Surjective (fderiv ℝ Rw1 0) →
      let J (ij : Fin n × Fin 2) := (D ij.1, -(c ij.1 ij.2) • ell ij.1)
      Submodule.span ℝ (Set.range J) = ⊤ ∧
        finrank ℝ (Submodule.span ℝ (Set.range J)) = n + 1 := by
    intro K1 L1 instK instKS instKF instL instLS instLF D ell Rw1 hdK hdL hDkill hRform hRonto
    let T : (Fin n → ℝ) →L[ℝ] (K1 →L[ℝ] L1) :=
      LinearMap.toContinuousLinearMap (Fintype.linearCombination ℝ D)
    have hTt (t : Fin n → ℝ) : T.toLinearMap.toFun t = ∑ i, t i • D i :=
      Fintype.linearCombination_apply ℝ D t
    have hRfun : Rw1 = T.toLinearMap.toFun := funext fun t ↦ (hRform t).trans (hTt t).symm
    have hTonto : Function.Surjective T.toLinearMap.toFun := by
      have hf : fderiv ℝ Rw1 0 = T :=
        (congrArg (fun f : (Fin n → ℝ) → (K1 →L[ℝ] L1) ↦ fderiv ℝ f 0) hRfun).trans
          (ContinuousLinearMap.fderiv (𝕜 := ℝ) (E := Fin n → ℝ)
            (F := K1 →L[ℝ] L1) (x := (0 : Fin n → ℝ)) T)
      intro Y
      obtain ⟨t, ht⟩ := hRonto Y
      exact ⟨t, (DFunLike.congr_fun hf t).symm.trans ht⟩
    have hDspan : Submodule.span ℝ (Set.range D) = ⊤ :=
      (Fintype.range_linearCombination ℝ D).symm.trans (LinearMap.range_eq_top.mpr hTonto)
    have hdHom : finrank ℝ (K1 →L[ℝ] L1) = n := by
      calc
        _ = finrank ℝ (K1 →ₗ[ℝ] L1) :=
          (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := K1) (F' := L1)).finrank_eq.symm
        _ = finrank ℝ K1 * finrank ℝ L1 := Module.finrank_linearMap ℝ ℝ K1 L1
        _ = n := by rw [hdK, hdL, mul_one]
    have hell : ∃ i, ell i ≠ 0 := by
      by_contra h
      have hall : ∀ i, ell i = 0 := by simpa only [not_exists, not_not] using h
      have hDzero (i : Fin n) : D i = 0 := hDkill i (hall i)
      have hbot : Submodule.span ℝ (Set.range D) = ⊥ := by
        apply Submodule.span_eq_bot.mpr
        rintro _ ⟨i, rfl⟩
        exact hDzero i
      have heq : (⊤ : Submodule ℝ (K1 →L[ℝ] L1)) = ⊥ := hDspan.symm.trans hbot
      have hz := congrArg (fun S : Submodule ℝ (K1 →L[ℝ] L1) ↦ finrank ℝ S) heq
      rw [finrank_top, finrank_bot, hdHom] at hz
      exact (by omega : n ≠ 0) hz
    have hellspan : Submodule.span ℝ (Set.range ell) = ⊤ := by
      obtain ⟨i, hi⟩ := hell
      have hsingle : Submodule.span ℝ ({ell i} : Set L1) = ⊤ :=
        Submodule.eq_top_of_finrank_eq ((finrank_span_singleton hi).trans hdL.symm)
      apply top_unique
      rw [← hsingle]
      apply Submodule.span_mono
      intro v hv
      exact ⟨i, Set.mem_singleton_iff.mp hv |>.symm⟩
    let J (ij : Fin n × Fin 2) : (K1 →L[ℝ] L1) × L1 :=
      (D ij.1, -(c ij.1 ij.2) • ell ij.1)
    let Z := Submodule.span ℝ (Set.range J)
    have hZB (i : Fin n) : (D i, (0 : L1)) ∈ Z := by
      have he : (-(c i 1) / delta i) • J (i, 0) +
          (c i 0 / delta i) • J (i, 1) = (D i, 0) := by
        exact Prod.ext (hm0 _ (D i) i) (hm1 _ (ell i) i)
      rw [← he]
      exact Z.add_mem (Z.smul_mem _ (Submodule.subset_span ⟨(i, 0), rfl⟩))
        (Z.smul_mem _ (Submodule.subset_span ⟨(i, 1), rfl⟩))
    have hZV (i : Fin n) : ((0 : K1 →L[ℝ] L1), ell i) ∈ Z := by
      have he : (-1 / delta i) • J (i, 0) + (1 / delta i) • J (i, 1) = (0, ell i) := by
        exact Prod.ext (hm2 _ (D i) i) (hm3 _ (ell i) i)
      rw [← he]
      exact Z.add_mem (Z.smul_mem _ (Submodule.subset_span ⟨(i, 0), rfl⟩))
        (Z.smul_mem _ (Submodule.subset_span ⟨(i, 1), rfl⟩))
    have hleft : Submodule.span ℝ (Set.range D) ≤
        Z.comap (LinearMap.inl ℝ (K1 →L[ℝ] L1) L1) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hZB i
    have hright : Submodule.span ℝ (Set.range ell) ≤
        Z.comap (LinearMap.inr ℝ (K1 →L[ℝ] L1) L1) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hZV i
    have hZ : Z = ⊤ := by
      apply top_unique
      intro p hp
      have hB : (p.1, (0 : L1)) ∈ Z := hleft (by rw [hDspan]; trivial)
      have hV : ((0 : K1 →L[ℝ] L1), p.2) ∈ Z := hright (by rw [hellspan]; trivial)
      have he : (p.1, (0 : L1)) + ((0 : K1 →L[ℝ] L1), p.2) = p :=
        Prod.ext (add_zero p.1) (zero_add p.2)
      exact he ▸ Z.add_mem hB hV
    have hdimZ : finrank ℝ Z = n + 1 := by
      rw [hZ, finrank_top, Module.finrank_prod, hdHom, hdL]
    exact ⟨hZ, hdimZ⟩
  let ell (i : Fin n) : L := ⟨nu i, hnuL i⟩
  let PN : EuclideanSpace ℝ (Fin N) →L[ℝ] normalSpace (I := I) F x :=
    (normalSpace (I := I) F x).orthogonalProjectionOnto
  let PL : normalSpace (I := I) F x →L[ℝ] L := L.orthogonalProjectionOnto
  let Q : EuclideanSpace ℝ (Fin N) →L[ℝ] L := PL.comp PN
  let D (i : Fin n) : K →L[ℝ] L :=
    Q.comp ((LinearMap.toContinuousLinearMap
      (show SymmetricSquare (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin N) from A i x)).comp K.subtypeL)
  have hRform (t : Fin n → ℝ) : Rw t = ∑ i, t i • D i := by
    apply DFunLike.ext
    intro k
    have hk : B (k : SymmetricSquare (EuclideanSpace ℝ (Fin n))) = 0 := hBkill k
    change L.orthogonalProjectionOnto
      (B (k : SymmetricSquare (EuclideanSpace ℝ (Fin n))) +
        (normalSpace (I := I) F x).orthogonalProjectionOnto ((S t x) k.val)) = _
    have hkill : PL (B k.val + PN ((S t x) k.val)) = Q ((S t x) k.val) :=
      congrArg PL ((congrArg (fun w ↦ w + PN ((S t x) k.val)) hk).trans (zero_add _))
    apply hkill.trans
    have heval : (S t x) k.val = ∑ i, (t i • A i x) k.val := LinearMap.sum_apply _ _ _
    change Q ((S t x) k.val) = (∑ i, t i • D i) k
    calc
      Q ((S t x) k.val) = Q (∑ i, (t i • A i x) k.val) := congrArg Q heval
      _ = ∑ i, Q ((t i • A i x) k.val) := map_sum Q.toLinearMap _ _
      _ = ∑ i, t i • D i k := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (congrArg Q (LinearMap.smul_apply (t i) (A i x) k.val)).trans
          (Q.map_smul (t i) (A i x k.val))
      _ = (∑ i, t i • D i) k :=
        ((DFunLike.congr_fun
          (ContinuousLinearMap.toLinearMap_sum Finset.univ (fun i : Fin n ↦ t i • D i)) k).trans
            (LinearMap.sum_apply _ _ _)).symm
  have hDkill (i : Fin n) (hi : ell i = 0) : D i = 0 := by
    have hnuzero : nu i = 0 := congrArg Subtype.val hi
    have hvalzero : (nu i : EuclideanSpace ℝ (Fin N)) = 0 :=
      congrArg Subtype.val hnuzero
    have hvarzero : supportedRankLegalVariation (xi i).toLinearMap
        (nu i : EuclideanSpace ℝ (Fin N)) = 0 :=
      (congrArg (supportedRankLegalVariation (xi i).toLinearMap) hvalzero).trans
        (LinearMap.smulRight_zero _)
    have hAzero : A i x = 0 := (hcol i).trans hvarzero
    apply DFunLike.ext
    intro k
    exact (congrArg Q (DFunLike.congr_fun hAzero k.val)).trans Q.map_zero
  let Jn (ij : Fin n × Fin 2) : (K →L[ℝ] L) × L :=
    (D ij.1, -(c ij.1 ij.2) • ell ij.1)
  have hp : Submodule.span ℝ (Set.range Jn) = ⊤ ∧
      finrank ℝ (Submodule.span ℝ (Set.range Jn)) = n + 1 :=
    hcore K L D ell Rw hdK hdL hDkill hRform hRonto
  let Ja (ij : Fin n × Fin 2) : (K →L[ℝ] L) × L :=
    (L.orthogonalProjectionOnto.comp
      (((normalSpace (I := I) F x).orthogonalProjectionOnto.comp
        (LinearMap.toContinuousLinearMap
          (show SymmetricSquare (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ]
            EuclideanSpace ℝ (Fin N) from (C ij.1 ij.2 x).1))).comp K.subtypeL),
      L.orthogonalProjectionOnto
        ((normalSpace (I := I) F x).orthogonalProjectionOnto (C ij.1 ij.2 x).2))
  have hJvalue (i : Fin n) (j : Fin 2) : Q (C i j x).2 = -(c i j) • ell i := by
    have hvx : v i x = nu i := (hfields i).2.2.2.2.2.2.2.2.2.1
    have hv : chi i x • (v i x : EuclideanSpace ℝ (Fin N)) =
        (nu i : EuclideanSpace ℝ (Fin N)) :=
      (congrArg (fun a : ℝ ↦ a • (v i x : EuclideanSpace ℝ (Fin N))) (chi i).eq_one).trans
        ((one_smul ℝ (v i x : EuclideanSpace ℝ (Fin N))).trans (congrArg Subtype.val hvx))
    have hn : PN (nu i : EuclideanSpace ℝ (Fin N)) = nu i :=
      (normalSpace (I := I) F x).orthogonalProjectionOnto_mem_subspace_eq_self (nu i)
    have hl : PL (nu i) = ell i :=
      L.orthogonalProjectionOnto_mem_subspace_eq_self (ell i)
    have hq : Q (nu i : EuclideanSpace ℝ (Fin N)) = ell i := (congrArg PL hn).trans hl
    exact (Q.map_smul (-(c i j)) (chi i x • (v i x : EuclideanSpace ℝ (Fin N)))).trans
      (congrArg (fun w : L ↦ -(c i j) • w) ((congrArg Q hv).trans hq))
  have hJeq : Ja = Jn := by
    apply funext
    intro ij
    apply Prod.ext
    · rfl
    · exact hJvalue ij.1 ij.2
  have hspan : Submodule.span ℝ (Set.range Ja) = Submodule.span ℝ (Set.range Jn) :=
    congrArg (fun J : (Fin n × Fin 2) → (K →L[ℝ] L) × L ↦
      Submodule.span ℝ (Set.range J)) hJeq
  exact ⟨hspan.trans hp.1, (congrArg
    (fun S : Submodule ℝ ((K →L[ℝ] L) × L) ↦ finrank ℝ S) hspan).trans hp.2⟩

#print axioms upgradeRankQ_exists_duplicated_principal_packet

end GlobalEmbedding.Paper
