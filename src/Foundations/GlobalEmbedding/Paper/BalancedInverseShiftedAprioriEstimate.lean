import GlobalEmbedding.External.CalabiYau.Analysis.Elliptic.Schauder.ConstantCoefficient.Estimate
import GlobalEmbedding.Paper.PeriodicCAlphaNormFromCalabiGauge
import GlobalEmbedding.Paper.PeriodicCAlphaJetMap
import GlobalEmbedding.Paper.PeriodicCAlphaEuclideanHolderBound
import GlobalEmbedding.Paper.PeriodicShiftedLaplacianMaximumPrinciple
import GlobalEmbedding.Paper.EuclideanCoordinateLaplacian

/-!
# The actual periodic shifted Schauder estimate in the original Hölder norm

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
lines 382–386. DAG node: `balanced-inverse-shifted-apriori-estimate`.

The genuine constant-coefficient estimate is reused from the W2 port of wxkj99/calabi-yau,
commit 91b1ddf000c7028bc42ae6102eba0e2042eb37ff. Its explicit constants are scaled here;
its original source and licenses are preserved with that port. No inverse is assumed.
-/

open scoped Topology ContDiff NNReal Laplacian
open Set WithLp HeatEquation CalabiYau.Schauder

namespace GlobalEmbedding.Paper

private theorem firstJetBound {a N : ℕ} {α : ℝ}
    (u : PeriodicCAlphaFunction a N 2 α) (x : EuclideanSpace ℝ (Fin a)) :
    ‖fderiv ℝ u.toFun x‖ ≤ ‖u‖ := by
  rw [← norm_iteratedFDeriv_one u.toFun]
  exact periodicCAlpha_global_jet_bound u 1 (by norm_num) x

private theorem secondJetBound {a N : ℕ} {α : ℝ}
    (u : PeriodicCAlphaFunction a N 2 α) (x : EuclideanSpace ℝ (Fin a)) :
    ‖fderiv ℝ (fderiv ℝ u.toFun) x‖ ≤ ‖u‖ := by
  rw [← norm_iteratedFDeriv_one (fderiv ℝ u.toFun), norm_iteratedFDeriv_fderiv]
  exact periodicCAlpha_global_jet_bound u 2 le_rfl x

private noncomputable def valueBCF {a N : ℕ} {α : ℝ}
    (u : PeriodicCAlphaFunction a N 2 α) :
    BoundedContinuousFunction (EuclideanSpace ℝ (Fin a)) (EuclideanSpace ℝ (Fin N)) :=
  .ofNormedAddCommGroup u.toFun u.contDiff.continuous ‖u‖ (periodicCAlpha_value_bound u)

private noncomputable def firstBCF {a N : ℕ} {α : ℝ}
    (u : PeriodicCAlphaFunction a N 2 α) :
    BoundedContinuousFunction (EuclideanSpace ℝ (Fin a))
      (EuclideanSpace ℝ (Fin a) →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  .ofNormedAddCommGroup (fderiv ℝ u.toFun)
    (u.contDiff.continuous_fderiv (by norm_num)) ‖u‖ (firstJetBound u)

private noncomputable def secondBCF {a N : ℕ} {α : ℝ}
    (u : PeriodicCAlphaFunction a N 2 α) :
    BoundedContinuousFunction (EuclideanSpace ℝ (Fin a))
      (EuclideanSpace ℝ (Fin a) →L[ℝ]
        EuclideanSpace ℝ (Fin a) →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  .ofNormedAddCommGroup (fderiv ℝ (fderiv ℝ u.toFun))
    ((u.contDiff.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num))
    ‖u‖ (secondJetBound u)

private theorem bcfJet_hasDerivatives {a N : ℕ} {α : ℝ}
    (u : PeriodicCAlphaFunction a N 2 α) :
    (∀ x, HasFDerivAt (valueBCF u : _ → _) (firstBCF u x) x) ∧
      (∀ x, HasFDerivAt (firstBCF u : _ → _) (secondBCF u x) x) := by
  constructor
  · intro x
    exact (u.contDiff.differentiable (by norm_num) x).hasFDerivAt
  · intro x
    exact ((u.contDiff.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) x).hasFDerivAt

private theorem bcfCoreLap_eq_native {a N : ℕ} {α : ℝ}
    (u : PeriodicCAlphaFunction a N 2 α) (x : EuclideanSpace ℝ (Fin a)) :
    coreLap (secondBCF u) x = Laplacian.laplacian u.toFun x := by
  rw [coreLap_apply, InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply Finset.sum_congr rfl
  intro i _
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

section Constants

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] [Nontrivial V] in
private theorem toNNReal_coeff_norm (c : ℝ) (u : BoundedContinuousFunction V F) :
    Real.toNNReal (c * ‖u‖) = ‖u‖₊ * Real.toNNReal c := by
  rw [mul_comm, Real.toNNReal_mul (norm_nonneg u)]
  congr 1
  exact norm_toNNReal

private theorem heatSpatial_norm_hom (t : ℝ) (u : BoundedContinuousFunction V F) (j : ℕ) :
    heatSupSpatialJetConst t u j = ‖u‖₊ * heatSupSpatialJetConst t
      (BoundedContinuousFunction.const V (1 : ℝ)) j := by
  cases j with
  | zero =>
    change ‖u‖₊ = ‖u‖₊ * ‖BoundedContinuousFunction.const V (1 : ℝ)‖₊
    rw [BoundedContinuousFunction.nnnorm_const_eq, nnnorm_one, mul_one]
  | succ j =>
    cases j with
    | zero =>
      change Real.toNNReal ((heatScale t)⁻¹ * heatC1 V * ‖u‖) =
        ‖u‖₊ * Real.toNNReal ((heatScale t)⁻¹ * heatC1 V *
          ‖BoundedContinuousFunction.const V (1 : ℝ)‖)
      rw [BoundedContinuousFunction.norm_const_eq, norm_one, mul_one]
      exact toNNReal_coeff_norm _ u
    | succ j =>
      change Real.toNNReal (t⁻¹ * heatC2 V * ‖u‖) =
        ‖u‖₊ * Real.toNNReal (t⁻¹ * heatC2 V *
          ‖BoundedContinuousFunction.const V (1 : ℝ)‖)
      rw [BoundedContinuousFunction.norm_const_eq, norm_one, mul_one]
      exact toNNReal_coeff_norm _ u

private theorem heatD2Holder_norm_hom (t : ℝ) (u : BoundedContinuousFunction V F) :
    heatD2SupHolderConst t u = ‖u‖₊ * heatD2SupHolderConst t
      (BoundedContinuousFunction.const V (1 : ℝ)) := by
  unfold heatD2SupHolderConst
  have hc : ‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V =
      (t⁻¹ * (heatScale t)⁻¹ * heatC3 V) * ‖u‖ := by ring
  rw [hc, toNNReal_coeff_norm, toNNReal_coeff_norm]
  simp only [BoundedContinuousFunction.norm_const_eq, norm_one, mul_one, one_mul]
  rw [show 2 * (‖u‖₊ * Real.toNNReal (t⁻¹ * heatC2 V)) =
      ‖u‖₊ * (2 * Real.toNNReal (t⁻¹ * heatC2 V)) by ring]
  exact (mul_max _ _ _).symm

private theorem heatSup_norm_hom (t : ℝ) (u : BoundedContinuousFunction V F) :
    heatSupSchauderConst t u = ‖u‖₊ * heatSupSchauderConst t
      (BoundedContinuousFunction.const V (1 : ℝ)) := by
  unfold heatSupSchauderConst heatSupHessianHolderConst
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact heatSpatial_norm_hom t u j
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β _
    exact heatD2Holder_norm_hom t u

end Constants

private theorem nativeLap_eq_trace {a : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : EuclideanSpace ℝ (Fin a) → F) (x : EuclideanSpace ℝ (Fin a)) :
    Laplacian.laplacian u x = ∑ i : Fin a,
      iteratedFDeriv ℝ 2 u x (fun _ ↦ EuclideanSpace.single i 1) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
    (EuclideanSpace.basisFun (Fin a) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ext j
  fin_cases j <;> simp [EuclideanSpace.basisFun_apply]

private theorem shifted_low_bounds {a N : ℕ} {α : ℝ≥0}
    (u : PeriodicCAlphaFunction a N 2 (α : ℝ))
    (f : PeriodicCAlphaFunction a N 0 (α : ℝ))
    (hPDE : ∀ x, Laplacian.laplacian u.toFun x - u.toFun x = f.toFun x) :
    (∀ x, ‖u.toFun x‖ ≤ ‖f‖) ∧ HolderWith ‖f‖₊ α u.toFun := by
  have htrace : ∀ x, (∑ i : Fin a, iteratedFDeriv ℝ 2 u.toFun x
      (fun _ ↦ EuclideanSpace.single i 1)) - u.toFun x = f.toFun x := by
    intro x
    rw [← nativeLap_eq_trace]
    exact hPDE x
  exact ⟨periodic_shifted_laplacian_norm_bound (norm_nonneg f) u.contDiff u.periodic htrace
      (periodicCAlpha_value_bound f),
    periodic_shifted_laplacian_holder_contraction u.contDiff u.periodic htrace
      (periodicCAlpha_holderWith_norm f)⟩

private theorem holder_add_same {X F : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup F] {g h : X → F} {K α : ℝ≥0}
    (hg : HolderWith K α g) (hh : HolderWith K α h) : HolderWith (2 * K) α (g + h) := by
  intro x y
  rw [edist_nndist, edist_nndist,
    ← ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  have hd : dist ((g + h) x) ((g + h) y) ≤ (2 * (K : ℝ)) * dist x y ^ (α : ℝ) := by
    simp only [dist_eq_norm, Pi.add_apply]
    rw [show g x + h x - (g y + h y) = (g x - g y) + (h x - h y) by abel]
    have hg' := hg.dist_le x y
    have hh' := hh.dist_le x y
    rw [dist_eq_norm] at hg' hh'
    exact (norm_add_le _ _).trans (by linarith)
  exact_mod_cast hd

private theorem shifted_gauge_bound {a N : ℕ} [Nonempty (Fin a)] {α : ℝ≥0}
    (hα0 : 0 < α) (hα1 : α < 1)
    (u : PeriodicCAlphaFunction a N 2 (α : ℝ))
    (f : PeriodicCAlphaFunction a N 0 (α : ℝ))
    (hPDE : ∀ x, Laplacian.laplacian u.toFun x - u.toFun x = f.toFun x) :
    eContDiffHolderGaugeOn 2 α univ u.toFun ≤
      (‖f‖₊ * (heatSupSchauderConst (V := EuclideanSpace ℝ (Fin a)) 1
        (BoundedContinuousFunction.const (EuclideanSpace ℝ (Fin a)) (1 : ℝ)) +
        heatDuhamelConstSchauderConst (V := EuclideanSpace ℝ (Fin a)) α 2 2 1) : ℝ≥0) := by
  let s := ‖f‖₊
  obtain ⟨husup, huh⟩ := shifted_low_bounds u f hPDE
  have hcore : (coreLap (secondBCF u) : _ → _) = f.toFun + u.toFun := by
    funext x
    rw [bcfCoreLap_eq_native]
    exact sub_eq_iff_eq_add.mp (hPDE x)
  have hB : ‖coreLap (secondBCF u)‖ ≤ (2 * s : ℝ≥0) := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    change ‖(coreLap (secondBCF u) : _ → _) x‖ ≤ _
    rw [hcore]
    change ‖f.toFun x + u.toFun x‖ ≤ 2 * ‖f‖
    have hfval : ‖f.toFun x‖ ≤ ‖f‖ := periodicCAlpha_value_bound f x
    exact (norm_add_le _ _).trans (by linarith [hfval, husup x])
  have hH : HolderWith (2 * s) α (coreLap (secondBCF u) : _ → _) := by
    rw [hcore]
    exact holder_add_same (periodicCAlpha_holderWith_norm f) huh
  have hS := laplacian_schauder_estimate hα0 hα1 (valueBCF u) (firstBCF u) (secondBCF u)
    (bcfJet_hasDerivatives u).1 (bcfJet_hasDerivatives u).2 hB hH
  have hUnorm : ‖valueBCF u‖ ≤ ‖f‖ :=
    (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr husup
  have hU : ‖valueBCF u‖₊ ≤ s := by exact_mod_cast hUnorm
  have hconst : laplacianSchauderConst α (2 * s) (2 * s) (valueBCF u) ≤
      s * (heatSupSchauderConst (V := EuclideanSpace ℝ (Fin a)) 1
        (BoundedContinuousFunction.const (EuclideanSpace ℝ (Fin a)) (1 : ℝ)) +
        heatDuhamelConstSchauderConst (V := EuclideanSpace ℝ (Fin a)) α 2 2 1) := by
    unfold laplacianSchauderConst
    rw [heatSup_norm_hom, show 2 * s = s * 2 by ring,
      heatDuhamelConstSchauderConst_nnreal_mul, mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_right hU (by positivity)) le_rfl
  exact hS.trans (ENNReal.coe_le_coe.mpr hconst)

/-- Every actual period-one solution of Δu−u=f satisfies the shifted Schauder estimate
in the original periodic flat-torus Hölder norms. The constant is chosen before u and f;
all spatial and target dimensions, including zero, are included, and only actual C²
regularity is needed.

Proof: the original forcing norm controls its actual Euclidean Hölder constant. The
proved periodic maximum principle and its translated-difference version then bound both
the supremum and Hölder constant of u by those of f. Construct actual bounded continuous
u, Du and D²u from the original carrier, identify the provider's core Laplacian with the
native Laplacian, and apply its genuine constant-coefficient Schauder estimate to Δu=f+u.
The actual forcing bounds give both provider inputs at most twice the original forcing
norm. Explicit homogeneity of the heat and Duhamel constants gives a fixed dimension-
and exponent-dependent bound on the provider gauge. The proved gauge-to-original-norm
bridge multiplies it by four. For spatial dimension zero, u is constant, its positive
jets vanish, and the same original-norm bridge applies directly with constant four.
Source: `lem:balanced`, proof lines 382–386; genuine CalabiYau constant-coefficient estimate.
-/
theorem periodicCAlpha_shifted_apriori_estimate {a N : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : PeriodicCAlphaFunction a N 2 α) (f : PeriodicCAlphaFunction a N 0 α),
        (∀ x, (∑ i : Fin a, fderiv ℝ
          (fun y ↦ fderiv ℝ u.toFun y (EuclideanSpace.basisFun (Fin a) ℝ i)) x
          (EuclideanSpace.basisFun (Fin a) ℝ i)) - u.toFun x = f.toFun x) →
        ‖u‖ ≤ C * ‖f‖ := by
  let β : ℝ≥0 := ⟨α, hα0.le⟩
  have hβ0 : 0 < β := hα0
  have hβ1 : β < 1 := hα1
  cases a with
  | zero =>
    refine ⟨4, by norm_num, ?_⟩
    intro u f hPDE
    have hn : ∀ x, Laplacian.laplacian u.toFun x - u.toFun x = f.toFun x := by
      intro x
      rw [euclidean_laplacian_eq_coordinate_second u.toFun u.contDiff]
      exact hPDE x
    have hbound := (shifted_low_bounds (α := β) u f hn).1
    have hc : u.toFun = fun _ ↦ u.toFun 0 :=
      funext fun x ↦ congrArg u.toFun (Subsingleton.elim x 0)
    have hjets : ∀ j ≤ 2, ∀ x, ‖iteratedFDeriv ℝ j u.toFun x‖ ≤ ‖f‖ := by
      intro j hj x
      by_cases hj0 : j = 0
      · subst j
        rw [norm_iteratedFDeriv_zero]
        exact hbound x
      · rw [hc, iteratedFDeriv_const_of_ne hj0]
        rw [Pi.zero_apply, norm_zero]
        exact norm_nonneg f
    have htop : HolderWith ‖f‖₊ β (iteratedFDeriv ℝ 2 u.toFun) := by
      have hz : iteratedFDeriv ℝ 2 u.toFun = 0 := by
        funext x
        rw [hc, iteratedFDeriv_const_of_ne two_ne_zero]
      rw [hz]
      exact HolderWith.zero
    exact periodicCAlphaNorm_le_of_euclidean_holder (α := β) (C := ‖f‖₊) u hjets htop
  | succ a =>
    let H : ℝ≥0 :=
      heatSupSchauderConst (V := EuclideanSpace ℝ (Fin (a + 1))) 1
        (BoundedContinuousFunction.const (EuclideanSpace ℝ (Fin (a + 1))) (1 : ℝ)) +
      heatDuhamelConstSchauderConst (V := EuclideanSpace ℝ (Fin (a + 1))) β 2 2 1
    refine ⟨4 * (H : ℝ), by positivity, ?_⟩
    intro u f hPDE
    have hn : ∀ x, Laplacian.laplacian u.toFun x - u.toFun x = f.toFun x := by
      intro x
      rw [euclidean_laplacian_eq_coordinate_second u.toFun u.contDiff]
      exact hPDE x
    have hg := shifted_gauge_bound hβ0 hβ1 u f hn
    have hnorm := periodicCAlphaNorm_le_of_calabi_gauge
      (α := β) (C := ‖f‖₊ * H) u hg
    calc
      ‖u‖ ≤ (2 + 2 : ℕ) * ((‖f‖₊ * H : ℝ≥0) : ℝ) := hnorm
      _ = 4 * (H : ℝ) * ‖f‖ := by
        simp only [NNReal.coe_mul, coe_nnnorm]
        ring

#print axioms periodicCAlpha_shifted_apriori_estimate

end GlobalEmbedding.Paper
