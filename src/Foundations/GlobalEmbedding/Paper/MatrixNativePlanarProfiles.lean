import GlobalEmbedding.Paper.PlanarHopfCurvature
import GlobalEmbedding.Paper.MatrixAngleAnsatz
import GlobalEmbedding.Paper.MatrixNativeOscillatoryAverage
import GlobalEmbedding.Paper.MatrixPlanarProfileIndependence
import GlobalEmbedding.Paper.MatrixAnalyticPlanarCurvatureNull
import GlobalEmbedding.Paper.MatrixWeightedPeriodGramPositive
import Mathlib.Analysis.Analytic.Linear

/-!
# Actual Hopf planar profiles for the matrix moment construction

Source: `literature/parallelizable-stable-plus-one/main.tex`, prop:matrix, lines291–307.
DAG: `matrix-planar-orbit-independence`.
The actual orbit derivative and curvature of the accepted native Hopf flow are used
throughout. The historical scalar profile proofs are consumed without modification.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace GlobalEmbedding.Paper

/-- The first actual velocity coordinate in the original matrix proof. -/
def matrixPlanarS {C : ℕ} (f : PlanarHopfSphere C → Planar) (z : PlanarHopfSphere C) : ℝ :=
  orbitDeriv planarHopfFlow f z 0

/-- The actual oscillatory phase, the second actual velocity coordinate. -/
def matrixPlanarT {C : ℕ} (f : PlanarHopfSphere C → Planar) (z : PlanarHopfSphere C) : ℝ :=
  orbitDeriv planarHopfFlow f z 1

/-- The actual scalar inner product of position with the quarter-turned velocity. -/
abbrev matrixPlanarB {C : ℕ} (f : PlanarHopfSphere C → Planar) :=
  matrixAngleNormalPosition f

/-- The actual original flat curvature weight. -/
abbrev matrixPlanarRho {C : ℕ} (f : PlanarHopfSphere C → Planar) :=
  matrixAngleCutoff (planarOrbitCurvature planarHopfFlow f)

/-- The canonical position/tangent inner product has the literal source coordinates. -/
theorem matrixPlanarB_coordinates {C : ℕ} (f : PlanarHopfSphere C → Planar)
    (z : PlanarHopfSphere C) :
    matrixPlanarB f z = -f z 0 * matrixPlanarT f z + f z 1 * matrixPlanarS f z := by
  simp [matrixPlanarB, matrixAngleNormalPosition, matrixPlanarS, matrixPlanarT,
    planarQuarterTurn, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  ring

/-- The four actual scalar data used by the matrix proof are native smooth.

Proof: accepted native differentiation along the actual smooth Hopf action preserves
smoothness. Coordinate projections, scalar products and the actual smooth flat cutoff
preserve it again. Source: prop:matrix, actual s,t,b and rho0, lines291–300. -/
theorem matrix_planar_data_contMDiff {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (matrixPlanarS f) ∧
      ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (matrixPlanarT f) ∧
      ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (matrixPlanarB f) ∧
      ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (matrixPlanarRho f) := by
  have hv := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf
  have ha := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) _ hv
  have hs := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).contMDiff.comp hv
  have ht := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).contMDiff.comp hv
  have hf0 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).contMDiff.comp hf
  have hf1 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).contMDiff.comp hf
  refine ⟨hs, ht, ?_, ?_⟩
  · have he : matrixPlanarB f = fun z ↦
        -f z 0 * matrixPlanarT f z + f z 1 * matrixPlanarS f z :=
        funext (matrixPlanarB_coordinates f)
    rw [he]
    exact (hf0.neg.mul ht).add (hf1.mul hs)
  · exact expNegInvGlue.contDiff.contMDiff.comp
      ((planarOrbitCurvature_contMDiff planarHopfFlow f hv ha).pow 2)

/-- The actual Hopf velocity profiles are nonconstant analytic, the actual two weighted
Gram profile pairs are independent, and the actual curvature cutoff is positive a.e.

Proof: actual coordinate HasDerivAt identifies each scalar profile derivative with the
actual native orbit derivative. Unit Euclidean speed gives the scalar unit identity.
The accepted closed-profile independence and period-independence proofs then apply.
Actual orbit analyticity passes through coordinate projections and derivatives. The
accepted analytic curvature-null proof and the actual native curvature identity give
finite curvature zeros and positive actual cutoff almost everywhere. Source: prop:matrix,
profile independence and positive weighted blocks, lines291–307. -/
theorem matrix_native_planar_profile_properties {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hunit : ∀ z, ‖orbitDeriv planarHopfFlow f z‖ = 1)
    (hana : ∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ f (planarHopfFlow t z)) univ)
    (z : PlanarHopfSphere C) :
    (∃ x y : ℝ, matrixPlanarS f (planarHopfFlow x z) ≠
      matrixPlanarS f (planarHopfFlow y z)) ∧
    (∃ x y : ℝ, matrixPlanarT f (planarHopfFlow x z) ≠
      matrixPlanarT f (planarHopfFlow y z)) ∧
    AnalyticOnNhd ℝ (fun t : ℝ ↦ matrixPlanarT f (planarHopfFlow t z)) univ ∧
    LinearIndependent ℝ ![(fun _ : Icc (0 : ℝ) 1 ↦ (1 : ℝ)),
      (fun t : Icc (0 : ℝ) 1 ↦ matrixPlanarS f (planarHopfFlow t.val z))] ∧
    LinearIndependent ℝ ![(fun t : Icc (0 : ℝ) 1 ↦
        matrixPlanarT f (planarHopfFlow t.val z)),
      (fun t : Icc (0 : ℝ) 1 ↦ matrixPlanarB f (planarHopfFlow t.val z))] ∧
    {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
      planarOrbitCurvature planarHopfFlow f (planarHopfFlow t z) = 0}.Finite ∧
    (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      0 < matrixPlanarRho f (planarHopfFlow t z)) := by
  have hdiff (w : PlanarHopfSphere C) :
      Differentiable ℝ (fun t : ℝ ↦ f (planarHopfFlow t w)) :=
    fun t ↦ (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add f hf t w).differentiableAt
  have hv := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf
  have hvdiff (w : PlanarHopfSphere C) :
      Differentiable ℝ (fun t : ℝ ↦ orbitDeriv planarHopfFlow f (planarHopfFlow t w)) :=
    fun t ↦ (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add _ hv t w).differentiableAt
  have hd (i : Fin 2) (t : ℝ) : deriv (fun r : ℝ ↦ f (planarHopfFlow r z) i) t =
      orbitDeriv planarHopfFlow f (planarHopfFlow t z) i :=
    (planarOrbitCoordinate_hasDerivAt planarHopfFlow planarHopfFlow_add f hdiff z t i).deriv
  have hc (i : Fin 2) : AnalyticOnNhd ℝ (fun t : ℝ ↦ f (planarHopfFlow t z) i) univ := by
    intro t ht
    exact ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) i).analyticAt _).comp (hana z t ht)
  have hu (t : ℝ) : deriv (fun r : ℝ ↦ f (planarHopfFlow r z) 0) t ^ 2 +
      deriv (fun r : ℝ ↦ f (planarHopfFlow r z) 1) t ^ 2 = 1 := by
    rw [hd, hd]
    have he := congrArg (fun r : ℝ ↦ r ^ 2) (hunit (planarHopfFlow t z))
    simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, one_pow] using he
  have hp (i : Fin 2) := orbitMap_periodic planarHopfFlow planarHopfFlow_add
    planarHopfFlow_one (fun w ↦ f w i) z
  have hi := planar_profile_independence _ _
    (fun t ↦ (hc 0 t (mem_univ _)).differentiableAt)
    (fun t ↦ (hc 1 t (mem_univ _)).differentiableAt) (hp 0) (hp 1) hu
  have hj := planar_profile_period_independence _ _
    (fun t ↦ (hc 0 t (mem_univ _)).differentiableAt)
    (fun t ↦ (hc 1 t (mem_univ _)).differentiableAt) (hp 0) (hp 1) hu
  have hk := analytic_planar_curvature_null _ _ (hc 0) (hc 1) (hp 0) (hp 1) hu 0 1
  have hkeq (t : ℝ) :
      deriv (fun r : ℝ ↦ f (planarHopfFlow r z) 0) t *
        deriv (deriv (fun r : ℝ ↦ f (planarHopfFlow r z) 1)) t -
      deriv (fun r : ℝ ↦ f (planarHopfFlow r z) 1) t *
        deriv (deriv (fun r : ℝ ↦ f (planarHopfFlow r z) 0)) t =
        planarOrbitCurvature planarHopfFlow f (planarHopfFlow t z) :=
    planarOrbitCurvature_on_orbit planarHopfFlow planarHopfFlow_add f hdiff hvdiff z t
  simp_rw [hd] at hi hj
  simp_rw [hkeq] at hk
  simp only [matrixPlanarB_coordinates, matrixPlanarS, matrixPlanarT]
  refine ⟨hi.1, hi.2.1, ?_, hj.1, hj.2, hk.1, hk.2⟩
  have he : (fun t : ℝ ↦ matrixPlanarT f (planarHopfFlow t z)) =
      deriv (fun t : ℝ ↦ f (planarHopfFlow t z) 1) := by
    funext t
    exact (hd 1 t).symm
  change AnalyticOnNhd ℝ (fun t ↦ matrixPlanarT f (planarHopfFlow t z)) univ
  rw [he]
  exact (hc 1).deriv

/-- The two literal weighted Gram blocks of the actual Hopf selector are positive definite.

Proof: the actual native scalar functions restrict continuously to each actual orbit.
The preceding actual profile theorem supplies both genuine period function independence
and positivity a.e. of the actual curvature weight. Apply the accepted weighted-period
Gram theorem to the two actual pairs. Source: prop:matrix, positive blocks, line307. -/
theorem matrix_native_weighted_gram_blocks {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hunit : ∀ z, ‖orbitDeriv planarHopfFlow f z‖ = 1)
    (hana : ∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ f (planarHopfFlow t z)) univ)
    (z : PlanarHopfSphere C) :
    Matrix.PosDef (fun i j : Fin 2 ↦ ∫ t in Icc (0 : ℝ) 1,
      matrixPlanarRho f (planarHopfFlow t z) *
        ![1, matrixPlanarS f (planarHopfFlow t z)] i *
        ![1, matrixPlanarS f (planarHopfFlow t z)] j) ∧
    Matrix.PosDef (fun i j : Fin 2 ↦ ∫ t in Icc (0 : ℝ) 1,
      matrixPlanarRho f (planarHopfFlow t z) *
        ![matrixPlanarT f (planarHopfFlow t z), matrixPlanarB f (planarHopfFlow t z)] i *
        ![matrixPlanarT f (planarHopfFlow t z), matrixPlanarB f (planarHopfFlow t z)] j) := by
  have hp := matrix_native_planar_profile_properties f hf hunit hana z
  obtain ⟨hs, ht, hb, hr⟩ := matrix_planar_data_contMDiff f hf
  have hflow : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
    ((planarHopfFlow_contMDiff C).comp (contMDiff_id.prodMk contMDiff_const)).continuous
  have hρ : Continuous (fun t : ℝ ↦ matrixPlanarRho f (planarHopfFlow t z)) :=
    hr.continuous.comp hflow
  have hn (t : ℝ) : 0 ≤ matrixPlanarRho f (planarHopfFlow t z) :=
    expNegInvGlue.nonneg _
  constructor
  · refine weighted_period_gram_positive
      (fun i t ↦ ![1, matrixPlanarS f (planarHopfFlow t z)] i) ?_
      (fun t ↦ matrixPlanarRho f (planarHopfFlow t z)) hρ hn hp.2.2.2.2.2.2 ?_
    · intro i
      fin_cases i
      · exact continuous_const
      · exact hs.continuous.comp hflow
    · convert hp.2.2.2.1 using 1
      funext i
      fin_cases i <;> rfl
  · refine weighted_period_gram_positive
      (fun i t ↦ ![matrixPlanarT f (planarHopfFlow t z),
        matrixPlanarB f (planarHopfFlow t z)] i) ?_
      (fun t ↦ matrixPlanarRho f (planarHopfFlow t z)) hρ hn hp.2.2.2.2.2.2 ?_
    · intro i
      fin_cases i
      · exact ht.continuous.comp hflow
      · exact hb.continuous.comp hflow
    · convert hp.2.2.2.2.1 using 1
      funext i
      fin_cases i <;> rfl

/-- Every actual smooth scalar amplitude has uniform oscillatory orbit-average decay
for the actual Hopf phase t=(Xf)1, with any fixed real phase shift.

Proof: the actual smooth native Hopf action makes the phase and amplitude jointly smooth.
Period one is the actual action period. The native profile theorem derives analyticity and
nonconstancy from the actual unit planar map. Apply the accepted compact-native theorem;
the ordinary interval integral equals its Icc version because endpoints are null.
Source: prop:matrix, uniform oscillatory averages, line293. -/
theorem matrix_hopf_uniform_oscillatory_average {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hunit : ∀ z, ‖orbitDeriv planarHopfFlow f z‖ = 1)
    (hana : ∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ f (planarHopfFlow t z)) univ)
    (a : PlanarHopfSphere C → ℝ)
    (ha : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ a) (phase : ℝ) :
    TendstoUniformly
      (fun T : ℝ ↦ orbitAverage planarHopfFlow
        (fun z ↦ a z * Real.cos (T * matrixPlanarT f z + phase)))
      (fun _ : PlanarHopfSphere C ↦ (0 : ℝ)) atTop := by
  have ht := (matrix_planar_data_contMDiff f hf).2.1
  have hflow : ContMDiff ((planarHopfModel C).prod 𝓘(ℝ, ℝ)) (planarHopfModel C) ∞
      (fun p : PlanarHopfSphere C × ℝ ↦ planarHopfFlow p.2 p.1) :=
    (planarHopfFlow_contMDiff C).comp (contMDiff_snd.prodMk contMDiff_fst)
  have hp (z : PlanarHopfSphere C) := matrix_native_planar_profile_properties f hf hunit hana z
  have h := native_uniform_oscillatory_cos_average
    (fun p : PlanarHopfSphere C × ℝ ↦ matrixPlanarT f (planarHopfFlow p.2 p.1))
    (fun p : PlanarHopfSphere C × ℝ ↦ a (planarHopfFlow p.2 p.1))
    (ht.comp hflow) (ha.comp hflow)
    (fun z ↦ orbitMap_periodic planarHopfFlow planarHopfFlow_add planarHopfFlow_one _ z)
    (fun z ↦ orbitMap_periodic planarHopfFlow planarHopfFlow_add planarHopfFlow_one a z)
    (fun z ↦ (hp z).2.2.1) (fun z ↦ (hp z).2.1) phase
  change TendstoUniformly (fun T z ↦ ∫ t in (0 : ℝ)..1,
    a (planarHopfFlow t z) * Real.cos (T * matrixPlanarT f (planarHopfFlow t z) + phase))
    (fun _ ↦ 0) atTop
  simpa only [intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc] using h

#print axioms matrix_planar_data_contMDiff
#print axioms matrix_native_planar_profile_properties
#print axioms matrix_native_weighted_gram_blocks
#print axioms matrix_hopf_uniform_oscillatory_average

end GlobalEmbedding.Paper
