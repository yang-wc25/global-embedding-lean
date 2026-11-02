import Probes.ActualIncrementPrimaryPhysicalFamily
import Probes.ActualIncrementPrimarySourceJets

/-! Primitive actual primary data yield the complete physical residual budget
with all auxiliary-parameter derivatives. The finite error retains (tau/ell)^p,
the original first-row factor two, both genuine free-normal channels and the
same full reconstruction. No source or output residual estimate is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ, D)

theorem actual_primary_physical_error_weighted_jets
    (F : Ep → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F b))
    (chart : Ep → OpenPartialHomeomorph M D)
    (hchart : ∀ b, chart b ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O) (hOt : ∀ z ∈ O, z.2 ∈ (chart z.1).target)
    (hinj : ∀ z ∈ O, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ, V) (F z.1) ((chart z.1).symm z.2)))
    (hfree : ∀ z ∈ O,
      let β := incrementsTransversePairing (F z.1) (hF z.1) ((chart z.1).symm z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (chart z.1).symm z.2 a.succ)
      (β.comp β.adjoint).IsInvertible)
    (vfR vfI : (b : Ep) → (x : D) → normalSpace (I := 𝓙) (F b) ((chart b).symm x))
    (hvfR : ContDiffOn ℝ ∞ (fun z : X => (vfR z.1 z.2 : V)) O)
    (hvfI : ContDiffOn ℝ ∞ (fun z : X => (vfI z.1 z.2 : V)) O)
    (hkernelR : ∀ z ∈ O, incrementsTransversePairing (F z.1) (hF z.1) ((chart z.1).symm z.2)
      (fun a : Fin m => incrementsModeCoordinateDirections (chart z.1).symm z.2 a.succ) (vfR z.1 z.2) = 0)
    (hkernelI : ∀ z ∈ O, incrementsTransversePairing (F z.1) (hF z.1) ((chart z.1).symm z.2)
      (fun a : Fin m => incrementsModeCoordinateDirections (chart z.1).symm z.2 a.succ) (vfI z.1 z.2) = 0)
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (chart z.1).symm z.2 0 i : V)) O)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (chart z.1).symm z.2) O)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (chart z.1).symm z.2) O)
    (n length : ℕ) (tau ell Mg KR KI a : ℝ) (htau : 0 < tau) (hell : 0 < ell)
    (hell1 : ell ≤ 1) (hMg : 0 ≤ Mg) (hKR : 0 ≤ KR) (hKI : 0 ≤ KI) (ha : 0 ≤ a)
    (hBRb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
      (fun w : X => fun i : Fin (m+1) =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (chart w.1).symm w.2 0 i : V)) z‖ ≤ Mg)
    (hAb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
      (fun w : X => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (chart w.1).symm w.2) z‖ ≤ Mg)
    (hBb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
      (fun w : X => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (chart w.1).symm w.2) z‖ ≤ Mg)
    (hvfRb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
      (fun w : X => (vfR w.1 w.2 : V)) z‖ ≤ KR*a)
    (hvfIb : ∀ r ≤ n, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
      (fun w : X => (vfI w.1 w.2 : V)) z‖ ≤ KI*a) :
    let c : Ep → D → M := fun b => (chart b).symm
    let k := fun z : X => actualHomogeneousSource F hF c vfR z +
      Complex.I • actualHomogeneousSource F hF c vfI z
    let alpha := (tau : ℂ)/Complex.I
    let U := fun b => incrementsActualModeSum
      (incrementsModeComplexFirstOrderA (F b) (hF b) (c b))
      (incrementsModeComplexFirstOrderB (F b) (hF b) (c b)) alpha length (fun x => k (b,x))
    let ZR := fun b => incrementsModeFullReconstruction (F b) (hF b) (c b)
      (fun x => incrementsModeRealPart (U b x)) (fun _ _ _ => 0) (vfR b)
    let ZI := fun b => incrementsModeFullReconstruction (F b) (hF b) (c b)
      (fun x => incrementsModeImagPart (U b x)) (fun _ _ _ => 0) (vfI b)
    let WR := fun b x => WithLp.toLp 2 (fun a : Fin N =>
      (Complex.exp (((x 0/tau : ℝ) : ℂ)*Complex.I)*
        ((ZR b x a : ℂ)+Complex.I*(ZI b x a : ℂ))).re)
    let WI := fun b x => WithLp.toLp 2 (fun a : Fin N =>
      (Complex.exp (((x 0/tau : ℝ) : ℂ)*Complex.I)*
        ((ZR b x a : ℂ)+Complex.I*(ZI b x a : ℂ))).im)
    let residual := fun z : X => alpha⁻¹ • U z.1 z.2 +
      incrementsModeComplexReducedOperator (F z.1) (hF z.1) (c z.1) (U z.1) z.2-k z
    let err := fun (z : X) i j => Complex.exp (-((z.2 0/tau : ℝ) : ℂ)*Complex.I)*
      ((incrementsCoordinateMetricVariation (F z.1 ∘ c z.1) (WR z.1) z.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ)+Complex.I*
        (incrementsCoordinateMetricVariation (F z.1 ∘ c z.1) (WI z.1) z.2
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ))
    let Ksource := homogeneousSourceConstant m N n Mg (KR+KI)*a
    let Kerr := (2*2^n*Mg)^length*(tau/ell)^length*Ksource
    ContDiffOn ℝ ∞ err O ∧ ∀ j, j+length ≤ n → ∀ z ∈ S,
      ell^j * ‖iteratedFDeriv ℝ j err z‖ ≤ 2*Kerr := by
  intro c k alpha U ZR ZI WR WI residual err Ksource Kerr
  obtain ⟨hk,hkb⟩ := actual_primary_two_channel_source_weighted_jets F hF c vfR vfI
    O S hO hSO hBR hvfR hvfI n ell Mg KR KI a hell.le hMg hKR hKI ha hBRb hvfRb hvfIb
  have hKsource : 0 ≤ Ksource :=
    mul_nonneg (homogeneousSourceConstant_nonneg m N n hMg (add_nonneg hKR hKI)) ha
  have hKerr : 0 ≤ Kerr := by dsimp only [Kerr]; positivity
  have hU : ContDiffOn ℝ ∞ (fun z : X => U z.1 z.2) O :=
    actual_joint_mode_sum_contDiffOn F hF c k tau length O hO hA hB hk
  have hres : ContDiffOn ℝ ∞ residual O :=
    actual_joint_reduced_residual_contDiffOn F hF c (fun z => U z.1 z.2) k O hO hA hB hU hk alpha
  have hb := actual_joint_finite_residual_scaled_jets F hF c k n length O S hO hSO
    hA hB hk tau ell Mg Ksource htau hell hell1 hMg hKsource hAb hBb hkb
  obtain ⟨he,herr⟩ := actual_primary_physical_error_eq_reduced F hF chart hchart O hO hOt hinj hfree
    vfR vfI hvfR hvfI hkernelR hkernelI hBR hA hB tau htau length
  refine ⟨herr,?_⟩
  intro j hj z hz
  have heq : err =ᶠ[𝓝 z] (fun w => actualModeResidualRows (residual w)) := by
    filter_upwards [hO.mem_nhds (hSO hz)] with w hw
    exact he hw
  rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
  exact (slow_linear_jet_bound actualModeResidualRows O hO residual hres j ell Kerr hell.le
    z (hSO hz) (hb j hj z hz)).trans
      (mul_le_mul_of_nonneg_right actualModeResidualRows_norm_le hKerr)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_primary_physical_error_weighted_jets
