import Probes.ActualUniformRawAnalyticCosts
import Probes.ActualRestrictedRawConclusion
import Smoothing.ParameterRound2MeanGermResidualMembership
import Smoothing.ParameterRound2UniformRawMeanResidual

/-! Complete actual finite increment with uniform constants selected before
all atlases, normalized targets and smoothing scales. The numerical target
slow profile is supplied by the SAME actual smoothing gain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation
variable {m d N c : ℕ} {M Tr Label SubPrimary SubSecondary : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

def ActualRestrictedRawFiniteIncrementAfterMean
    (q Rsub Lprimary Rsecondary : ℕ) (reserve rho : ℝ) (hrho : 0 < rho)
    (Brest Mrest Kcut T Tinv Tobs TP : ℕ → ℝ)
    (CR CU Cmean : ℕ → ℝ) (hCR : ∀ j, 0 ≤ CR j) (hCU : ∀ j, 0 ≤ CU j) (hCmean : ∀ j, 0 ≤ Cmean j)
    (hAnalytic : ActualRawAnalyticBudget (m := m) (d := d) (N := N) (c := c) (M := M) (Tr := Tr)
      (Label := Label) (SubPrimary := SubPrimary) (SubSecondary := SubSecondary)
      q Rsub Lprimary Rsecondary reserve Brest Mrest Kcut T Tinv Tobs TP CR CU)
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (H : parameterRound2_originalTensorGermSpace A B S W)
    (hParam : ∀ i : Fin A.count × Fin c, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i →
      ∀ k, 1 ≤ k → ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B i.2)) z‖ ≤ TP k)
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (primary : Label → Set (Ep × M)) (epsilon0 : ℝ) (he01 : epsilon0 ≤ 1) : Prop :=
    let p := parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell
    ∀ hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W,
    ParameterRound2ActualGermMeanPhysicalResidual A B S W p H rho ell q Cmean epsilon0 F hF g hsm →
    let C := fun j => CR j+Cmean j+CU j
    ActualRestrictedRawFiniteIncrementConclusion (Tr := Tr) (SubSecondary := SubSecondary)
      q Rsub Lprimary Rsecondary reserve Brest Mrest Kcut T Tinv Tobs
      A B S W p H rho ell F hF g primary epsilon0 C hsm

end GlobalEmbedding.Continuation
