import Smoothing.ParameterRound2BackgroundGermTransfer
import Probes.ActualUniformRestrictedRawFiniteIncrementAllIndex
import Probes.ActualRepairIncrementConsumer

/-! Complete actual finite increment with uniform constants selected before
all atlases, normalized targets and smoothing scales. The numerical target
slow profile is supplied by the SAME actual smoothing gain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M Tr : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

def ActualUniformRestrictedBackgroundRepairStatementAllIndex
    (B0 : ℕ → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bmean : ℕ → ℝ → ℝ) (Mmean Dinput Brest Mrest Kcut : ℕ → ℝ)
    (hBmean : ∀ s R, 0 ≤ Bmean s R) (hMmean : ∀ s, 0 ≤ Mmean s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (hBrest : ∀ s, 0 ≤ Brest s) (hMrest : ∀ s, 0 ≤ Mrest s) (hKcut : ∀ s, 0 ≤ Kcut s)
    (T Tinv Tobs TP : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) (hTP : ∀ k, 0 ≤ TP k) : Prop :=
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧ ∀
      (Label SubPrimary SubSecondary : Type*) [Fintype Label] [DecidableEq Label]
      [Fintype SubPrimary] [Fintype SubSecondary] (c : ℕ)
      (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
      (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
      (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
      (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
      (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
      (H : parameterRound2_originalTensorGermSpace A B S W),
    let p := parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell
    (∀ s, p s H ≤ B0 s) →
    (∀ i : Fin A.count × Fin c, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i →
      ∀ k, 1 ≤ k → ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B i.2)) z‖ ≤ TP k) → ∀
      (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
      (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
      (primary : Label → Set (Ep × M)),
    ParameterRound2MeanRawGermReserveSupply (Tr := Tr) A B S W p H rho q Rsub Lprimary reserve
      Bmean Mmean Dinput T F hF g primary ell →
    ∃ hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W,
    ∀ epsilon, 0 < epsilon → epsilon < epsilon0 →
    let Top := parameterRound2_actualGermMeanReserveOperator A B S W p H rho ell F hF g q hsm
    let K := fun i : ℕ => (meanReserveStep (p 0) H rho (Top epsilon))^[i] H
    (∀ i ≤ q, p 0 (K i-H) ≤ rho/2) ∧
    ∀ (Gdomain : Set (Ep × M)) (hGdomain : IsOpen Gdomain), Gdomain ⊆ W →
    (∀ i, MapsTo (incrementsOriginalJointPoint A B i) (S i) Gdomain) →
    let gG := parameterRound2_restrictPrimaryFamily F g Gdomain hGdomain
    ∀ (delta : ℝ), 0 ≤ delta → delta ≤ epsilon*ell →
    ∀ (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m),
    let U := actualOriginalIncrementMap F hF gG (K q).val (q+2) (epsilon*ell) delta choice
    ∀ (j : ℕ)
      (inputbar : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x)) (Delta : ℝ)
      (raw : ActualOriginalSecondaryRawData (Tr := Tr) F hF gG (K q).val inputbar
        (actualSecondaryInputOrder q j) (actualSecondarySolveOrder q j) j q Rsub Lprimary
        reserve (Brest j) (Mrest j) (Kcut j) T Tinv Gdomain primary ell delta (epsilon*ell) Delta choice)
      (Obs : Fin A.count × Fin c → Set X)
      (obs : ∀ i : Fin A.count × Fin c, ActualOriginalSecondaryObservationData raw Tobs Rsecondary
        (A.chart i.1) (Obs i)
        (parameterRound2_meanParameterMap (m := m) (B i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i))),
    ∀ (G SG : Ep × M → V),
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B G i)
      (incrementsOriginalDifferentiation A B i)) →
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B SG i)
      (incrementsOriginalDifferentiation A B i)) →
    (∀ z ∈ Gdomain, (fun x => F z.1 x) = (fun x => SG (z.1,x))) →
    ∀ (hstar h0 SH : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (deltaNext : ℝ), delta ≠ 0 → deltaNext ≠ 0 →
    H.val = (fun t x => SH t x-(deltaNext/delta)^2 • h0 t x) →
    let Hold := fun t x => (delta^2)⁻¹ • (hstar t x-inducedMetric (I := 𝓙) (fun y => G (t,y)) x)
    let Hnext := fun t x => (deltaNext^2)⁻¹ • (hstar t x-inducedMetric (I := 𝓙) (fun y => G (t,y)+U (t,y)) x)
    let O := incrementsOriginalDifferentiation A B
    let WT := fun T => paperAtlasWeighted 0 j (epsilon*ell) (incrementsOriginalTensorCoordinates A B T) O S
    let WM := fun b f => paperAtlasWeighted b j (epsilon*ell) (incrementsOriginalMapCoordinates A B f) O S
    (∀ i, ∃ V0 : Set (Fin (m+1+d) → ℝ), IsOpen V0 ∧ S i ⊆ V0 ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B (fun t x => Hold t x-SH t x) i) V0) →
    WT (fun t x => Hold t x-SH t x) ≠ ⊤ →
    WM 2 (fun z => G z-SG z) ≠ ⊤ →
    (∀ i, ∃ V0 : Set (Fin (m+1+d) → ℝ), IsOpen V0 ∧ S i ⊆ V0 ∧ V0 ⊆ O i ∧
      ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B (fun z => G z+U z) i) V0 ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B (fun t x => Hnext t x-h0 t x) i) V0) ∧
    WT (fun t x => Hnext t x-h0 t x) ≠ ⊤ ∧
    (WT (fun t x => Hnext t x-h0 t x)).toReal ≤ (deltaNext^2)⁻¹ *
      (C j*(delta*((epsilon*ell)/ell)^q+delta^3/(epsilon*ell)) +
        delta^2*(WT (fun t x => Hold t x-SH t x)).toReal +
        actualRepairCrossCost (m+1) d N j*(WM 2 (fun z => G z-SG z)).toReal*(C j*delta))

end GlobalEmbedding.Continuation
