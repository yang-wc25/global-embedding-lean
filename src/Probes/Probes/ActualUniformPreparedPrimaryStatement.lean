import Probes.ActualUniformRestrictedRawFiniteIncrement
import Smoothing.ParameterRound2ActualFinalPreparedProfiles
import Probes.ActualRawProfileBudgets

/-! Complete actual finite increment with uniform constants selected before
all atlases, normalized targets and smoothing scales. The numerical target
slow profile is supplied by the SAME actual smoothing gain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
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

def ActualUniformPreparedPrimaryFiniteStatement
    (B0 : ℕ → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bmean : ℕ → ℝ → ℝ) (Mmean Dinput Msecondary Kcut : ℕ → ℝ)
    (hBmean : ∀ s R, 0 ≤ Bmean s R) (hMmean : ∀ s, 0 ≤ Mmean s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (hMsecondary : ∀ s, 0 ≤ Msecondary s) (hKcut : ∀ s, 0 ≤ Kcut s)
    (T Tinv Tobs TP : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) (hTP : ∀ k, 0 ≤ TP k) : Prop :=
    let Csize := fun s R => parameterRound2_rawMeanOriginalGermNormCost
      (m := m) (d := d) (N := N) (c := c) (M := M) (Tr := Tr) (Λ := Label) (Β := SubPrimary)
      (s+(q+4)) q s Rsub Lprimary hq (by omega) reserve (Bmean s R) (Mmean s)
      hc (hBmean s R) (hMmean s) T TP hT hTP
    let Rq := parameterRound2_uniformMeanProfile B0 Csize (q+4) q
    let Brest := fun j => Bmean (actualSecondarySolveOrder q j) (Rq (actualSecondaryInputOrder q j))
    let Mrest := fun j => max (Mmean (actualSecondarySolveOrder q j)) (Msecondary j)
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧ ∀
      (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
      (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
      (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W Vprep : Set (Ep × M))
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
    ParameterRound2MeanRawPreparedCanonicalSupply (Tr := Tr) A B S W Vprep p H rho q Rsub Lprimary reserve
      Bmean Mmean Dinput T F hF g primary ell →
    ∃ hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W,
    ActualRestrictedRawFiniteIncrementConclusion (Tr := Tr) (SubSecondary := SubSecondary)
      q Rsub Lprimary Rsecondary reserve Brest Mrest Kcut T Tinv Tobs
      A B S W p H rho ell F hF g primary epsilon0 C hsm ∧
    ∀ epsilon, 0 < epsilon → epsilon < epsilon0 →
    let Top := parameterRound2_actualGermMeanReserveOperator A B S W p H rho ell F hF g q hsm
    let K := fun i => (meanReserveStep (p 0) H rho (Top epsilon))^[i] H
    (∀ i ≤ q, p 0 (K i-H) ≤ rho/2) ∧ (∀ s, p s (K q) ≤ Rq s) ∧
    ∃ G : Set (Ep × M), ∃ hG : IsOpen G, G ⊆ W ∧ G ⊆ Vprep ∧
      (∀ i, MapsTo (incrementsOriginalJointPoint A B i) (S i) G) ∧
      (∀ i : Fin A.count × Fin c, actualRawObserverOpen (A.chart i.1) G ⊆
        (B i.2).source ×ˢ (A.chart i.1).target) ∧
      ∀ j, Nonempty (∀ i : Fin A.count × Fin c,
        ParameterRound2GlobalMeanRawProfiles (Tr := Tr)
          (actualSecondaryInputOrder q j) (q+2) (actualSecondarySolveOrder q j) Rsub Lprimary
          reserve (Brest j) (Mrest j) T F hF
          (parameterRound2_restrictPrimaryFamily F g G hG) (K q).val (K q).val G primary (A.chart i.1)
          (actualRawObserverOpen (A.chart i.1) G) (parameterRound2_meanParameterMap (m := m) (B i.2) ''
            ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)) (epsilon*ell) ell 0)

end GlobalEmbedding.Continuation
