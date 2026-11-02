import Probes.ActualUniformRestrictedSmoothedStep
import Probes.ActualRepairSixTermClosure

/-! The same actual update, with the literal stage choices (6.5), both
reserves and the six original exponents (6.7). The input tensor and map
derivative orders remain those of the unchanged raw finite construction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff ENNReal Classical BigOperators
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

local instance actualUniformRestrictedScaledRepairChartedSpace : ChartedSpace (Ep × D) (Ep × M) :=
  prodChartedSpace Ep Ep D M
local instance actualUniformRestrictedScaledRepairIsManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (Ep × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) Ep M

def ActualUniformRestrictedScaledRepairStatement
    (B0 : ℕ → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bmean : ℕ → ℝ → ℝ) (Mmean Dinput Brest Mrest Kcut : ℕ → ℝ)
    (hBmean : ∀ s R, 0 ≤ Bmean s R) (hMmean : ∀ s, 0 ≤ Mmean s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (hBrest : ∀ s, 0 ≤ Brest s) (hMrest : ∀ s, 0 ≤ Mrest s) (hKcut : ∀ s, 0 ≤ Kcut s)
    (T Tinv Tobs TP : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) (hTP : ∀ k, 0 ≤ TP k)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (radius : ℝ) (hradius : 0 < radius) : Prop :=
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧ ∀
      (A : BufferedAtlas M D) (B : TensorBufferedChartFamily (Fin c) Ep Ep)
      (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
      (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
      (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B.chart i)
      (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
      (H : parameterRound2_originalTensorGermSpace A B.chart S W),
    let p := parameterRound2_originalTensorGermSeminorm A B.chart S W hS hSO ell
    (∀ s, p s H ≤ B0 s) →
    ( ∀ i : Fin A.count × Fin c, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i →
      ∀ k, 1 ≤ k → ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B.chart i.2)) z‖ ≤ TP k) →
    ∀
    (parameterSet : Set Ep)
    (RS : TensorRawCutoffPreparation A BS0 TS0 Ds)
    (RP : TensorLocalRawPreparation B parameterSet BP0 TP0 Dp)
    (hbuffer : radius ≤ min B.buffer A.buffer)
    (Omega : Fin A.count → Set D) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, IsCompact (Omega i)) (hQ : ∀ i, IsCompact (Q i))
    (hOmegaTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQTarget : ∀ i, Q i ⊆ (B.chart i).target)
    (hsource : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (hparameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i)
    (hSinner : ∀ i, S i ⊆ tensorLocalOriginalInner A B parameterSet i),
    ∀ t : ℝ, ell ≤ t → t ≤ 1 →
    ∀ (G : Ep × M → V), ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ G →
    ∀ (hstar h0 : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x)),
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart hstar i)
      (incrementsOriginalDifferentiation A B.chart i)) →
    ∀ (delta deltaNext : ℝ), 0 < delta → deltaNext ≠ 0 →
    let Hold := fun t x => (delta^2)⁻¹ • (hstar t x-inducedMetric (I := 𝓙) (fun y => G (t,y)) x)
    ∀ budget : ℝ,
    (parameterLocalOriginalTotalPairWeighted A B G Hold q t
      (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal ≤ budget →
    let mu := (volume : Measure X)
    let kernel := fixedSmoothingKernel mu radius hradius q
    let chi := parameterLocalProductCutoff A B (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
    let SF := parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu kernel ell chi G
    let SH := tensorLocalParameterSmoothing A B hA mu kernel ell chi Hold
    H.val = (fun t x => SH t x-(deltaNext/delta)^2 • h0 t x) →
    ∀ (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t)),
    ∀ (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary)
      F) (primary : Label → Set (Ep × M)),
    ParameterRound2MeanRawGermReserveSupply (Tr := Tr) A B.chart S W p H rho q Rsub Lprimary reserve
      Bmean Mmean Dinput T F hF g primary ell →
    ∃ hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B.chart S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B.chart S W,
    ∀ epsilon, 0 < epsilon → epsilon < epsilon0 → delta ≤ epsilon*ell →
    let Top := parameterRound2_actualGermMeanReserveOperator A B.chart S W p H rho ell
      F hF g q hsm
    let K := fun i : ℕ => (meanReserveStep (p 0) H rho (Top epsilon))^[i] H
    (∀ i ≤ q, p 0 (K i-H) ≤ rho/2) ∧
    ∀ (Gdomain : Set (Ep × M)) (hGdomain : IsOpen Gdomain), Gdomain ⊆ W →
    (∀ i, MapsTo (incrementsOriginalJointPoint A B.chart i) (S i) Gdomain) →
    (∀ z ∈ Gdomain, (fun x => F z.1 x) = (fun x => SF (z.1,x))) →
    let gG := parameterRound2_restrictPrimaryFamily F g Gdomain hGdomain
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
        (parameterRound2_meanParameterMap (m := m) (B.chart i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i))),
    let Hnext := fun t x => (deltaNext^2)⁻¹ • (hstar t x-inducedMetric (I := 𝓙) (fun y => G (t,y)+U (t,y)) x)
    let O := incrementsOriginalDifferentiation A B.chart
    let WT := fun T => paperAtlasWeighted 0 j (epsilon*ell) (incrementsOriginalTensorCoordinates A B.chart T) O S
    (∀ i, ∃ V0 : Set (Fin (m+1+d) → ℝ), IsOpen V0 ∧ S i ⊆ V0 ∧ V0 ⊆ O i ∧
      ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B.chart (fun z => G z+U z) i) V0 ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart (fun t x => Hnext t x-h0 t x) i) V0) ∧
    WT (fun t x => Hnext t x-h0 t x) ≠ ⊤ ∧
    ∀ k s : ℕ, 10 ≤ k → s ≤ k+1 → q = 40*(k+1) →
      ell = t^(11/10 : ℝ) → delta = t^k → epsilon*ell = t^(6/5 : ℝ) →
      deltaNext = (t^(6/5 : ℝ))^s →
    let inherited := (parameterLocalOriginalTotalPairWeighted A B G Hold j t
      (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal
    (WT (fun t x => Hnext t x-h0 t x)).toReal ≤
      (2*C j*(1+budget))*t^(1/5 : ℝ)*(1+inherited) ∧
    (s = k+1 → (WT (fun t x => Hnext t x-h0 t x)).toReal ≤
      ∑ i : Fin 6, actualRepairSixCoefficients (C j) budget inherited i*t^repairErrorExponent k i)

end GlobalEmbedding.Continuation
