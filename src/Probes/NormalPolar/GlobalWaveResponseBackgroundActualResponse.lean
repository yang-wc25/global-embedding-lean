import NormalPolar.GlobalWaveResponseBackgroundActualPairs
import NormalPolar.GlobalWaveResponseBackgroundGlobalResponse
import Probes.ActualSecondaryPrimaryRawConsumers

/-! Native responses of the actual finite-background displacement on the
original atlas. Raw pairs and a valid observer neighborhood are constructed
from the original reserve supply and the same actual mean iterate. Constants
precede the actual fields, epsilon, delta and probe parameter. Adaptation is
consumed from the same produced physical geometry, not supplied independently.
The common positivity and actual scalar-input joint regularity remain the
original geometric obligations, not full-wave output assumptions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation
universe uM uTr uΛ uΒ
variable {m d N p r count : ℕ} {M : Type uM} {Tr : Type uTr} {Λ : Type uΛ} {Β : Type uΒ}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

private local instance bgActualHessianSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance bgActualHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance bgActualHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

/-- The same finite forced background substitutions and their original
paper-norm residual, obtained from primitive geometry/input profiles. -/
theorem globalWave_actual_background_native_response
    (atlas : BufferedAtlas M D) (param : Fin count → OpenPartialHomeomorph Ep Ep)
    (hAtlas : IsSmoothBufferedAtlas atlas) (hParamSmooth : ∀ i, param i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
    (S : Fin atlas.count × Fin count → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation atlas param i)
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (H : parameterRound2_originalTensorGermSpace atlas param S W) (HBound : ℕ → ℝ)
    (hH : ∀ s, parameterRound2_originalTensorGermSeminorm atlas param S W hS hSO ell s H ≤ HBound s)
    (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ)
    (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (T TP : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTP : ∀ k, 0 ≤ TP k)
    (hParam : ∀ i : Fin atlas.count × Fin count, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i → ∀ k, 1 ≤ k →
      ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m:=m) (param i.2)) z‖ ≤ TP k)
    (ProbeB ProbeDiff : ℕ → ℝ) (Su : Set (Fin p → ℝ)) (hSu : IsOpen Su) :
    let C := fun s R => parameterRound2_rawMeanIndexUniformCost.{uM,uTr,uΛ,uΒ}
      (m:=m) (d:=d) (N:=N) (M:=M) (Tr:=Tr)
      (s+(q+4)) q s Rsub Lprimary hq (by omega) reserve (Bnd s R) (Mg s) hc
      (hBnd s R) (hMg s) T TP hT hTP
    let pj := parameterRound2_originalTensorGermSeminorm atlas param S W hS hSO ell
    let cap := round4ParameterProbeForcedCap HBound rho ProbeB C q (q+4)
    let R := round4ParameterProbeForcedProfile HBound ProbeB C (q+4)
    let Cd := fun s bound => C s bound*Dinput s
    0 < cap ∧ ∀ iter ≤ q+1, ∀ s, 2 ≤ s → ∃ Cwave : ℝ, 0 ≤ Cwave ∧ ∀
      (F : Ep → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F b))
      (g : IncrementsGlobalPrimaryFamily (I:=𝓙) (m:=m) (N:=N) (Λ:=Λ) (Β:=Β) F)
      (primary : Λ → Set (Ep × M)),
    ParameterRound2MeanRawGermReserveSupply (Tr:=Tr) atlas param S W pj H rho q Rsub Lprimary
      reserve Bnd Mg Dinput T F hF g primary ell →
    ∀ (epsilon : ℝ), 0 < epsilon → epsilon < cap → ∀ (delta : ℝ)
      (label : (Fin r × Bool) ↪ Fin p) (c : Fin r → Ep → D → M)
      (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I:=𝓙) (F b) (c l b x))
      (phase : Fin r → Ep × M → ℝ) (probeLength : ℕ)
      (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
      (P : (Fin p → ℝ) → parameterRound2_originalTensorGermSpace atlas param S W),
    (∀ u ∈ Su, (P u).val = (delta^2)⁻¹ •
      round4PrescribedNativeMean label F hF c vf phase (epsilon*ell) probeLength a u) →
    (∀ u ∈ Su, ∀ s, pj s (P u) ≤ ProbeB s) →
    (∀ u ∈ Su, pj 0 (P u) ≤ rho/4) →
    (∀ u ∈ Su, ∀ v ∈ Su, ∀ s,
      pj s (P u-P v) ≤ ((‖u‖+‖v‖)*‖u-v‖)*ProbeDiff s) →
    let A := round4ActualBackgroundMeanIterate F hF g (q+2) (epsilon*ell) delta H.val
      (round4PrescribedNativeMean label F hF c vf phase (epsilon*ell) probeLength a)
    ∀ (idx : Fin atlas.count × Fin count) (u : Fin p → ℝ), u ∈ Su →
    ∀ (base : ParameterRound2GlobalMeanPrimitives F hF g (A iter u) W primary)
      (hArgument : ∀ nu, ContMDiffOn ((𝓘(ℝ,(Fin p → ℝ)×Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞
        (fun z : ((Fin p → ℝ)×Ep)×M =>
          g.linearArgument nu z.1.2 z.2 (A iter z.1.1 z.1.2 z.2))
        ((((fun z : ((Fin p → ℝ)×Ep)×M => z.1.1) ⁻¹' Su) ∩
          ((fun z : ((Fin p → ℝ)×Ep)×M => (z.1.2,z.2)) ⁻¹' W)) ∩
          ((fun z : ((Fin p → ℝ)×Ep)×M => (z.1.2,z.2)) ⁻¹' primary nu)))
      (hPositive : ∀ v ∈ Su, ∀ nu z, z ∈ incrementsGlobalRelativeSupport W (g.cutoff nu) →
        0 < g.linearArgument nu z.1 z.2 (A iter v z.1 z.2))
      (geom : ActualOriginalPrimaryPhysicalGeometry F hF g),
    let Samples := parameterRound2_meanParameterMap (m:=m) (param idx.2) ''
      ((parameterTensorModelEquiv (m+1) d) ⁻¹' S idx)
    let Dpair := Dinput s*round4ParameterProbeForcedDifferenceCost ProbeDiff Cd R (q+4) iter (s+(q+4))
    ∀ y ∈ Samples,
    let f := fun v x => incrementsGlobalPrimaryWave F hF g (A iter v) (q+2) (epsilon*ell)
      (y.1,(atlas.chart idx.1).symm x)
    (HasFDerivAt (fun v => f v y.2) (fderiv ℝ (fun v => f v y.2) u) u ∧
      ‖fderiv ℝ (fun v => f v y.2) u‖ ≤ 2*(Cwave*Dpair*(epsilon*ell))*‖u‖) ∧
    (HasFDerivAt (fun v => fderiv ℝ (fderiv ℝ (f v)) y.2)
      (fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (f v)) y.2) u) u ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (f v)) y.2) u‖ ≤
        2*(Cwave*Dpair/(epsilon*ell))*‖u‖) := by
  intro C pj cap R Cd
  have hpairs := globalWave_actual_background_raw_pairs (Λ:=Λ) (Β:=Β) (Tr:=Tr) (N:=N) (p:=p) (r:=r)
    atlas param hAtlas hParamSmooth S W hS hSO ell hell hell1 H HBound hH rho hrho
    q Rsub Lprimary hq reserve hc Bnd Mg Dinput hBnd hMg hDinput T TP hT hTP hParam ProbeB ProbeDiff Su
  refine ⟨hpairs.1,?_⟩
  intro iter hi s hs
  obtain ⟨Cwave,hCwave,hresponse⟩ := globalWave_background_global_native_response
    (P:=Fin p → ℝ) (I:=𝓙) (M:=M) («Ep» := EuclideanSpace ℝ (Fin d)) (Tr:=Tr) (m:=m) (N:=N)
    (s+(q+4)) (q+2) s Rsub Lprimary (by omega) hs reserve (Bnd s (R iter (s+(q+4))))
    (Mg s) hc (hBnd s _) (hMg s) T hT
  refine ⟨Cwave,hCwave,?_⟩
  intro F hF g primary hraw epsilon he hecap delta label c vf phase probeLength a P
    hPv hP hP0 hPQ A idx u hu base hArgument hPositive geom Samples Dpair y hy f
  have hPair := hpairs.2 F hF g primary hraw epsilon he hecap delta label c vf phase
    probeLength a P hPv hP hP0 hPQ iter hi s idx u hu
  obtain ⟨G0,hG0,O0,Delta0,hG0W,hO0,⟨raw0⟩,_⟩ := hPair u hu
  have hDpair : 0 ≤ Dpair := mul_nonneg (hDinput s)
    (round4ParameterProbeForcedDifferenceCost_nonneg ProbeDiff Cd R (q+4) iter (s+(q+4)))
  apply hresponse F hF g (A iter) Su hSu u hu W primary (A iter u) base hArgument hPositive geom.adaptation
    (atlas.chart idx.1) (contMDiffOn_symm_of_mem_maximalAtlas (hAtlas.chart_mem idx.1))
    O0 Samples raw0.hO raw0.hSO (fun z hz => (hO0 hz).2) (fun z hz => hG0W (raw0.hmapWO hz))
    (epsilon*ell) ell Dpair (mul_pos he hell) hDpair _ y hy
  intro v hv
  obtain ⟨G,hG,Oraw,Delta,_,_,hrawv,hDelta⟩ := hPair v hv
  exact ⟨G,hG,Oraw,Delta,hrawv,hDelta⟩

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_actual_background_native_response
