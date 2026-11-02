import NormalPolar.JointBackgroundGroupedQ440Producer
import NormalPolar.ActualProbeInitialSupplyGroupedMean
import NormalPolar.ActualProbeInitialSupplyPrimaryOriginal

/-! The q = 440 grouped error is the true physical combined mean defect
of the same whole-parameter background. The decomposition is obtained from
the produced actual raw primitives and the original atlas covers. No mean
identity, amplitude regularity, or output residual estimate is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation
universe uM uTr uP uΛ uΒ
variable {m N d r : ℕ} {M : Type uM} {Tr : Type uTr} {P : Type uP}
  {Λ : Type uΛ} {Β : Type uΒ}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [TopologicalSpace P] [T2Space P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype Λ] [Fintype Β]
variable {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1))
local notation "𝓙" => 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))

theorem jointBackground_grouped_q440_physical_mean_producer
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B)
    (Q : Fin B.count → Set Ep) (hQ : ∀ i, IsCompact (Q i))
    (hQT : ∀ i, Q i ⊆ (B.chart i).target)
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (S : Fin A.count × Fin B.count → Set (Fin (m+1+d) → ℝ))
    (hS : ∀ idx, IsCompact (S idx))
    (hSO : ∀ idx, S idx ⊆ incrementsOriginalDifferentiation A B.chart idx)
    (hSQ : ∀ idx z, parameterTensorModelEquiv (m+1) d z ∈ S idx → z.1 ∈ Q idx.2)
    (Tp : ℕ → ℕ → ℝ) (hTp : ∀ j k, 0 ≤ Tp j k)
    (weight : Fin r → ℝ) (Mgp Bchi Bnu Mphase : ℕ → ℝ)
    (hMgp : ∀ j, 0 ≤ Mgp j) (hBchi : ∀ j, 0 ≤ Bchi j)
    (hBnu : ∀ j, 0 ≤ Bnu j) (hMphase : ∀ j, 0 ≤ Mphase j)
    (rho : ℝ) (hrho : 0 < rho) :
    let Csrc := jointGroupedPrescribedZeroSourceCost Sub m N d d 444 442 (Tp 0) weight
      (Mgp 0) (Bchi 0) (Bnu 0) (Mphase 0)
    let amplitude := passiveOriginalReserveAmplitude Csrc rho
    let u := passiveOriginalSmallParameter B amplitude
      (passiveOriginalReserveAmplitude_pos Csrc rho hrho) b p₀
    ∃ Ku : ℕ → ℝ, (∀ j, 0 ≤ Ku j) ∧ Ku 0 = amplitude ∧
    let ProbeB := fun j => ((j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j)*
      jointGroupedPrescribedMeanUniformCost Sub m N d (j+444) 442 j (Tp j) weight
        (Mgp j) (Bchi j) (Bnu j) (Mphase j) (Ku j)
    ∀ (H : parameterRound2_originalTensorGermSpace A B.chart S univ)
      (HBound : ℕ → ℝ) (Rsub Lprimary : ℕ) (reserve : ℝ) (hc : 0 < reserve)
      (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ)
      (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s) (hDinput : ∀ s, 0 ≤ Dinput s)
      (Tb : ℕ → ℝ) (hTb : ∀ k, 0 ≤ Tb k),
    let C := round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      440 Rsub Lprimary (by omega) reserve hc Bnd Mg hBnd hMg Tb hTb
    let cap := round4ParameterProbeForcedCap HBound rho ProbeB C 440 444
    let R := round4ParameterProbeForcedProfile HBound ProbeB C 444
    let C0 := fun s => ProbeB s+max 0 (C s (HBound (s+444)))
    let Cd := fun i s => max 0 ((C s (max (R i (s+444)) (R (i+1) (s+444))))*Dinput s)
    0 < cap ∧ ∀ (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1),
    (∀ s, parameterRound2_originalTensorGermSeminorm A B.chart S univ hS hSO ell s H ≤ HBound s) →
    let pj := parameterRound2_originalTensorGermSeminorm A B.chart S univ hS hSO ell
    ∀ (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
      (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
      (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k)) (primary : Λ → Set (P × M)),
    Round3ParameterCanonicalMeanRawReserveSupply (Tr := Tr) A B.chart S univ pj H rho
      440 Rsub Lprimary reserve Bnd Mg Dinput Tb F hF g primary ell →
    ∀ (label : (Fin r × Bool) ↪ Fin d)
      (c : (l : Fin r) → Sub l → P → D → M)
      (chi : (l : Fin r) → Sub l → P × D → ℝ)
      (nu : (l : Fin r) → (s : Sub l) → (p : P) → (x : D) →
        normalSpace (I := 𝓙) (F p) (c l s p x))
      (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (P × M) (P × D))
      (ha : ∀ l s, Round3ParameterChartPreserves (a l s)) (phase : Fin r → P × M → ℝ)
      (Omega : ℕ → Fin A.count × Fin B.count → Set X)
      (hOmega : ∀ j idx, IsOpen (Omega j idx))
      (hOmegaSub : ∀ j idx, Omega j idx ⊆ (B.chart idx.2).target ×ˢ (A.chart idx.1).target)
      (hSamples : ∀ j idx, (parameterTensorModelEquiv (m+1) d) ⁻¹' S idx ⊆ Omega j idx)
      (profiles : ∀ j idx, JointGroupedPrescribedParameterChartRawData F hF c chi nu phase a
        (B.chart idx.2) (A.chart idx.1) (Omega j idx)
        ((parameterTensorModelEquiv (m+1) d) ⁻¹' S idx)
        (j+444) j ell (Mgp j) (Bchi j) (Bnu j) (Mphase j) (Tp j))
      (epsilon : ℝ), 0 < epsilon → epsilon < cap → ∀ (delta : ℝ), 0 < delta →
    let vf := fun l s p x => (-(delta*(epsilon*ell))/(weight l)^2) • (chi l s (p,x) • nu l s p x)
    let meanProbe := fun p x => jointGroupedParameterPrescribedMean label F hF c vf phase
      (epsilon*ell) 442 a (u p) p x
    let background := fun i => actualParameterBackgroundMeanIterate F hF g 442
      (epsilon*ell) delta H.val (fun (_ : Fin 0 → ℝ) => meanProbe) i 0
    ∃ K : ℕ → parameterRound2_originalTensorGermSpace A B.chart S univ,
      (∀ i ≤ 441, (K i).val = background i) ∧
      (∀ i ≤ 441, pj 0 (K i-H) ≤ rho/2) ∧
      (∀ i ≤ 441, ∀ s, pj s (K i) ≤ R i s) ∧
      (∀ i ≤ 441, ∀ s, Nonempty (∀ idx : Fin A.count × Fin B.count,
        ParameterRound2GlobalMeanRawProfiles (Tr := Tr) (s+444) 442 s Rsub Lprimary
          reserve (Bnd s (R i (s+444))) (Mg s) Tb
          (fun t => F ((B.chart idx.2).symm t)) (fun t => hF ((B.chart idx.2).symm t))
          (round3ParameterNativePrimary F
            (round3Parameter_restrictPrimaryFamily F g univ isOpen_univ) (B.chart idx.2))
          (fun t => background i ((B.chart idx.2).symm t))
          (fun t => background i ((B.chart idx.2).symm t))
          (round3ParameterNativeDomain (B.chart idx.2) (univ : Set (P × M)))
          (fun l => round3ParameterNativeDomain (B.chart idx.2) (primary l)) (A.chart idx.1)
          (actualRawObserverOpen (A.chart idx.1)
            (round3ParameterNativeDomain (B.chart idx.2) (univ : Set (P × M))))
          ((parameterTensorModelEquiv (m+1) d) ⁻¹' S idx) (epsilon*ell) ell 0)) ∧
      ∃ E : parameterRound2_originalTensorGermSpace A B.chart S univ,
        E.val = actualProbeInitialGroupedMean F hF g label c vf phase
          (epsilon*ell) delta 442 442 a (background 441) u - delta^2 • H.val ∧
        ∀ s, pj s E ≤ delta^2*(epsilon^441*parameterRound2_finiteMeanErrorCost C0 Cd 444 441 s) := by
  intro Csrc amplitude u
  obtain ⟨Ku,hKu,hKu0,hproduce⟩ := jointBackground_grouped_q440_actual_producer
    (Tr := Tr) (Λ := Λ) (Β := Β) (Sub := Sub)
    A hA B hB Q hQ hQT b p₀ hp₀ S hS hSO hSQ Tp hTp weight Mgp Bchi Bnu Mphase
    hMgp hBchi hBnu hMphase rho hrho
  refine ⟨Ku,hKu,hKu0,?_⟩
  intro ProbeB H HBound Rsub Lprimary reserve hc Bnd Mg Dinput hBnd hMg hDinput
    Tb hTb C cap R C0 Cd
  have hp := hproduce H HBound Rsub Lprimary reserve hc Bnd Mg Dinput hBnd hMg hDinput Tb hTb
  refine ⟨hp.1,?_⟩
  intro ell hell hell1 hH pj F hF g hg primary supply label c chi nu a ha phase Omega hOmega
    hOmegaSub hSamples profiles epsilon he hecap delta hdelta vf meanProbe background
  obtain ⟨K,hvalue,hreserve,hbound,hraw,E,hE,hEbound⟩ := hp.2 ell hell hell1 hH
    F hF g hg primary supply label c chi nu a ha phase Omega hOmega hOmegaSub hSamples profiles
    epsilon he hecap delta hdelta
  have hmean : actualProbeInitialGroupedMean F hF g label c vf phase
      (epsilon*ell) delta 442 442 a (background 441) u =
      delta^2 • round3ParameterPrimaryMean F hF g (background 441) 442 (epsilon*ell) + meanProbe := by
    funext p x
    obtain ⟨ip,hip⟩ := B.cover p
    obtain ⟨ix,hix⟩ := A.cover x
    obtain ⟨raw⟩ := hraw 441 le_rfl 0
    have prim := (raw (ix,ip)).prim
    rw [actualProbeInitialSupply_restrict_univ F g] at prim
    exact actualProbeInitialSupply_grouped_mean_from_raw F hF g hg label c vf phase
      (epsilon*ell) delta 442 442 a (background 441) u univ primary
      (B.chart ip) prim p (B.inner_subset ip hip) x (mem_univ _)
  refine ⟨K,hvalue,hreserve,hbound,hraw,E,?_,hEbound⟩
  rw [hE,hmean]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.jointBackground_grouped_q440_physical_mean_producer
