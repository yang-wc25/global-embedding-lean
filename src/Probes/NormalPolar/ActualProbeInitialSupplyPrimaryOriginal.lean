import NormalPolar.ActualProbeInitialSupplyPrimary
import NormalPolar.ParameterDisplacementCombinedParameterNative
import NormalPolar.ActualRepairModelFirstDefectMapNative
import Probes.Round3ParameterRawAtlasData
import Smoothing.Round3ParameterPrimaryRestriction

/-!
# Original norms of the same joint primary on the physical parameter space

The native raw records use the canonical pullbacks of one global primary
family, one global background input, and one global prescribed parameter.
The existing exact pullback theorem supplies the identity of the physical
waves. No identity or bound for a completed wave is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation

variable {M P Tr Λ Β : Type*} {m d N p r count : ℕ}
  [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

/-- The reserve supplier's restriction to the whole physical domain changes
neither the primitive family nor any of its native realizations. -/
theorem actualProbeInitialSupply_restrict_univ
    (F : P → M → V)
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F) :
    round3Parameter_restrictPrimaryFamily F g univ isOpen_univ = g := by
  have hchart : (fun l b => (g.chart l b).restrOpen univ isOpen_univ) = g.chart := by
    funext l b
    apply OpenPartialHomeomorph.ext ((g.chart l b).restrOpen univ isOpen_univ)
      (g.chart l b) (fun _ => rfl) (fun _ => rfl)
    simp only [OpenPartialHomeomorph.restrOpen_source,inter_univ]
  cases g
  simp only [round3Parameter_restrictPrimaryFamily] at hchart ⊢
  congr 1

structure ActualProbeInitialPrimaryRawAtlas
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin count → Set (Fin (m+1+d) → ℝ))
    (F : P → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
    (c : Fin r → P → D → M) (chi : Fin r → P × D → ℝ)
    (nu : (l : Fin r) → (b : P) → (x : D) → normalSpace (I := IM) (F b) (c l b x))
    (phase : Fin r → P × M → ℝ)
    (a : Fin r → OpenPartialHomeomorph (P × M) (P × D))
    (input inputbar : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : P → Fin p → ℝ) (W : Set (P × M)) (K : (Λ ⊕ Fin r) → Set (P × M))
    (n backgroundLength j Rbackground L : ℕ)
    (reserve Bnd Mg Bchi Bnu Ku Mphase tau ell Delta : ℝ)
    (Tbackground Tprobe : ℕ → ℝ) where
  domain : Fin A.count × Fin count → Set X
  target : ∀ i z, z ∈ domain i → z.2 ∈ (A.chart i.1).target
  background : ∀ i : Fin A.count × Fin count,
    ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n backgroundLength (j+1) Rbackground L
      reserve Bnd Mg Tbackground
      (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
      (round3ParameterNativePrimary F g (B i.2))
      (fun t => input ((B i.2).symm t)) (fun t => inputbar ((B i.2).symm t))
      (round3ParameterNativeDomain (B i.2) W)
      (fun l => round3ParameterNativeDomain (B i.2) (K (Sum.inl l)))
      (A.chart i.1) (domain i) ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)
      tau ell Delta
  prescribed : ∀ i : Fin A.count × Fin count,
    ActualPrescribedObservationProfiles
      (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
      (fun l t => c l ((B i.2).symm t))
      (fun l z => chi l ((B i.2).symm z.1,z.2))
      (fun l t => nu l ((B i.2).symm t))
      (fun l => round3ParameterChartPullback (B i.2) (a l))
      (round3ParameterNativeDomain (B i.2) W)
      (fun l => round3ParameterNativeDomain (B i.2) (K (Sum.inr l)))
      n (j+2) ell Mg Bchi Bnu (fun z : X => (z.1,(A.chart i.1).symm z.2))
      (domain i) ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i) Tprobe
      (fun l z => phase l ((B i.2).symm z.1,z.2)) Mphase
  parameter_smooth : ∀ i,
    ContDiffOn ℝ ∞ (fun z : X => u ((B i.2).symm z.1)) (domain i)
  parameter_jets : ∀ i k, k ≤ j+2 →
    ∀ z ∈ (parameterTensorModelEquiv (m+1) d) ⁻¹' S i,
      ell^k*‖iteratedFDeriv ℝ k (fun y : X => u ((B i.2).symm y.1)) z‖ ≤ Ku
  overlap : ∀ i z, z ∈ (parameterTensorModelEquiv (m+1) d) ⁻¹' S i →
    (Finset.univ.filter (fun l => (z.1,(A.chart i.1).symm z.2) ∈
      round3ParameterNativeDomain (B i.2) (K l))).card ≤ L

attribute [local irreducible] OpenPartialHomeomorph.symm
set_option backward.isDefEq.respectTransparency true in
theorem actualProbeInitialSupply_primary_original_norms_from_raw
    (n backgroundLength probeLength j Rbackground L : ℕ)
    (hbackgroundOrder : j+3+backgroundLength ≤ n) (hprobeOrder : j+3+probeLength ≤ n)
    (reserve Bnd Mg Bchi Bnu Ku Mphase : ℝ)
    (hreserve : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) (hKu : 0 ≤ Ku)
    (weight : Fin r → ℝ) (Tbackground Tprobe : ℕ → ℝ)
    (hTbackground : ∀ k, 0 ≤ Tbackground k) (hTprobe : ∀ k, 0 ≤ Tprobe k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
      (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph P Ep)
      (S : Fin A.count × Fin count → Set (Fin (m+1+d) → ℝ))
      (F : P → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
      (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
      (hg : ∀ l b, Round3ParameterChartPreserves (g.chart l b))
      (hadapt : ∀ l b z, z ∈ (g.chart l b).source → g.phase l z = (g.chart l b z).2 0)
      (label : (Fin r × Bool) ↪ Fin p)
      (c : Fin r → P → D → M) (chi : Fin r → P × D → ℝ)
      (nu : (l : Fin r) → (b : P) → (x : D) → normalSpace (I := IM) (F b) (c l b x))
      (phase : Fin r → P × M → ℝ)
      (a : Fin r → OpenPartialHomeomorph (P × M) (P × D))
      (ha : ∀ l, Round3ParameterChartPreserves (a l))
      (input inputbar : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
      (u : P → Fin p → ℝ) (tau ell delta Delta : ℝ)
      (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1) (hdelta : 0 ≤ delta)
      (W : Set (P × M)) (K : (Λ ⊕ Fin r) → Set (P × M))
      (raw : ActualProbeInitialPrimaryRawAtlas (Tr := Tr) A B S F hF g c chi nu phase a
        input inputbar u W K n backgroundLength j Rbackground L
        reserve Bnd Mg Bchi Bnu Ku Mphase tau ell Delta Tbackground Tprobe),
    let vf := fun l b x => (-(delta*tau)/(weight l)^2) • (chi l (b,x) • nu l b x)
    let U := fun z : P × M => actualParameterProbeCombinedPrimary F hF g label c vf phase
      tau delta backgroundLength probeLength a input (u z.1) z
    let coordinates := incrementsOriginalMapCoordinates A B U
    (∀ i, ∃ G : Set (Fin (m+1+d) → ℝ), IsOpen G ∧ S i ⊆ G ∧
      G ⊆ incrementsOriginalDifferentiation A B i ∧ ContDiffOn ℝ ∞ (coordinates i) G) ∧
    (paperAtlasWeighted 2 j tau coordinates (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 2 j tau coordinates (incrementsOriginalDifferentiation A B) S).toReal ≤ C*delta/tau) ∧
    (paperAtlasCj 2 coordinates (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasCj 2 coordinates (incrementsOriginalDifferentiation A B) S).toReal ≤ C*delta/tau) := by
  obtain ⟨Cnative,hCnative,hconstruct⟩ := actualProbeInitialSupply_joint_primary_raw_jets_uniform
    (M := M) («Ep» := Ep) (Tr := Tr) (m := m) (N := N) (p := p) (Λ := Λ) (Β := Β)
    n backgroundLength probeLength (j+1) Rbackground L (by omega) (by omega)
    reserve Bnd Mg Bchi Bnu Ku Mphase hreserve hBnd hMg hBchi hBnu hKu
    weight Tbackground Tprobe hTbackground hTprobe
  let C := actualRepairModelFirstDefectMapNormCost m d N j Cnative
  refine ⟨C,actualRepairModelFirstDefectMapNormCost_nonneg m d N j Cnative hCnative,?_⟩
  intro A B S F hF g hg hadapt label c chi nu phase a ha input inputbar u
    tau ell delta Delta htau htaul hell1 hdelta W K raw vf U coordinates
  have hadaptNative (i : Fin A.count × Fin count) :
      ∀ l b z, z ∈ ((round3ParameterNativePrimary F g (B i.2)).chart l b).source →
        (round3ParameterNativePrimary F g (B i.2)).phase l z =
          ((round3ParameterNativePrimary F g (B i.2)).chart l b z).2 0 := by
    intro l b z hz
    change g.phase l ((B i.2).symm z.1,z.2) =
      (round3ParameterChartPullback (B i.2) (g.chart l b) z).2 0
    rw [round3ParameterChartPullback_apply]
    exact hadapt l b ((B i.2).symm z.1,z.2)
      ((round3ParameterChartPullback_source (B i.2) (g.chart l b) z).mp hz).2.1
  have hNative (i : Fin A.count × Fin count) :=
    hconstruct (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
      (round3ParameterNativePrimary F g (B i.2)) label
      (fun l t => c l ((B i.2).symm t)) (fun l z => chi l ((B i.2).symm z.1,z.2))
      (fun l t => nu l ((B i.2).symm t)) (fun l z => phase l ((B i.2).symm z.1,z.2))
      (fun l => round3ParameterChartPullback (B i.2) (a l))
      (fun t => input ((B i.2).symm t)) (fun t => inputbar ((B i.2).symm t))
      tau ell delta Delta hdelta (round3ParameterNativeDomain (B i.2) W)
      (fun l => round3ParameterNativeDomain (B i.2) (K l)) (A.chart i.1)
      (raw.domain i) ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)
      (raw.background i) (hadaptNative i) (raw.prescribed i) (raw.overlap i)
      (fun t => u ((B i.2).symm t)) (raw.parameter_smooth i) (raw.parameter_jets i)
  have hDomain (i) : raw.domain i ⊆ (B i.2).target ×ˢ (A.chart i.1).target := by
    intro z hz
    exact ⟨((raw.background i).hmapWO hz).1,raw.target i z hz⟩
  let native := fun (i : Fin A.count × Fin count) (z : X) => round4ParameterProbeCombinedPrimary
    (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
    (round3ParameterNativePrimary F g (B i.2)) label
    (fun l t => c l ((B i.2).symm t)) (fun l t => vf l ((B i.2).symm t))
    (fun l w => phase l ((B i.2).symm w.1,w.2)) tau delta backgroundLength probeLength
    (fun l => round3ParameterChartPullback (B i.2) (a l)) (fun t => input ((B i.2).symm t))
    (u ((B i.2).symm z.1)) (z.1,(A.chart i.1).symm z.2)
  have heq (i) : EqOn (actualRepairModelFirstDefectObservedMap A B U i) (native i) (raw.domain i) := by
    intro z hz
    dsimp only [actualRepairModelFirstDefectObservedMap,U,native,round3ParameterNativePrimary]
    exact (actualParameterProbeCombinedPrimary_native_pullback F hF g label c vf phase tau delta
      backgroundLength probeLength a (B i.2) hg ha input (u ((B i.2).symm z.1))
      z.1 (hDomain i hz).1 ((A.chart i.1).symm z.2)).symm
  have hSmooth (i) : ContDiffOn ℝ ∞ (actualRepairModelFirstDefectObservedMap A B U i) (raw.domain i) :=
    (hNative i).1.congr (heq i)
  have hJets : ∀ i, ∀ k ≤ j+2, ∀ z : X, parameterTensorModelEquiv (m+1) d z ∈ S i →
      tau^k*‖iteratedFDeriv ℝ k (actualRepairModelFirstDefectObservedMap A B U i) z‖ ≤
        Cnative*delta*tau := by
    intro i k hk z hz
    rw [(((heq i).eventuallyEq_of_mem ((raw.background i).hO.mem_nhds
      ((raw.background i).hSO hz))).iteratedFDeriv ℝ k).eq_of_nhds]
    exact (hNative i).2 k (by omega) z hz
  exact actualRepairModelFirstDefect_map_norms_from_native A B S raw.domain
    (fun i => (raw.background i).hO) hDomain (fun i => (raw.background i).hSO)
    U j tau delta Cnative htau (htaul.trans hell1) hdelta hCnative hSmooth hJets

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_primary_original_norms_from_raw
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_restrict_univ
