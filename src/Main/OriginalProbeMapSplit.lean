import NormalPolar.ActualProbeInitialSupplyGroupedIncrement
import NormalPolar.JointMixedGroupedBackgroundBinding
import NormalPolar.OriginalWaveSeedPhysicalResponses
import NormalPolar.ActualRepairModelFirstDefectStateMap

/-!
# The literal complete first map splits into its three actual components

The grouped physical primary has one background block and one block for
each original prescribed label. This file splits the finite sum itself;
all subordinate pieces remain grouped under their original label. The
secondary is retained as the complete signed source sum of that very
primary. No independently chosen map enters the identities.
-/

noncomputable section
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical

namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade

variable {m N p r : ℕ} {M P Λ Β : Type*}
  [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [Fintype Β]
  {Pieces : Fin r → Type*} [∀ l, Fintype (Pieces l)]

local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

/-- Literal splitting of the actual physical grouped array. It requires
no regularity or jet estimate and retains all within-label cross terms in
the amplitudes used by the later secondary construction. -/
theorem probes_actual_grouped_primary_eq
    (F : P → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : (l : Fin r) → Pieces l → P → D → M)
    (vf : (l : Fin r) → (s : Pieces l) → (b : P) → (x : D) →
      normalSpace (I := IM) (F b) (c l s b x))
    (phase : Fin r → P × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
    (a : (l : Fin r) → Pieces l → OpenPartialHomeomorph (P × M) (P × D))
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : P → Fin p → ℝ) (z : P × M) :
    actualProbeInitialGroupedPrimary F hF g label c vf phase tau delta
      backgroundLength probeLength a input u z =
    delta • round3ParameterPrimaryWave F hF g input backgroundLength tau z +
      ∑ l, (Real.cos (phase l z/tau) •
        jointGroupedParameterPrescribedAmplitude label F hF c vf tau probeLength a
          false (u z.1) l z -
        Real.sin (phase l z/tau) •
        jointGroupedParameterPrescribedAmplitude label F hF c vf tau probeLength a
          true (u z.1) l z) := by
  simp only [actualProbeInitialGroupedPrimary,Fintype.sum_sum_type,
    actualProbeInitialGroupedAmplitude,Sum.elim_inl,Sum.elim_inr,Bool.not_false,Bool.not_true,
    round3ParameterPrimaryWave,Finset.smul_sum,smul_sub]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [smul_comm (Real.cos _),smul_comm (Real.sin _)]

section OriginalFamily
variable [T2Space M] [CompactSpace M]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "d" => Fintype.card (Fin r × Bool)
local notation "Ep" => EuclideanSpace ℝ (Fin d)

/-- The actual prescribed block of the original family is exactly its
existing physical paired map, before taking any parameter or source jet. -/
theorem probes_original_grouped_primary_eq
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ,V) ∞ F₀)
    (waves : Fin r → LocalLegalWave (n := m+1) F₀ hF₀) (weight : Fin r → ℝ)
    (family : OriginalWaveSeedRescaledFamily F₀ hF₀ waves weight)
    (scale : ℝ) (hscale : scale ∈ Icc (1/2:ℝ) 1)
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β)
      (fun _ : P => scale • F₀))
    (tau delta : ℝ) (backgroundLength probeLength : ℕ)
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : P → Fin d → ℝ) (z : P × M) :
    let F : P → M → V := fun _ => scale • F₀
    let hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b) :=
      fun _ => contMDiff_const_rescale F₀ hF₀ scale
    let c : (l : Fin r) → Fin (family.refinement l).count → P → D → M :=
      fun l s _ => (family.outer l s).spatialChart.symm
    let vf : (l : Fin r) → (s : Fin (family.refinement l).count) →
        (b : P) → (x : D) → normalSpace (I := IM) (F b) (c l s b x) :=
      fun l s _ x => (-(delta*tau)/(weight l)^2) •
      ((family.refinement l).cutoffCoordinates s (0,x) •
        actualRescaledNormal F₀ hF₀ scale (originalWave_contraction_ne_zero scale hscale)
          ((family.outer l s).spatialChart.symm x)
          ((waves l).normal ((family.outer l s).spatialChart.symm x)))
    let phase : Fin r → P × M → ℝ := fun l z => weight l*(waves l).phase z.2
    let a : (l : Fin r) → Fin (family.refinement l).count →
        OpenPartialHomeomorph (P × M) (P × D) :=
      fun l s => passiveParameterChart (P := P) (0 : Z) (family.inner l s).chart
    actualProbeInitialGroupedPrimary F hF g (round4PairedParameterIndex r).toEmbedding
      c vf phase tau delta backgroundLength probeLength a input u z =
      delta • round3ParameterPrimaryWave F hF g input backgroundLength tau z +
      family.physicalPairMap scale hscale delta tau probeLength (u z.1) z := by
  intro F hF c vf phase a
  exact probes_actual_grouped_primary_eq F hF g (round4PairedParameterIndex r).toEmbedding
    c vf phase tau delta backgroundLength probeLength a input u z

variable [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (Fintype.card (Fin r × Bool)))) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (Fintype.card (Fin r × Bool)))) ∞ P]
  [DecidableEq Λ] {Sub : Type*} [Fintype Sub]

/-- On the whole fixed original ball, the actual first map is the reference
plus the exact background, the existing physical prescribed map, and its
own complete signed secondary. This is a whole-spatial-slice identity and
therefore supports the open-ball derivative transport in FirstModel. -/
theorem probes_original_centered_first_map_split
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ,V) ∞ F₀)
    (waves : Fin r → LocalLegalWave (n := m+1) F₀ hF₀) (weight : Fin r → ℝ)
    (family : OriginalWaveSeedRescaledFamily F₀ hF₀ waves weight)
    (scale : ℝ) (hscale : scale ∈ Icc (1/2:ℝ) 1)
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β)
      (fun _ : Z => scale • F₀))
    (tau delta : ℝ) (backgroundLength probeLength secondaryLength iteration : ℕ)
    (target : (s : Z) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (B : BufferedAtlas P Ep) (amplitude : ℝ) (ha : 0 < amplitude)
    (hbuffer : B.buffer ≤ amplitude/
      (‖(EuclideanSpace.equiv (Fin d) ℝ).toContinuousLinearMap‖+1))
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (choice : ActualSecondarySignedRecord (Λ ⊕ Fin r) → Sub →
      Round3ParameterSecondaryChoice P M m)
    (hc : ∀ rec s, Round3ParameterChartPreserves (choice rec s).chart) :
    let Fz : Z → M → V := fun _ => scale • F₀
    let hz : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (Fz b) :=
      fun _ => contMDiff_const_rescale F₀ hF₀ scale
    let F : P → M → V := fun _ => Fz 0
    let hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b) := fun _ => hz 0
    let gp : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F :=
      passiveParameterPrimary (P := P) (0 : Z) Fz g
    let cz : (l : Fin r) → Fin (family.refinement l).count → Z → D → M :=
      fun l s _ => (family.outer l s).spatialChart.symm
    let vz : (l : Fin r) → (s : Fin (family.refinement l).count) →
        (b : Z) → (x : D) → normalSpace (I := IM) (Fz b) (cz l s b x) :=
      fun l s _ x => (-(delta*tau)/(weight l)^2) •
      ((family.refinement l).cutoffCoordinates s (0,x) •
        actualRescaledNormal F₀ hF₀ scale (originalWave_contraction_ne_zero scale hscale)
          ((family.outer l s).spatialChart.symm x)
          ((waves l).normal ((family.outer l s).spatialChart.symm x)))
    let phasez : Fin r → Z × M → ℝ := fun l z => weight l*(waves l).phase z.2
    let az : (l : Fin r) → Fin (family.refinement l).count →
        OpenPartialHomeomorph (Z × M) (Z × D) := fun l s => (family.inner l s).chart
    let c : (l : Fin r) → Fin (family.refinement l).count → P → D → M :=
      fun l s _ => cz l s 0
    let vf : (l : Fin r) → (s : Fin (family.refinement l).count) →
        (b : P) → (x : D) → normalSpace (I := IM) (F b) (c l s b x) :=
      fun l s _ => vz l s 0
    let phase : Fin r → P × M → ℝ := fun l z => phasez l (0,z.2)
    let a : (l : Fin r) → Fin (family.refinement l).count →
        OpenPartialHomeomorph (P × M) (P × D) :=
      fun l s => passiveParameterChart (P := P) (0 : Z) (az l s)
    let globalU : P → Fin d → ℝ := passiveOriginalSmallParameter B amplitude ha b p₀
    let input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x) :=
      passiveGroupedFamilyJointBackground F hF gp
      (round4PairedParameterIndex r).toEmbedding c vf phase tau delta backgroundLength
      probeLength a (fun _ : P => target 0) iteration globalU
    let U : P × M → V := actualProbeInitialGroupedIncrement F hF gp (round4PairedParameterIndex r).toEmbedding
      c vf phase tau delta backgroundLength probeLength secondaryLength a input globalU choice hc
    let secondary : P × M → V := actualParameterSecondarySourceSum F hF
      (actualProbeInitialGroupedSource F hF gp (round4PairedParameterIndex r).toEmbedding
        c vf phase tau delta backgroundLength probeLength a input globalU choice hc) tau secondaryLength
    let probe : (Fin d → ℝ) → (b : Z) → (x : M) →
        LinearMap.BilinForm ℝ (TangentSpace IM x) :=
      jointGroupedParameterPrescribedMean (round4PairedParameterIndex r).toEmbedding
      Fz hz cz vz phasez tau probeLength az
    let background : (Fin d → ℝ) → M → V := jointMixedSeedBackgroundWave (0 : Z) Fz hz g
      backgroundLength tau delta target probe iteration
    ∀ u : ProbeParameters r,
      ‖u‖ < actualRepairParameterRadius (tensorChartFamilyOfAtlas B) → ∀ x : M,
    let point := actualRepairParameterMap (tensorChartFamilyOfAtlas B) b p₀
      (round4PairedParameterReindex r u)
    actualRepairModelFirstDefectFirstMap (fun z : P × M => F₀ z.2) U delta (point,x) =
      Real.sqrt (1-delta^2) • F₀ x +
        delta • background (round4PairedParameterReindex r u) x +
        family.centeredPhysicalPairMap scale hscale delta tau probeLength B amplitude ha b p₀ u x +
        secondary (point,x) := by
  intro Fz hz F hF gp cz vz phasez az c vf phase a globalU input U secondary probe background
    u hu x point
  have hv : ‖round4PairedParameterReindex r u‖ <
      actualRepairParameterRadius (tensorChartFamilyOfAtlas B) := by
    simpa only [LinearIsometryEquiv.norm_map] using hu
  have hprimary := probes_original_grouped_primary_eq F₀ hF₀ waves weight family scale hscale
    gp tau delta backgroundLength probeLength input globalU (point,x)
  have hbackground : round3ParameterPrimaryWave F hF gp input backgroundLength tau (point,x) =
      background (round4PairedParameterReindex r u) x := by
    dsimp only [input]
    rw [jointMixed_grouped_background_moving_binding (0 : Z) Fz hz g
      (round4PairedParameterIndex r).toEmbedding cz vz phasez tau delta
      backgroundLength probeLength az target iteration globalU]
    exact jointMixed_passive_background_original_ball (0 : Z) Fz hz g
      backgroundLength tau delta target probe iteration B amplitude ha hbuffer
      b p₀ hp₀ (round4PairedParameterReindex r u) hv x
  change Real.sqrt (1-delta^2) • F₀ x +
      (actualProbeInitialGroupedPrimary F hF gp (round4PairedParameterIndex r).toEmbedding
        c vf phase tau delta backgroundLength probeLength a input globalU (point,x) +
        secondary (point,x)) = _
  rw [hprimary,hbackground]
  change Real.sqrt (1-delta^2) • F₀ x +
      (delta • background (round4PairedParameterReindex r u) x +
        family.centeredPhysicalPairMap scale hscale delta tau probeLength B amplitude ha b p₀ u x +
        secondary (point,x)) = _
  abel

end OriginalFamily
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.probes_actual_grouped_primary_eq
#print axioms GlobalEmbedding.Continuation.probes_original_grouped_primary_eq
#print axioms GlobalEmbedding.Continuation.probes_original_centered_first_map_split
