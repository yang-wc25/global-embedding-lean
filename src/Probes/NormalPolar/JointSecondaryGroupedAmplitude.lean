import NormalPolar.JointSecondaryAmplitude
import Probes.Round4PrescribedGlobalWave

/-!
# Actual prescribed amplitudes grouped by the original label

An arbitrary original legal wave may require finitely many adapted charts.
The subordinate index is dependent on the original label and never becomes
a new probe label. Each piece is the complete original finite reconstruction.
Both amplitude channels are summed before any quadratic coefficient is formed.
The same embedding into Fin p is retained, including at chart boundaries.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ} {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

/-- Complete finite reconstructed amplitudes, summed within the original label. -/
def jointGroupedPrescribedAmplitude
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → Ep → D → M)
    (vf : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) →
      normalSpace (I := I) (F b) (c l s b x))
    (tau : ℝ) (length : ℕ)
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) X)
    (u : Fin p → ℝ) (l : Fin r) (z : Ep × M) : V :=
  ∑ s, round4PrescribedGlobalAmplitude imag label l F hF (c l s) (vf l s)
    tau length (a l s) u z

/-- Same-phase real wave of the grouped full amplitudes. -/
def jointGroupedPrescribedWave
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → Ep → D → M)
    (vf : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) →
      normalSpace (I := I) (F b) (c l s b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) X)
    (u : Fin p → ℝ) (z : Ep × M) : V :=
  ∑ l, (Real.cos (phase l z / tau) •
    jointGroupedPrescribedAmplitude false label F hF c vf tau length a u l z -
    Real.sin (phase l z / tau) •
    jointGroupedPrescribedAmplitude true label F hF c vf tau length a u l z)

theorem jointGroupedPrescribedWave_eq_piece_sum
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → Ep → D → M)
    (vf : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) →
      normalSpace (I := I) (F b) (c l s b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) X)
    (u : Fin p → ℝ) (z : Ep × M) :
    jointGroupedPrescribedWave label F hF c vf phase tau length a u z =
      ∑ l, ∑ s, (Real.cos (phase l z / tau) •
        round4PrescribedGlobalAmplitude false label l F hF (c l s) (vf l s)
          tau length (a l s) u z -
        Real.sin (phase l z / tau) •
        round4PrescribedGlobalAmplitude true label l F hF (c l s) (vf l s)
          tau length (a l s) u z) := by
  simp only [jointGroupedPrescribedWave,jointGroupedPrescribedAmplitude,
    Finset.smul_sum,Finset.sum_sub_distrib]

/-- Actual reconstruction columns retain exactly the original Fin p. -/
theorem jointGroupedPrescribedAmplitude_columns
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → Ep → D → M)
    (vf : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) →
      normalSpace (I := I) (F b) (c l s b x))
    (tau : ℝ) (length : ℕ)
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) X)
    (hA : ∀ l s, ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l s z.1) z.2) (a l s).target)
    (hB : ∀ l s, ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l s z.1) z.2) (a l s).target)
    (hBR : ∀ l s, ContDiffOn ℝ ∞ (fun z : X => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l s z.1) z.2 0 i : V)) (a l s).target)
    (hvf : ∀ l s, ContDiffOn ℝ ∞ (fun z : X => (vf l s z.1 z.2 : V)) (a l s).target)
    (u : Fin p → ℝ) (l : Fin r) :
    jointGroupedPrescribedAmplitude imag label F hF c vf tau length a u l =
      fun z => ∑ q, u q • jointGroupedPrescribedAmplitude imag label F hF c vf
        tau length a (Pi.single q 1) l z := by
  funext z
  simp only [jointGroupedPrescribedAmplitude]
  calc
    _ = ∑ s, ∑ q, u q • round4PrescribedGlobalAmplitude imag label l F hF
        (c l s) (vf l s) tau length (a l s) (Pi.single q 1) z := by
      apply Finset.sum_congr rfl
      intro s _
      exact congrFun (round4PrescribedGlobalAmplitude_columns imag label l F hF
        (c l s) (vf l s) tau length (a l s) (hA l s) (hB l s) (hBR l s) (hvf l s) u) z
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.smul_sum]

/-- Global regularity and the original support follow from each actual raw
piece. The original carrier K may contain all subordinate carriers without
requiring a single adapted chart to contain K. -/
theorem jointGroupedPrescribedAmplitude_regular_from_raw
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → Ep → D → M)
    (chi : (l : Fin r) → Sub l → X → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) →
      normalSpace (I := I) (F b) (c l s b x))
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M))
    (pieceK : (l : Fin r) → Sub l → Set (Ep × M))
    (hW : IsOpen W) (hK : ∀ l s, pieceK l s ⊆ K l)
    (n j length : ℕ) (ell Mg Bchi Bnu tau delta : ℝ) (weight : Fin r → ℝ)
    (raw : ∀ l s, ActualPrescribedSpatialRawProfiles F hF (c l s) (chi l s) (nu l s)
      (a l s) W (pieceK l s) n j ell Mg Bchi Bnu)
    (u : Fin p → ℝ) (l : Fin r) :
    let vf := fun l s => actualProbeNormalAmplitude F (c l s) (chi l s) (nu l s) delta tau (weight l)
    let amp := jointGroupedPrescribedAmplitude imag label F hF c vf tau length a u l
    ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,V) ∞ amp W ∧
      tsupport (fun z : W => amp z.val) ⊆ Subtype.val ⁻¹' K l := by
  intro vf amp
  have hp s := actualRepairModelFirstDefect_prescribed_amplitude_regular imag label l
    F hF (c l s) (chi l s) (nu l s) (a l s) W (pieceK l s) hW
    n j length ell Mg Bchi Bnu tau delta (weight l) (raw l s) u
  refine ⟨contMDiffOn_finsetSum (fun s _ => (hp s).1),?_⟩
  apply actualRepairModelFirstDefect_finite_sum_support
  intro s z hz
  exact hK l s ((hp s).2 hz)

/-- Variable parameter support uses the actual fixed columns before any joint
derivative; it does not select a fixed-parameter existence witness. -/
theorem jointGroupedPrescribedAmplitude_variable_support
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → Ep → D → M)
    (chi : (l : Fin r) → Sub l → X → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) →
      normalSpace (I := I) (F b) (c l s b x))
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M))
    (pieceK : (l : Fin r) → Sub l → Set (Ep × M))
    (hW : IsOpen W) (hK : ∀ l s, pieceK l s ⊆ K l)
    (n j length : ℕ) (ell Mg Bchi Bnu tau delta : ℝ) (weight : Fin r → ℝ)
    (raw : ∀ l s, ActualPrescribedSpatialRawProfiles F hF (c l s) (chi l s) (nu l s)
      (a l s) W (pieceK l s) n j ell Mg Bchi Bnu)
    (u : Ep → Fin p → ℝ) (l : Fin r) :
    let vf := fun l s => actualProbeNormalAmplitude F (c l s) (chi l s) (nu l s) delta tau (weight l)
    tsupport (fun z : W => jointGroupedPrescribedAmplitude imag label F hF c vf
      tau length a (u z.val.1) l z.val) ⊆ Subtype.val ⁻¹' K l := by
  intro vf
  apply actualRepairModelFirstDefect_finite_sum_support
  intro s z hz
  exact hK l s ((jointSecondary_prescribed_amplitude_support imag label l F hF
    (c l s) (chi l s) (nu l s) (a l s) W (pieceK l s) hW n j length
    ell Mg Bchi Bnu tau delta (weight l) (raw l s) u) hz)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.jointGroupedPrescribedWave_eq_piece_sum
#print axioms GlobalEmbedding.Continuation.jointGroupedPrescribedAmplitude_columns
#print axioms GlobalEmbedding.Continuation.jointGroupedPrescribedAmplitude_regular_from_raw
#print axioms GlobalEmbedding.Continuation.jointGroupedPrescribedAmplitude_variable_support
