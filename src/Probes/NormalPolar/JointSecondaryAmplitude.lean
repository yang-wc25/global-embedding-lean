import NormalPolar.ActualRepairModelFirstDefectAmplitude
import Probes.Round4PrescribedGlobalParameterSmooth

/-! The actual common primary array with a variable parameter.

The parameter is a function of the physical parameter point, so spatial
derivatives hold its value fixed, while joint derivatives see every variation.
The array is defined before any choice of a secondary piece. Its support is
derived from the original finite columns, without an output-support premise.
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
  {m N p r : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

def jointSecondaryCombinedAmplitude
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (tau delta : ℝ) (backgroundLength probeLength : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (u : Ep → Fin p → ℝ) (imag : Bool) (l : Λ ⊕ Fin r) (z : Ep × M) : V :=
  round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta
    backgroundLength probeLength a input (u z.1) imag l z

theorem jointSecondary_combined_amplitude_spatial_slice
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (tau delta : ℝ) (backgroundLength probeLength : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (u : Ep → Fin p → ℝ) (imag : Bool) (l : Λ ⊕ Fin r) (b : Ep) :
    (fun x => jointSecondaryCombinedAmplitude F hF g label c vf tau delta
      backgroundLength probeLength a input u imag l (b,x)) =
    (fun x => round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta
      backgroundLength probeLength a input (u b) imag l (b,x)) := rfl

theorem jointSecondary_prescribed_amplitude_support
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Ep → D → M) (chi : X → ℝ)
    (nu : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (a : OpenPartialHomeomorph (Ep × M) X) (W K : Set (Ep × M)) (hW : IsOpen W)
    (n j length : ℕ) (ell Mg Bchi Bnu tau delta weight : ℝ)
    (raw : ActualPrescribedSpatialRawProfiles F hF c chi nu a W K n j ell Mg Bchi Bnu)
    (u : Ep → Fin p → ℝ) :
    let vf := actualProbeNormalAmplitude F c chi nu delta tau weight
    tsupport (fun z : W => round4PrescribedGlobalAmplitude imag label l F hF c vf
      tau length a (u z.val.1) z.val) ⊆ Subtype.val ⁻¹' K := by
  intro vf
  have hvf : ContDiffOn ℝ ∞ (fun z : X => (vf z.1 z.2 : V)) a.target :=
    (raw.cutoff_smooth.smul raw.normal_smooth).const_smul (-(delta*tau)/weight^2)
  have hcolumns (v : Fin p → ℝ) := round4PrescribedGlobalAmplitude_columns imag label l F hF c vf
    tau length a raw.A_smooth raw.B_smooth raw.BR_smooth hvf v
  have he : (fun z : W => round4PrescribedGlobalAmplitude imag label l F hF c vf
      tau length a (u z.val.1) z.val) =
      (fun z : W => ∑ q, u z.val.1 q • round4PrescribedGlobalAmplitude imag label l F hF c vf
        tau length a (Pi.single q 1) z.val) := by
    funext z
    exact congrFun (hcolumns (u z.val.1)) z.val
  rw [he]
  apply actualRepairModelFirstDefect_finite_sum_support
  intro q
  exact (tsupport_smul_subset_right _ _).trans
    (actualRepairModelFirstDefect_prescribed_amplitude_regular imag label l F hF c chi nu a W K hW
      n j length ell Mg Bchi Bnu tau delta weight raw (Pi.single q 1)).2

theorem jointSecondary_common_amplitude_support
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (K : (Λ ⊕ Fin r) → Set (Ep × M))
    (background : ParameterRound2GlobalMeanPrimitives F hF g input W (fun l => K (Sum.inl l)))
    (n j backgroundLength probeLength : ℕ) (ell Mg Bchi Bnu tau delta : ℝ) (weight : Fin r → ℝ)
    (prescribed : ∀ l, ActualPrescribedSpatialRawProfiles F hF (c l) (chi l) (nu l) (a l)
      W (K (Sum.inr l)) n j ell Mg Bchi Bnu)
    (u : Ep → Fin p → ℝ) :
    let vf := fun l => actualProbeNormalAmplitude F (c l) (chi l) (nu l) delta tau (weight l)
    let amplitude := jointSecondaryCombinedAmplitude F hF g label c vf tau delta
      backgroundLength probeLength a input u
    ∀ ch l, tsupport (fun z : W => amplitude ch l z.val) ⊆ Subtype.val ⁻¹' K l := by
  intro vf amplitude ch l
  cases l with
  | inl l =>
    exact (tsupport_smul_subset_right _ _).trans
      (actualRepairModelFirstDefect_background_amplitude_regular F hF g input W
        (fun l => K (Sum.inl l)) background backgroundLength tau (!ch) l).2
  | inr l =>
    exact jointSecondary_prescribed_amplitude_support ch label l F hF (c l) (chi l) (nu l) (a l)
      W (K (Sum.inr l)) background.hW n j probeLength ell Mg Bchi Bnu tau delta (weight l)
      (prescribed l) u

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_common_amplitude_support
