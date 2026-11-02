import Smoothing.WeightedActualOperations
import GlobalEmbedding.Paper.IncrementsSecondaryMode

/-!
# The actual homogeneous probe source and its primitive slow bounds

The source below is literally the original incrementsModeSource with h=0
and the supplied genuine normal amplitude. The true second-form rows retain
their original row weights, including weight one in row 11 and two in mixed
rows. The actual forcing pairing and its native operator norm are reused.
No desired bound on the source is assumed in the main result: it follows
from primitive true-B and normal-amplitude jets on the same joint domain.
-/

noncomputable section
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff

namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Cdata" => Fin (m + 1) → ℂ

/-- Exact original free-normal source, with the original half in the fixed
forcing pairing cancelled by its explicit factor two. -/
theorem actual_homogeneous_source_real_eq
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (chart : D → M)
    (vf : (x : D) → normalSpace (I := I) F (chart x)) (x : D) :
    incrementsModeSource F hF chart (fun _ _ _ => 0) vf x =
      (2 : ℝ) • incrementsModeForcingSourcePairing
        (fun i => (incrementsModeSecondForm F hF chart x 0 i : V)) (vf x : V) := by
  have ht : incrementsModeTransverseSource (fun _ _ _ => (0 : ℝ)) x = 0 := by
    ext q
    simp [incrementsModeTransverseSource]
  ext i
  change incrementsModeSource F hF chart (fun _ _ _ => 0) vf x i =
    2 * incrementsModeForcingSourcePairing
      (fun a => (incrementsModeSecondForm F hF chart x 0 a : V)) (vf x : V) i
  rw [incrementsModeForcingSourcePairing_apply]
  simp only [incrementsModeSource, ht, map_zero, inner_zero_right, mul_zero, sub_zero,
    Submodule.coe_inner]
  refine Fin.cases ?_ (fun a => ?_) i <;> simp [incrementsModeRowWeight] <;> ring

/-- The actual complex source of one real free-normal channel, retaining the
same source used by the original finite mode solver. -/
def actualHomogeneousSource
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (chart : Ep → D → M)
    (vf : (p : Ep) → (x : D) → normalSpace (I := I) (F p) (chart p x)) (z : X) : Cdata :=
  incrementsModeComplexInclude
    (incrementsModeSource (F z.1) (hF z.1) (chart z.1) (fun _ _ _ => 0) (vf z.1) z.2)

theorem actualHomogeneousSource_eq
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (chart : Ep → D → M)
    (vf : (p : Ep) → (x : D) → normalSpace (I := I) (F p) (chart p x)) (z : X) :
    actualHomogeneousSource F hF chart vf z =
      ((2 : ℝ) • incrementsModeComplexInclude)
        (incrementsModeForcingSourcePairing
          (fun i => (incrementsModeSecondForm (F z.1) (hF z.1) (chart z.1) z.2 0 i : V))
          (vf z.1 z.2 : V)) := by
  rw [actualHomogeneousSource, actual_homogeneous_source_real_eq, map_smul]
  rfl

/-- Explicit finite primitive constant. Every coordinate-conversion norm is
retained, and no small scale, atlas cardinality or function is an input. -/
def homogeneousSourceConstant (m N j : ℕ) (MB K : ℝ) : ℝ :=
  ‖(2 : ℝ) • incrementsModeComplexInclude (m := m)‖ * 2 ^ j *
    ‖incrementsModeForcingSourcePairing (m := m) (N := N)‖ * MB * K

theorem homogeneousSourceConstant_nonneg (m N j : ℕ) {MB K : ℝ}
    (hMB : 0 ≤ MB) (hK : 0 ≤ K) : 0 ≤ homogeneousSourceConstant m N j MB K := by
  unfold homogeneousSourceConstant
  positivity

/-- Actual true-B rows and actual normal-amplitude slow jets produce the
weighted bound on the SAME original source. The parameter space Ep is arbitrary.
Set a=delta*tau for the homogeneous probe amplitude. -/
theorem actualHomogeneousSource_weighted_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (chart : Ep → D → M)
    (vf : (p : Ep) → (x : D) → normalSpace (I := I) (F p) (chart p x))
    (O : Set X) (hO : IsOpen O)
    (hB : ContDiffOn ℝ ∞ (fun z : X => fun i : Fin (m + 1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (chart z.1) z.2 0 i : V)) O)
    (hvf : ContDiffOn ℝ ∞ (fun z : X => (vf z.1 z.2 : V)) O)
    (j : ℕ) (ell MB K a : ℝ) (hell : 0 ≤ ell) (hMB : 0 ≤ MB) (hK : 0 ≤ K) (ha : 0 ≤ a)
    (hBb : ∀ k ≤ j, ∀ z ∈ O, ell ^ k * ‖iteratedFDeriv ℝ k
      (fun y : X => fun i : Fin (m + 1) =>
        (incrementsModeSecondForm (F y.1) (hF y.1) (chart y.1) y.2 0 i : V)) z‖ ≤ MB)
    (hvfb : ∀ k ≤ j, ∀ z ∈ O, ell ^ k * ‖iteratedFDeriv ℝ k
      (fun y : X => (vf y.1 y.2 : V)) z‖ ≤ K * a) :
    ContDiffOn ℝ ∞ (actualHomogeneousSource F hF chart vf) O ∧
    ∀ k ≤ j, ∀ z ∈ O, ell ^ k *
      ‖iteratedFDeriv ℝ k (actualHomogeneousSource F hF chart vf) z‖ ≤
        homogeneousSourceConstant m N j MB K * a := by
  let B : X → Fin (m + 1) → V := fun z i =>
    (incrementsModeSecondForm (F z.1) (hF z.1) (chart z.1) z.2 0 i : V)
  let v : X → V := fun z => (vf z.1 z.2 : V)
  let Q := incrementsModeForcingSourcePairing (m := m) (N := N)
  let L := (2 : ℝ) • incrementsModeComplexInclude (m := m)
  let f : X → D := fun z => Q (B z) (v z)
  have hf : ContDiffOn ℝ ∞ f O := (Q.contDiff.comp_contDiffOn hB).clm_apply hvf
  have he : actualHomogeneousSource F hF chart vf = L ∘ f :=
    funext (actualHomogeneousSource_eq F hF chart vf)
  rw [he]
  refine ⟨L.contDiff.comp_contDiffOn hf, ?_⟩
  intro k hk z hz
  have hb := slow_bilinear_jet_bound_norm Q O hO B v hB hvf k ell MB (K * a) hell z hz
    (fun r hr => hBb r (hr.trans hk) z hz) (fun r hr => hvfb r (hr.trans hk) z hz)
  have hp := slow_linear_jet_bound L O hO f hf k ell
    (2 ^ k * (‖Q‖ * MB) * (K * a)) hell z hz hb
  apply hp.trans
  change ‖L‖ * (2 ^ k * (‖Q‖ * MB) * (K * a)) ≤
    ‖L‖ * 2 ^ j * ‖Q‖ * MB * K * a
  calc
    _ = (‖L‖ * ‖Q‖ * MB * K * a) * 2 ^ k := by ring
    _ ≤ (‖L‖ * ‖Q‖ * MB * K * a) * 2 ^ j :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hk) (by positivity)
    _ = _ := by ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_homogeneous_source_real_eq
#print axioms GlobalEmbedding.Continuation.actualHomogeneousSource_weighted_jets
