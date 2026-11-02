import Probes.Round4PrescribedNativeMeanParity

/-!
# Actual background substitutions on entire native tensor fields

Each step applies the original `incrementsGlobalPrimaryMeanError` to the whole
previous field, retaining every spatial derivative in the canonical finite
source solver. The parameter is external to that operation. No pointwise
finite-dimensional replacement of the background operator is used.

The reflected complete probe mean makes every finite background iterate even.
The exact physical mean residual is the difference of two consecutive actual
mean errors. Analytic reserve and Hessian estimates for these iterates remain
separate obligations; they are not silently assumed or claimed here.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Pspace" => Fin p → ℝ

/-- The literal original finite mean substitution, acting on full fields. -/
def round4ActualBackgroundMeanIterate
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (length : ℕ) (tau delta : ℝ) (target : ((b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))) (probe : Pspace → ((b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))) :
    ℕ → Pspace → ((b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
  | 0 => fun _ => target
  | j+1 => fun u => target - (delta^2)⁻¹ • probe u -
      incrementsGlobalPrimaryMeanError F hF g
        (round4ActualBackgroundMeanIterate F hF g length tau delta target probe j u) length tau

/-- Algebraic induction in the actual full-field recurrence. The concrete
producer of the probe parity is applied below. -/
theorem round4ActualBackgroundMeanIterate_even
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (length : ℕ) (tau delta : ℝ) (target : ((b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))) (probe : Pspace → ((b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)))
    (hprobe : ∀ u, probe (-u) = probe u) (j : ℕ) (u : Pspace) :
    round4ActualBackgroundMeanIterate F hF g length tau delta target probe j (-u) =
      round4ActualBackgroundMeanIterate F hF g length tau delta target probe j u := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [round4ActualBackgroundMeanIterate,hprobe,ih]

/-- The mean residual of the SAME next iterate is exactly the difference of
consecutive actual errors, after restoring the original physical delta squared. -/
theorem round4ActualBackgroundMeanIterate_physical_residual
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (length : ℕ) (tau delta : ℝ) (hdelta : delta ≠ 0)
    (target : ((b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))) (probe : Pspace → ((b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))) (j : ℕ) (u : Pspace) :
    let A := round4ActualBackgroundMeanIterate F hF g length tau delta target probe
    delta^2 • (fun b x => incrementsGlobalPrimaryMean F hF g (A (j+1) u) length tau b x) +
      probe u - delta^2 • target =
      delta^2 • (incrementsGlobalPrimaryMeanError F hF g (A (j+1) u) length tau -
        incrementsGlobalPrimaryMeanError F hF g (A j u) length tau) := by
  intro A
  funext b x
  ext v w
  change delta^2 * incrementsGlobalPrimaryMean F hF g (A (j+1) u) length tau b x v w +
      probe u b x v w - delta^2 * target b x v w =
    delta^2 * ((incrementsGlobalPrimaryMean F hF g (A (j+1) u) length tau b x v w -
      A (j+1) u b x v w) -
      (incrementsGlobalPrimaryMean F hF g (A j u) length tau b x v w - A j u b x v w))
  have ha : A (j+1) u b x v w = target b x v w - (delta^2)⁻¹ * probe u b x v w -
      (incrementsGlobalPrimaryMean F hF g (A j u) length tau b x v w - A j u b x v w) := rfl
  rw [ha]
  field_simp [hdelta]
  <;> ring

/-- Genuine evenness of every native background field driven by the complete
prescribed amplitudes. Only original coefficient/source smoothness is required;
neither output parity nor an abstract correction map is a hypothesis. -/
theorem round4_prescribed_actual_background_iterates_even
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phi : Fin r → Ep × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) (Ep × D))
    (hA : ∀ l, ContDiffOn ℝ ∞ (fun z : Ep × D =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hB : ∀ l, ContDiffOn ℝ ∞ (fun z : Ep × D =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hBR : ∀ l, ContDiffOn ℝ ∞ (fun z : Ep × D => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l z.1) z.2 0 i : V)) (a l).target)
    (hvf : ∀ l, ContDiffOn ℝ ∞ (fun z : Ep × D => (vf l z.1 z.2 : V)) (a l).target)
    (target : ((b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))) (j : ℕ) (u : Pspace) :
    let probe := round4PrescribedNativeMean label F hF c vf phi tau probeLength a
    let A := round4ActualBackgroundMeanIterate F hF g backgroundLength tau delta target probe
    A j (-u) = A j u := by
  intro probe A
  exact round4ActualBackgroundMeanIterate_even F hF g backgroundLength tau delta target probe
    (fun w => round4PrescribedNativeMean_even label F hF c vf phi tau probeLength a hA hB hBR hvf w) j u

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round4ActualBackgroundMeanIterate_even
#print axioms GlobalEmbedding.Continuation.round4ActualBackgroundMeanIterate_physical_residual
#print axioms GlobalEmbedding.Continuation.round4_prescribed_actual_background_iterates_even
