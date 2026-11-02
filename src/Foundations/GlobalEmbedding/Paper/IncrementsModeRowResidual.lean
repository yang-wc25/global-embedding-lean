import GlobalEmbedding.Paper.IncrementsModeFullReconstruction
import GlobalEmbedding.Paper.IncrementsComplexLinearizedMetric
import GlobalEmbedding.Paper.IncrementsModeCoordinateRegularity

/-!
# Original geometric row factors for the actual mode residual

Source: `main.tex`, lem:increments617–643, equation (6.2). Actual source, T, J,
normal fibers and reduced operator are reused. No desired PDE or metric residual
identity is assumed, and no R or J constructor is introduced.
-/

noncomputable section
open Manifold Filter
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "Cdata" => Fin (m + 1) → ℂ
local notation "P" => {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

/-- The ORIGINAL reconstructed 11 row has twice the reduced residual. The source
half-factor and the included J h_H term are the canonical actual expressions. -/
theorem increments_mode_reconstructed_first_row
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M)
    (u : D → D) (h : D → Fin (m + 1) → Fin (m + 1) → ℝ)
    (vf : (y : D) → normalSpace (I := I) F (c y)) (x : D) :
    let J := incrementsModeCoordinateJ F hF c x
    let ν := vf x + J (incrementsModeTransverseTensor F c u x) -
      (1 / 2 : ℝ) • J (incrementsModeTransverseSource h x)
    (fderiv ℝ u x (EuclideanSpace.single 0 1)) 0 +
        (fderiv ℝ u x (EuclideanSpace.single 0 1)) 0 -
        2 * inner ℝ (incrementsModeGamma F c x 0 0) (u x) -
        2 * inner ℝ (incrementsModeSecondForm F hF c x 0 0) ν - h x 0 0 =
      2 * (incrementsModeReducedOperator F hF c u x 0 -
        incrementsModeSource F hF c h vf x 0) := by
  dsimp only
  rw [incrementsModeSource_first]
  simp only [incrementsModeReducedOperator, incrementsModeRowWeight, Fin.cases_zero,
    inner_sub_right, inner_add_right]
  rw [real_inner_smul_right (incrementsModeSecondForm F hF c x 0 0)
    (incrementsModeCoordinateJ F hF c x (incrementsModeTransverseSource h x)) (1 / 2)]
  ring

/-- The ORIGINAL mixed row has factor one. In particular the mixed source uses
minus ONE on J h_H; it is not silently changed to the 11 half-factor. -/
theorem increments_mode_reconstructed_mixed_row
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M)
    (u : D → D) (h : D → Fin (m + 1) → Fin (m + 1) → ℝ)
    (vf : (y : D) → normalSpace (I := I) F (c y)) (x : D) (a : Fin m) :
    let J := incrementsModeCoordinateJ F hF c x
    let ν := vf x + J (incrementsModeTransverseTensor F c u x) -
      (1 / 2 : ℝ) • J (incrementsModeTransverseSource h x)
    (fderiv ℝ u x (EuclideanSpace.single 0 1)) a.succ +
        (fderiv ℝ u x (EuclideanSpace.single a.succ 1)) 0 -
        2 * inner ℝ (incrementsModeGamma F c x 0 a.succ) (u x) -
        2 * inner ℝ (incrementsModeSecondForm F hF c x 0 a.succ) ν - h x 0 a.succ =
      incrementsModeReducedOperator F hF c u x a.succ -
        incrementsModeSource F hF c h vf x a.succ := by
  dsimp only
  rw [incrementsModeSource_mixed]
  simp only [incrementsModeReducedOperator, incrementsModeRowWeight, Fin.cases_succ,
    inner_sub_right, inner_add_right]
  rw [real_inner_smul_right (incrementsModeSecondForm F hF c x 0 a.succ)
    (incrementsModeCoordinateJ F hF c x (incrementsModeTransverseSource h x)) (1 / 2)]
  ring

/-- Every original once-sorted transverse row, INCLUDING diagonals, vanishes by
the accepted actual normal reconstruction. The input is the original beta Gram
invertibility and free-normal condition, not a desired right-inverse/PDE identity. -/
theorem increments_mode_reconstructed_transverse_row
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M)
    (u : D → D) (h : D → Fin (m + 1) → Fin (m + 1) → ℝ)
    (vf : (y : D) → normalSpace (I := I) F (c y)) (x : D)
    (hG : ((incrementsTransversePairing F hF (c x)
      (fun a ↦ incrementsModeCoordinateDirections c x a.succ)).comp
      (incrementsTransversePairing F hF (c x)
        (fun a ↦ incrementsModeCoordinateDirections c x a.succ)).adjoint).IsInvertible)
    (hfree : incrementsTransversePairing F hF (c x)
      (fun a ↦ incrementsModeCoordinateDirections c x a.succ) (vf x) = 0) (q : P) :
    let J := incrementsModeCoordinateJ F hF c x
    let ν := vf x + J (incrementsModeTransverseTensor F c u x) -
      (1 / 2 : ℝ) • J (incrementsModeTransverseSource h x)
    (fderiv ℝ u x (EuclideanSpace.single q.val.1.succ 1)) q.val.2.succ +
        (fderiv ℝ u x (EuclideanSpace.single q.val.2.succ 1)) q.val.1.succ -
        2 * inner ℝ (incrementsModeGamma F c x q.val.1.succ q.val.2.succ) (u x) -
        2 * inner ℝ (incrementsModeSecondForm F hF c x q.val.1.succ q.val.2.succ) ν -
        h x q.val.1.succ q.val.2.succ = 0 := by
  have ht := increments_actual_transverse_reconstruction F hF (c x)
    (fun a ↦ incrementsModeCoordinateDirections c x a.succ) hG (vf x) hfree
    (incrementsModeTransverseTensor F c u x) (incrementsModeTransverseSource h x) q
  change 2 *
    (((fderiv ℝ u x (EuclideanSpace.single q.val.1.succ 1)) q.val.2.succ +
      (fderiv ℝ u x (EuclideanSpace.single q.val.2.succ 1)) q.val.1.succ) / 2 -
      inner ℝ (incrementsModeGamma F c x q.val.1.succ q.val.2.succ) (u x) -
      inner ℝ (incrementsModeSecondForm F hF c x q.val.1.succ q.val.2.succ)
        (vf x + incrementsModeCoordinateJ F hF c x
          (incrementsModeTransverseTensor F c u x) - (1 / 2 : ℝ) •
          incrementsModeCoordinateJ F hF c x (incrementsModeTransverseSource h x))) -
      h x q.val.1.succ q.val.2.succ = 0 at ht
  dsimp only
  linarith


/-- Native complex packing of the actual reconstructed first row. The phase term
has the original row factor two; the source is the SAME two actual real channels. -/
theorem increments_mode_complex_first_row
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M)
    (u : D → Cdata) (α : ℂ)
    (hR hI : D → Fin (m + 1) → Fin (m + 1) → ℝ)
    (vfR vfI : (y : D) → normalSpace (I := I) F (c y)) (x : D) :
    let uR := fun y ↦ incrementsModeRealPart (u y)
    let uI := fun y ↦ incrementsModeImagPart (u y)
    let J := incrementsModeCoordinateJ F hF c x
    let νR := vfR x + J (incrementsModeTransverseTensor F c uR x) -
      (1 / 2 : ℝ) • J (incrementsModeTransverseSource hR x)
    let νI := vfI x + J (incrementsModeTransverseTensor F c uI x) -
      (1 / 2 : ℝ) • J (incrementsModeTransverseSource hI x)
    let k := incrementsModeComplexInclude (incrementsModeSource F hF c hR vfR x) +
      Complex.I • incrementsModeComplexInclude (incrementsModeSource F hF c hI vfI x)
    (((fderiv ℝ uR x (EuclideanSpace.single 0 1)) 0 +
        (fderiv ℝ uR x (EuclideanSpace.single 0 1)) 0 -
        2 * inner ℝ (incrementsModeGamma F c x 0 0) (uR x) -
        2 * inner ℝ (incrementsModeSecondForm F hF c x 0 0) νR - hR x 0 0 : ℝ) : ℂ) +
      Complex.I * (((fderiv ℝ uI x (EuclideanSpace.single 0 1)) 0 +
        (fderiv ℝ uI x (EuclideanSpace.single 0 1)) 0 -
        2 * inner ℝ (incrementsModeGamma F c x 0 0) (uI x) -
        2 * inner ℝ (incrementsModeSecondForm F hF c x 0 0) νI - hI x 0 0 : ℝ) : ℂ) +
      2 * α⁻¹ * u x 0 =
        2 * ((α⁻¹ • u x + incrementsModeComplexReducedOperator F hF c u x - k) 0) := by
  dsimp only
  rw [increments_mode_reconstructed_first_row F hF c _ hR vfR x,
    increments_mode_reconstructed_first_row F hF c _ hI vfI x]
  let lr := incrementsModeReducedOperator F hF c
    (fun y ↦ incrementsModeRealPart (u y)) x 0
  let li := incrementsModeReducedOperator F hF c
    (fun y ↦ incrementsModeImagPart (u y)) x 0
  let kr := incrementsModeSource F hF c hR vfR x 0
  let ki := incrementsModeSource F hF c hI vfI x 0
  change ((2 * (lr - kr) : ℝ) : ℂ) + Complex.I * ((2 * (li - ki) : ℝ) : ℂ) +
    2 * α⁻¹ * u x 0 = 2 * (α⁻¹ * u x 0 + ((lr : ℂ) + Complex.I * (li : ℂ)) -
      ((kr : ℂ) + Complex.I * (ki : ℂ)))
  push_cast
  ring

/-- Native complex packing of the actual reconstructed mixed row. The phase term
has the original row factor one; the source is the SAME two actual real channels. -/
theorem increments_mode_complex_mixed_row
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M)
    (u : D → Cdata) (α : ℂ)
    (hR hI : D → Fin (m + 1) → Fin (m + 1) → ℝ)
    (vfR vfI : (y : D) → normalSpace (I := I) F (c y)) (x : D) (a : Fin m) :
    let uR := fun y ↦ incrementsModeRealPart (u y)
    let uI := fun y ↦ incrementsModeImagPart (u y)
    let J := incrementsModeCoordinateJ F hF c x
    let νR := vfR x + J (incrementsModeTransverseTensor F c uR x) -
      (1 / 2 : ℝ) • J (incrementsModeTransverseSource hR x)
    let νI := vfI x + J (incrementsModeTransverseTensor F c uI x) -
      (1 / 2 : ℝ) • J (incrementsModeTransverseSource hI x)
    let k := incrementsModeComplexInclude (incrementsModeSource F hF c hR vfR x) +
      Complex.I • incrementsModeComplexInclude (incrementsModeSource F hF c hI vfI x)
    (((fderiv ℝ uR x (EuclideanSpace.single 0 1)) a.succ +
        (fderiv ℝ uR x (EuclideanSpace.single a.succ 1)) 0 -
        2 * inner ℝ (incrementsModeGamma F c x 0 a.succ) (uR x) -
        2 * inner ℝ (incrementsModeSecondForm F hF c x 0 a.succ) νR - hR x 0 a.succ : ℝ) : ℂ) +
      Complex.I * (((fderiv ℝ uI x (EuclideanSpace.single 0 1)) a.succ +
        (fderiv ℝ uI x (EuclideanSpace.single a.succ 1)) 0 -
        2 * inner ℝ (incrementsModeGamma F c x 0 a.succ) (uI x) -
        2 * inner ℝ (incrementsModeSecondForm F hF c x 0 a.succ) νI - hI x 0 a.succ : ℝ) : ℂ) +
      α⁻¹ * u x a.succ =
        ((α⁻¹ • u x + incrementsModeComplexReducedOperator F hF c u x - k) a.succ) := by
  dsimp only
  rw [increments_mode_reconstructed_mixed_row F hF c _ hR vfR x a,
    increments_mode_reconstructed_mixed_row F hF c _ hI vfI x a]
  let lr := incrementsModeReducedOperator F hF c
    (fun y ↦ incrementsModeRealPart (u y)) x a.succ
  let li := incrementsModeReducedOperator F hF c
    (fun y ↦ incrementsModeImagPart (u y)) x a.succ
  let kr := incrementsModeSource F hF c hR vfR x a.succ
  let ki := incrementsModeSource F hF c hI vfI x a.succ
  change ((lr - kr : ℝ) : ℂ) + Complex.I * ((li - ki : ℝ) : ℂ) +
    α⁻¹ * u x a.succ = α⁻¹ * u x a.succ + ((lr : ℂ) + Complex.I * (li : ℂ)) -
      ((kr : ℂ) + Complex.I * (ki : ℂ))
  push_cast
  ring


/-- Both actual real channels give zero in every original sorted transverse row.
No conjugation phase term occurs in these adapted transverse directions. -/
theorem increments_mode_complex_transverse_row
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M)
    (u : D → Cdata) (hR hI : D → Fin (m + 1) → Fin (m + 1) → ℝ)
    (vfR vfI : (y : D) → normalSpace (I := I) F (c y)) (x : D)
    (hG : ((incrementsTransversePairing F hF (c x)
      (fun a ↦ incrementsModeCoordinateDirections c x a.succ)).comp
      (incrementsTransversePairing F hF (c x)
        (fun a ↦ incrementsModeCoordinateDirections c x a.succ)).adjoint).IsInvertible)
    (hfreeR : incrementsTransversePairing F hF (c x)
      (fun a ↦ incrementsModeCoordinateDirections c x a.succ) (vfR x) = 0)
    (hfreeI : incrementsTransversePairing F hF (c x)
      (fun a ↦ incrementsModeCoordinateDirections c x a.succ) (vfI x) = 0) (q : P) :
    let uR := fun y ↦ incrementsModeRealPart (u y)
    let uI := fun y ↦ incrementsModeImagPart (u y)
    let J := incrementsModeCoordinateJ F hF c x
    let νR := vfR x + J (incrementsModeTransverseTensor F c uR x) -
      (1 / 2 : ℝ) • J (incrementsModeTransverseSource hR x)
    let νI := vfI x + J (incrementsModeTransverseTensor F c uI x) -
      (1 / 2 : ℝ) • J (incrementsModeTransverseSource hI x)
    (((fderiv ℝ uR x (EuclideanSpace.single q.val.1.succ 1)) q.val.2.succ +
        (fderiv ℝ uR x (EuclideanSpace.single q.val.2.succ 1)) q.val.1.succ -
        2 * inner ℝ (incrementsModeGamma F c x q.val.1.succ q.val.2.succ) (uR x) -
        2 * inner ℝ (incrementsModeSecondForm F hF c x q.val.1.succ q.val.2.succ) νR -
        hR x q.val.1.succ q.val.2.succ : ℝ) : ℂ) +
      Complex.I * (((fderiv ℝ uI x (EuclideanSpace.single q.val.1.succ 1)) q.val.2.succ +
        (fderiv ℝ uI x (EuclideanSpace.single q.val.2.succ 1)) q.val.1.succ -
        2 * inner ℝ (incrementsModeGamma F c x q.val.1.succ q.val.2.succ) (uI x) -
        2 * inner ℝ (incrementsModeSecondForm F hF c x q.val.1.succ q.val.2.succ) νI -
        hI x q.val.1.succ q.val.2.succ : ℝ) : ℂ) = 0 := by
  dsimp only
  rw [increments_mode_reconstructed_transverse_row F hF c _ hR vfR x hG hfreeR q,
    increments_mode_reconstructed_transverse_row F hF c _ hI vfI x hG hfreeI q]
  simp

end GlobalEmbedding.Paper

namespace GlobalEmbedding.Paper

section ActualChart

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ, D)
local notation "Cdata" => Fin (m + 1) → ℂ

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) M]

/-- The accepted literal metric conjugation, in the SAME original inverse chart,
uses exactly the canonical true B and Gamma of the row identities above. The
adapted phase is the actual first coordinate, so its phase term is the true delta
term. This only transports accepted geometric identities; no new reconstruction,
normal inverse, metric or differential-solver definition is introduced. -/
theorem increments_mode_physical_metric_row
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (y : M)
    (Ω : Set D) (hΩ : IsOpen Ω) (hΩt : Ω ⊆ (extChartAt 𝓙 y).target)
    (hinj : ∀ z ∈ Ω, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ, V) F ((extChartAt 𝓙 y).symm z)))
    (u : D → Cdata)
    (νR νI : (z : D) → normalSpace (I := 𝓙) F ((extChartAt 𝓙 y).symm z))
    (τ : ℝ) (x : D) (hx : x ∈ Ω) (hu : DifferentiableAt ℝ u x)
    (hνR : DifferentiableAt ℝ (fun z ↦ (νR z : V)) x)
    (hνI : DifferentiableAt ℝ (fun z ↦ (νI z : V)) x) (i j : Fin (m + 1)) :
    let c := (extChartAt 𝓙 y).symm
    let uR := fun z ↦ incrementsModeRealPart (u z)
    let uI := fun z ↦ incrementsModeImagPart (u z)
    let P := fun z ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) z) (uR z) + (νR z : V)
    let Q := fun z ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) z) (uI z) + (νI z : V)
    let R := fun z ↦ WithLp.toLp 2 (fun a : Fin N ↦
      (Complex.exp (((z 0 / τ : ℝ) : ℂ) * Complex.I) *
        ((P z a : ℂ) + Complex.I * (Q z a : ℂ))).re)
    let S := fun z ↦ WithLp.toLp 2 (fun a : Fin N ↦
      (Complex.exp (((z 0 / τ : ℝ) : ℂ) * Complex.I) *
        ((P z a : ℂ) + Complex.I * (Q z a : ℂ))).im)
    Complex.exp (-((x 0 / τ : ℝ) : ℂ) * Complex.I) *
        ((incrementsCoordinateMetricVariation (F ∘ c) R x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ) +
          Complex.I * (incrementsCoordinateMetricVariation (F ∘ c) S x
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ)) =
      ((fderiv ℝ uR x (EuclideanSpace.single i 1)) j +
        (fderiv ℝ uR x (EuclideanSpace.single j 1)) i -
        2 * inner ℝ (incrementsModeGamma F c x i j) (uR x) -
        2 * inner ℝ (incrementsModeSecondForm F hF c x i j) (νR x) : ℝ) +
      Complex.I * ((fderiv ℝ uI x (EuclideanSpace.single i 1)) j +
        (fderiv ℝ uI x (EuclideanSpace.single j 1)) i -
        2 * inner ℝ (incrementsModeGamma F c x i j) (uI x) -
        2 * inner ℝ (incrementsModeSecondForm F hF c x i j) (νI x) : ℝ) +
      (Complex.I / (τ : ℂ)) *
        ((if i = 0 then u x j else 0) + (if j = 0 then u x i else 0)) := by
  let c := (extChartAt 𝓙 y).symm
  let uR := fun z ↦ incrementsModeRealPart (u z)
  let uI := fun z ↦ incrementsModeImagPart (u z)
  have hFc : ContDiffOn ℝ ∞ (F ∘ c) Ω :=
    ((hF.comp_contMDiffOn (contMDiffOn_extChartAt_symm y)).contDiffOn).mono hΩt
  have hcInj : ∀ z ∈ Ω, Function.Injective (fderiv ℝ (F ∘ c) z) := by
    intro z hz
    exact fixed_chart_derivative_injective F y z (hΩt hz)
      (hF.mdifferentiable (by simp) _) (hinj z hz)
  have hnR : ∀ z ∈ Ω,
      (νR z : V) ∈ (LinearMap.range (fderiv ℝ (F ∘ c) z).toLinearMap)ᗮ := by
    intro z hz
    rw [← normalSpace_eq_fixed_chart_range_orthogonal F y z (hΩt hz)
      (hF.mdifferentiable (by simp) _)]
    exact (νR z).property
  have hnI : ∀ z ∈ Ω,
      (νI z : V) ∈ (LinearMap.range (fderiv ℝ (F ∘ c) z).toLinearMap)ᗮ := by
    intro z hz
    rw [← normalSpace_eq_fixed_chart_range_orthogonal F y z (hΩt hz)
      (hF.mdifferentiable (by simp) _)]
    exact (νI z).property
  have huR : DifferentiableAt ℝ uR x := incrementsModeRealPart.differentiableAt.comp x hu
  have huI : DifferentiableAt ℝ uI x := incrementsModeImagPart.differentiableAt.comp x hu
  have hψ : DifferentiableAt ℝ (fun z : D ↦ z 0) x :=
    (EuclideanSpace.proj (0 : Fin (m + 1)) : D →L[ℝ] ℝ).differentiableAt
  have hd (a : Fin (m + 1)) :
      fderiv ℝ (fun z : D ↦ z 0) x (EuclideanSpace.single a 1) =
        if a = 0 then 1 else 0 := by
    have hproj : fderiv ℝ (fun z : D ↦ z 0) x =
        (EuclideanSpace.proj (0 : Fin (m + 1)) : D →L[ℝ] ℝ) :=
      (EuclideanSpace.proj (0 : Fin (m + 1)) : D →L[ℝ] ℝ).hasFDerivAt.fderiv
    rw [hproj]
    simp [EuclideanSpace.proj, PiLp.single_apply, eq_comm]
  have hp (a : Fin (m + 1)) : (uR x a : ℂ) + Complex.I * (uI x a : ℂ) = u x a := by
    change ((u x a).re : ℂ) + Complex.I * ((u x a).im : ℂ) = u x a
    simpa only [mul_comm] using Complex.re_add_im (u x a)
  have hb := incrementsModeSecondForm_chart F hF y x (hΩt hx) i j
  conv_rhs at hb =>
    rw [normalSpace_eq_fixed_chart_range_orthogonal F y x (hΩt hx)
      (hF.mdifferentiable (by simp) _)]
  have hm := increments_complex_linearized_metric Ω hΩ (F ∘ c) hFc hcInj uR uI
    (fun z ↦ (νR z : V)) (fun z ↦ (νI z : V)) hnR hnI (fun z ↦ z 0) τ x hx
    huR huI hνR hνI hψ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  dsimp only at hm
  rw [← hb] at hm
  simp only [EuclideanSpace.inner_single_right, conj_trivial, one_mul] at hm
  rw [hp j, hp i, hd i, hd j] at hm
  refine hm.trans ?_
  dsimp only [uR, uI, c, incrementsModeGamma]
  simp only [Submodule.coe_inner]
  split_ifs <;> push_cast <;> ring


/-- ORIGINAL actual physical metric errors of the SAME normal reconstruction are
2e in row11, e in mixed rows, and zero in every once-sorted transverse row. Here e
is the literal reduced expression, not a supplied PDE or output identity. Only
actual differentiability of the reconstructed normal fields is an upstream
regularity input. No R/J construction or geometric estimate is duplicated. -/
theorem increments_mode_physical_residual_rows
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (y : M)
    (Ω : Set D) (hΩ : IsOpen Ω) (hΩt : Ω ⊆ (extChartAt 𝓙 y).target)
    (hinj : ∀ z ∈ Ω, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ, V) F ((extChartAt 𝓙 y).symm z)))
    (u : D → Cdata) (hR hI : D → Fin (m + 1) → Fin (m + 1) → ℝ)
    (vfR vfI : (z : D) → normalSpace (I := 𝓙) F ((extChartAt 𝓙 y).symm z))
    (τ : ℝ) (x : D) (hx : x ∈ Ω) (hu : DifferentiableAt ℝ u x)
    (hG : ((incrementsTransversePairing F hF ((extChartAt 𝓙 y).symm x)
      (fun a ↦ incrementsModeCoordinateDirections (extChartAt 𝓙 y).symm x a.succ)).comp
      (incrementsTransversePairing F hF ((extChartAt 𝓙 y).symm x)
        (fun a ↦
          incrementsModeCoordinateDirections (extChartAt 𝓙 y).symm x a.succ)).adjoint).IsInvertible)
    (hfreeR : incrementsTransversePairing F hF ((extChartAt 𝓙 y).symm x)
      (fun a ↦ incrementsModeCoordinateDirections (extChartAt 𝓙 y).symm x a.succ)
      (vfR x) = 0)
    (hfreeI : incrementsTransversePairing F hF ((extChartAt 𝓙 y).symm x)
      (fun a ↦ incrementsModeCoordinateDirections (extChartAt 𝓙 y).symm x a.succ)
      (vfI x) = 0) :
    let c := (extChartAt 𝓙 y).symm
    let uR := fun z ↦ incrementsModeRealPart (u z)
    let uI := fun z ↦ incrementsModeImagPart (u z)
    let νR := fun z ↦ vfR z + incrementsModeCoordinateJ F hF c z
      (incrementsModeTransverseTensor F c uR z) - (1 / 2 : ℝ) •
      incrementsModeCoordinateJ F hF c z (incrementsModeTransverseSource hR z)
    let νI := fun z ↦ vfI z + incrementsModeCoordinateJ F hF c z
      (incrementsModeTransverseTensor F c uI z) - (1 / 2 : ℝ) •
      incrementsModeCoordinateJ F hF c z (incrementsModeTransverseSource hI z)
    DifferentiableAt ℝ (fun z ↦ (νR z : V)) x →
    DifferentiableAt ℝ (fun z ↦ (νI z : V)) x →
    let ZR := incrementsModeFullReconstruction F hF c uR hR vfR
    let ZI := incrementsModeFullReconstruction F hF c uI hI vfI
    let WR := fun z ↦ WithLp.toLp 2 (fun a : Fin N ↦
      (Complex.exp (((z 0 / τ : ℝ) : ℂ) * Complex.I) *
        ((ZR z a : ℂ) + Complex.I * (ZI z a : ℂ))).re)
    let WI := fun z ↦ WithLp.toLp 2 (fun a : Fin N ↦
      (Complex.exp (((z 0 / τ : ℝ) : ℂ) * Complex.I) *
        ((ZR z a : ℂ) + Complex.I * (ZI z a : ℂ))).im)
    let err := fun i j ↦ Complex.exp (-((x 0 / τ : ℝ) : ℂ) * Complex.I) *
      ((incrementsCoordinateMetricVariation (F ∘ c) WR x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ) +
        Complex.I * (incrementsCoordinateMetricVariation (F ∘ c) WI x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ)) -
      ((hR x i j : ℂ) + Complex.I * (hI x i j : ℂ))
    let k := incrementsModeComplexInclude (incrementsModeSource F hF c hR vfR x) +
      Complex.I • incrementsModeComplexInclude (incrementsModeSource F hF c hI vfI x)
    let e := (((τ : ℂ) / Complex.I)⁻¹ • u x) +
      incrementsModeComplexReducedOperator F hF c u x - k
    err 0 0 = 2 * e 0 ∧ (∀ a : Fin m, err 0 a.succ = e a.succ) ∧
      ∀ q : {p : Fin m × Fin m // p.1 ≤ p.2}, err q.val.1.succ q.val.2.succ = 0 := by
  dsimp only
  let c := (extChartAt 𝓙 y).symm
  let uR := fun z ↦ incrementsModeRealPart (u z)
  let uI := fun z ↦ incrementsModeImagPart (u z)
  let νR := fun z ↦ vfR z + incrementsModeCoordinateJ F hF c z
      (incrementsModeTransverseTensor F c uR z) - (1 / 2 : ℝ) •
      incrementsModeCoordinateJ F hF c z (incrementsModeTransverseSource hR z)
  let νI := fun z ↦ vfI z + incrementsModeCoordinateJ F hF c z
      (incrementsModeTransverseTensor F c uI z) - (1 / 2 : ℝ) •
      incrementsModeCoordinateJ F hF c z (incrementsModeTransverseSource hI z)
  intro hνR hνI
  let ZR := incrementsModeFullReconstruction F hF c uR hR vfR
  let ZI := incrementsModeFullReconstruction F hF c uI hI vfI
  let WR := fun z ↦ WithLp.toLp 2 (fun a : Fin N ↦
    (Complex.exp (((z 0 / τ : ℝ) : ℂ) * Complex.I) *
      ((ZR z a : ℂ) + Complex.I * (ZI z a : ℂ))).re)
  let WI := fun z ↦ WithLp.toLp 2 (fun a : Fin N ↦
    (Complex.exp (((z 0 / τ : ℝ) : ℂ) * Complex.I) *
      ((ZR z a : ℂ) + Complex.I * (ZI z a : ℂ))).im)
  let err := fun i j ↦ Complex.exp (-((x 0 / τ : ℝ) : ℂ) * Complex.I) *
    ((incrementsCoordinateMetricVariation (F ∘ c) WR x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ) +
      Complex.I * (incrementsCoordinateMetricVariation (F ∘ c) WI x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ)) -
    ((hR x i j : ℂ) + Complex.I * (hI x i j : ℂ))
  let k := incrementsModeComplexInclude (incrementsModeSource F hF c hR vfR x) +
    Complex.I • incrementsModeComplexInclude (incrementsModeSource F hF c hI vfI x)
  let e := (((τ : ℂ) / Complex.I)⁻¹ • u x) +
    incrementsModeComplexReducedOperator F hF c u x - k
  let α := (τ : ℂ) / Complex.I
  let rowR := fun i j ↦ (fderiv ℝ uR x (EuclideanSpace.single i 1)) j +
    (fderiv ℝ uR x (EuclideanSpace.single j 1)) i -
    2 * inner ℝ (incrementsModeGamma F c x i j) (uR x) -
    2 * inner ℝ (incrementsModeSecondForm F hF c x i j) (νR x) - hR x i j
  let rowI := fun i j ↦ (fderiv ℝ uI x (EuclideanSpace.single i 1)) j +
    (fderiv ℝ uI x (EuclideanSpace.single j 1)) i -
    2 * inner ℝ (incrementsModeGamma F c x i j) (uI x) -
    2 * inner ℝ (incrementsModeSecondForm F hF c x i j) (νI x) - hI x i j
  change err 0 0 = 2 * e 0 ∧ (∀ a : Fin m, err 0 a.succ = e a.succ) ∧
    ∀ q : {p : Fin m × Fin m // p.1 ≤ p.2}, err q.val.1.succ q.val.2.succ = 0
  have hphys (i j : Fin (m + 1)) : err i j =
      (rowR i j : ℂ) + Complex.I * (rowI i j : ℂ) +
      α⁻¹ * ((if i = 0 then u x j else 0) + (if j = 0 then u x i else 0)) := by
    have hp := increments_mode_physical_metric_row F hF y Ω hΩ hΩt hinj u νR νI τ
      x hx hu hνR hνI i j
    dsimp only at hp
    conv_lhs at hp =>
      simp only [νR, νI, Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul]
    dsimp only [err, WR, WI, ZR, ZI]
    simp_rw [incrementsModeFullReconstruction_tangent_normal]
    rw [hp]
    dsimp only [rowR, rowI, uR, uI, c]
    have ha : α⁻¹ = Complex.I / (τ : ℂ) := by dsimp [α]; rw [inv_div]
    rw [ha]
    push_cast
    ring
  constructor
  · have hr := increments_mode_complex_first_row F hF c u α hR hI vfR vfI x
    change (rowR 0 0 : ℂ) + Complex.I * (rowI 0 0 : ℂ) +
      2 * α⁻¹ * u x 0 = 2 * e 0 at hr
    rw [hphys]
    simp only [ite_true]
    calc
      _ = (rowR 0 0 : ℂ) + Complex.I * (rowI 0 0 : ℂ) + 2 * α⁻¹ * u x 0 := by ring
      _ = _ := hr
  constructor
  · intro a
    have hr := increments_mode_complex_mixed_row F hF c u α hR hI vfR vfI x a
    change (rowR 0 a.succ : ℂ) + Complex.I * (rowI 0 a.succ : ℂ) +
      α⁻¹ * u x a.succ = e a.succ at hr
    rw [hphys]
    simpa only [Fin.succ_ne_zero, ite_false, ite_true, add_zero] using hr
  · intro q
    have hr := increments_mode_complex_transverse_row F hF c u hR hI vfR vfI x
      hG hfreeR hfreeI q
    change (rowR q.val.1.succ q.val.2.succ : ℂ) +
      Complex.I * (rowI q.val.1.succ q.val.2.succ : ℂ) = 0 at hr
    rw [hphys]
    simpa only [Fin.succ_ne_zero, ite_false, add_zero, mul_zero] using hr

end ActualChart
end GlobalEmbedding.Paper
