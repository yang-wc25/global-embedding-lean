import Smoothing.IntegrationParameterModelHighGain

/-!
# Spatial-base parameter-map tail in the original coordinates

The map is the same bufferedSmoothing on the genuine product atlas. No
replacement jets are glued. Native low/high bounds are produced internally
from the original input norms on a fixed sampling buffer, and then summed
with the original weights. Constants precede all atlases, fields and scales.
This is the spatial-0/1/2 packet version of the two-term tail. It is distinct
from frozen paperAtlasWeighted 2 on the full joint coordinate space, which
also contains two extra pure-parameter derivatives. It must not be identified
with that stronger frozen Core field without a separate theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators

namespace GlobalEmbedding.Continuation

attribute [local instance] spatialNativeJetNormedAddCommGroup spatialNativeJetNormedSpace

section Constants
variable {Ep Es Y : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es] [FiniteDimensional ℝ Es]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace (Ep × Es)] {n d q : ℕ}

def parameterModelTransferConstant
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ)) (C T : ℕ → ℝ) (D j : ℕ) : ℝ :=
  parameterModelCoordinateFactor cp cs cy j * parameterJetTransferConstant C T D j

theorem parameterModelTransferConstant_nonneg
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ)) {C T : ℕ → ℝ}
    (hC : ∀ j, 0 ≤ C j) (hT : ∀ j, 0 ≤ T j) (D j : ℕ) :
    0 ≤ parameterModelTransferConstant cp cs cy C T D j :=
  mul_nonneg (parameterModelCoordinateFactor_nonneg cp cs cy j)
    (parameterJetTransferConstant_nonneg hC hT D j)

theorem parameterModelTransferConstant_mono
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ)) {C T : ℕ → ℝ}
    (hC : ∀ j, 0 ≤ C j) (hT : ∀ j, 0 ≤ T j) (D : ℕ) {j k : ℕ} (hjk : j ≤ k) :
    parameterModelTransferConstant cp cs cy C T D j ≤ parameterModelTransferConstant cp cs cy C T D k :=
  mul_le_mul (parameterModelCoordinateFactor_mono cp cs cy hjk)
    (parameterJetTransferConstant_mono hC hT D hjk)
    (parameterJetTransferConstant_nonneg hC hT D j) (parameterModelCoordinateFactor_nonneg cp cs cy k)

def parameterModelSmoothingTailConstant
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ)) (mu : Measure (Ep × Es)) (kappa : Ep × Es → ℝ)
    (C T : ℕ → ℝ) (D m r : ℕ) : ℝ :=
  parameterModelTransferConstant cp cs cy C T D m *
    (((m+1 : ℕ) : ℝ) * (kernelTailConstant mu (finiteMomentKernel r kappa) r *
      parameterModelNativeFactor cp cs cy r) +
      (1 + ∫ y, |finiteMomentKernel r kappa y| ∂mu) * parameterModelNativeFactor cp cs cy m)

theorem parameterModelSmoothingTailConstant_nonneg
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ)) (mu : Measure (Ep × Es)) (kappa : Ep × Es → ℝ)
    {C T : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j) (hT : ∀ j, 0 ≤ T j) (D m r : ℕ) :
    0 ≤ parameterModelSmoothingTailConstant cp cs cy mu kappa C T D m r := by
  unfold parameterModelSmoothingTailConstant
  exact mul_nonneg (parameterModelTransferConstant_nonneg cp cs cy hC hT D m)
    (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (kernelTailConstant_nonneg mu _ _)
      (parameterModelNativeFactor_nonneg cp cs cy r)))
      (mul_nonneg (add_nonneg zero_le_one (integral_nonneg fun _ => abs_nonneg _))
        (parameterModelNativeFactor_nonneg cp cs cy m)))
end Constants

variable {Ep Es P M Y : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [FiniteDimensional ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es] [FiniteDimensional ℝ Es]
  [MeasurableSpace Ep] [BorelSpace Ep] [MeasurableSpace Es] [BorelSpace Es]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace Ep P] [IsManifold 𝓘(ℝ, Ep) ∞ P]
  [ChartedSpace Es M] [IsManifold 𝓘(ℝ, Es) ∞ M]
  {n d q : ℕ}

local instance : ChartedSpace (Ep × Es) (P × M) := prodChartedSpace Ep P Es M
local instance : IsManifold 𝓘(ℝ, Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Ep)) (I' := 𝓘(ℝ, Es)) (n := ∞) P M

variable (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
local notation "AB" => parameterProductAtlas A B

/-- The actual spatial-base parameter-map counterpart of (6.4), for unchanged native
models and true spatial 0/1/2 packet followed by all joint derivatives. -/
theorem parameterBufferedSmoothing_original_weighted_tail
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ)) (mu : Measure (Ep × Es)) [mu.IsAddHaarMeasure]
    {kappa : Ep × Es → ℝ} (hsmooth : ContDiff ℝ ∞ kappa) (hcompact : HasCompactSupport kappa)
    (hmass : (∫ y, kappa y ∂mu) = 1) (m r : ℕ)
    {rho tau ell t : ℝ} (hsupp : tsupport (finiteMomentKernel r kappa) ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ min B.buffer A.buffer) (htau : 0 < tau) (htaul : tau ≤ ell)
    (helt : ell ≤ t) (ht1 : t ≤ 1)
    (chi : Fin (B.count * A.count) → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (AB).inner i)
    (hpartition : ∀ z, ∑ i, chi i z ^ 2 = 1)
    {u : P × M → Y} (hu : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Y) ∞ u)
    (C T : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k) (hT : ∀ k, 0 ≤ T k) (D : ℕ)
    (hD : ∀ z, (activeCutoffIndices chi z).card ≤ D)
    (hcoeff : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates AB p,
      ((AB).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (parameterBufferedTransfer (Y := Y) A B chi p i) y‖ ≤ C k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates AB p,
      ((AB).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k ((AB).chart i ∘ ((AB).chart p).symm) y‖ ≤ T k)
    (hNr : parameterSpatialWeighted (n := n) (d := d) r t
      (parameterBufferedModelCoordinates A B cp cs cy u)
      (parameterBufferedModelTargets A B cp cs) (parameterBufferedModelSampling A B cp cs) ≠ ⊤)
    (hNm : parameterSpatialWeighted (n := n) (d := d) m t
      (parameterBufferedModelCoordinates A B cp cs cy u)
      (parameterBufferedModelTargets A B cp cs) (parameterBufferedModelSampling A B cp cs) ≠ ⊤)
    (budget : ℝ) (hbudget : (parameterSpatialWeighted (n := n) (d := d) r t
      (parameterBufferedModelCoordinates A B cp cs cy u)
      (parameterBufferedModelTargets A B cp cs) (parameterBufferedModelSampling A B cp cs)).toReal ≤ budget) :
    let S := bufferedSmoothing AB mu (finiteMomentKernel r kappa) ell chi u
    let f := parameterBufferedModelCoordinates A B cp cs cy u
    let e := parameterBufferedModelCoordinates A B cp cs cy (fun z => S z - u z)
    let O := parameterBufferedModelTargets A B cp cs
    parameterSpatialWeighted (n := n) (d := d) m tau e O (parameterBufferedModelInner A B cp cs) ≠ ⊤ ∧
    (parameterSpatialWeighted (n := n) (d := d) m tau e O (parameterBufferedModelInner A B cp cs)).toReal ≤
      parameterModelSmoothingTailConstant cp cs cy mu kappa C T D m r *
        (budget * (ell/t)^r +
          (parameterSpatialWeighted (n := n) (d := d) m t f O
            (parameterBufferedModelSampling A B cp cs)).toReal * (tau/t)^r) := by
  dsimp only
  let K := finiteMomentKernel r kappa
  let S := bufferedSmoothing AB mu K ell chi u
  let f := parameterBufferedModelCoordinates A B cp cs cy u
  let e := parameterBufferedModelCoordinates A B cp cs cy (fun z => S z - u z)
  let O := parameterBufferedModelTargets A B cp cs
  let V := parameterBufferedModelSampling A B cp cs
  let U := parameterBufferedModelInner A B cp cs
  let I := fun j => (parameterSpatialCj (n := n) (d := d) j f O V).toReal
  let E := fun j => (parameterSpatialCj (n := n) (d := d) j e O U).toReal
  let Q := parameterModelTransferConstant cp cs cy C T D m
  let L := Q * kernelTailConstant mu K r * parameterModelNativeFactor cp cs cy r
  let H := Q * (1 + ∫ y, |K y| ∂mu) * parameterModelNativeFactor cp cs cy m
  have hQ : 0 ≤ Q := parameterModelTransferConstant_nonneg cp cs cy hC hT D m
  have hK : 0 ≤ kernelTailConstant mu K r := kernelTailConstant_nonneg mu K r
  have hL1 : 0 ≤ 1 + ∫ y, |K y| ∂mu :=
    add_nonneg zero_le_one (integral_nonneg fun y => abs_nonneg (K y))
  have hL : 0 ≤ L := mul_nonneg (mul_nonneg hQ hK) (parameterModelNativeFactor_nonneg cp cs cy r)
  have hH : 0 ≤ H := mul_nonneg (mul_nonneg hQ hL1) (parameterModelNativeFactor_nonneg cp cs cy m)
  have hell : 0 < ell := htau.trans_le htaul
  have ht : 0 < t := hell.trans_le helt
  have hell1 : ell ≤ 1 := helt.trans ht1
  have hfinM (j : ℕ) (hj : j ≤ m) := parameterSpatialWeighted_Cj_ne_top m ht f O V hNm hj
  have hfinR := parameterSpatialWeighted_Cj_ne_top r ht f O V hNr le_rfl
  have hhighRaw (j : ℕ) (hj : j ≤ m) := parameterBufferedModel_error_high A B hA hB cp cs cy mu
    (finiteMomentKernel_contDiff hsmooth r) (finiteMomentKernel_hasCompactSupport hcompact r) j
    hsupp hrho hell.le hell1 chi hchi hchiSupport hpartition hu C T hC hT D hD hcoeff htransition (hfinM j hj)
  have hout := parameterSpatialWeighted_ne_top_of_Cj m tau e O U (fun j hj => (hhighRaw j hj).1)
  have hlow : ∀ j ≤ m, j ≤ r → E j ≤ L * ell^(r-j) * I r := by
    intro j hj hjr
    have h := (parameterBufferedModel_error_low A B hA hB cp cs cy mu hsmooth hcompact hmass r j hjr
      hsupp hrho hell.le hell1 chi hchi hchiSupport hpartition hu C T hC hT D hD hcoeff htransition hfinR).2
    apply h.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (parameterModelTransferConstant_mono cp cs cy hC hT D hj) hK)
          (parameterModelNativeFactor_nonneg cp cs cy r)) (pow_nonneg hell.le _)) ENNReal.toReal_nonneg
  have hhigh : ∀ j ≤ m, E j ≤ H * I j := by
    intro j hj
    apply (hhighRaw j hj).2.trans
    apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (parameterModelTransferConstant_mono cp cs cy hC hT D hj) hL1)
      (parameterModelNativeFactor_mono cp cs cy hj) (parameterModelNativeFactor_nonneg cp cs cy j)
      (mul_nonneg hQ hL1)
  have hNrSum : (∑ a ∈ Finset.range (r+1), t^a * I a) ≤ budget := by
    rw [parameterSpatialWeighted_toReal r t ht.le f O V hNr] at hbudget
    exact hbudget
  have hw := weighted_low_high_tail m r I E (fun _ => ENNReal.toReal_nonneg)
    L H hL hH htau.le htaul helt ht budget hNrSum hlow hhigh
  refine ⟨hout, ?_⟩
  rw [parameterSpatialWeighted_toReal m tau htau.le e O U hout,
    parameterSpatialWeighted_toReal m t ht.le f O V hNm]
  convert hw using 1
  unfold parameterModelSmoothingTailConstant
  dsimp only [L, H, Q, K]
  ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.parameterBufferedSmoothing_original_weighted_tail
