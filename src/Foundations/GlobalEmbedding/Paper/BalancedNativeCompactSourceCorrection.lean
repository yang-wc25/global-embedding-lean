import GlobalEmbedding.Paper.BalancedNativeLocalSourceData
import GlobalEmbedding.Paper.LittlePeriodicCAlphaCompactSourceCorrection

/-!
# Actual compact local correction branches from native global sources

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines403–418.
DAG node: `balanced-native-compact-source-correction`.
-/

noncomputable section

open Set WithLp
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

local instance balancedNativeCompactTorusChartedSpace (a : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin a)) (PeriodOneTorus a) :=
  periodicFlatTorusChartedSpace a

variable {E H EB M B ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B]

namespace PrincipalTorusBundle

variable {a : ℕ} {I : ModelWithCorners ℝ E H} {π : M → B}
  [IsManifold I ∞ M] [AddAction (PeriodOneTorus a) M]
  (S : PrincipalTorusBundle (ι := ι) a I 𝓘(ℝ, EB) π)

/-- Actual native global sources construct genuine common-interval local correction
branches near any actual compact set of genuine bundle/base coordinates.

Proof: the native local-source constructor supplies actual little forcing and bounded
multiplier carriers, exact original values and true norm smoothness. Its actual pullback
theorem also gives the pointwise source smoothness and integer periodicity. The source
forcing at time zero is zero because the original global forcing is zero there. Apply
the existing actual compact-source correction theorem verbatim. Retain its actual open
neighborhood, common interval, strict-small fixed equations, linear v bound and genuine
native joint smoothness/quadratic norm bound of time times v. No compact bounds, little
carriers, selected solution, bootstrap regularity or compatibility are assumed.
The bounded symmetric equivariant Q is the separate analytic construction input of this
auxiliary; the final target uses the actual canonical whole-function Qcal, not a new
target hypothesis. Source: the compact local contraction in `lem:balanced`, lines403–418. -/
theorem native_compact_source_correction {d N : ℕ} {α : ℝ}
    (Q : LittlePeriodicCAlphaFunction a N 2 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α →L[ℝ] LittlePeriodicCAlphaFunction a d 2 α)
    (hQsym : ∀ v w, Q v w = Q w v)
    (hQτ : ∀ h v w, Q (littlePeriodicCAlphaTranslateIsometry h v)
      (littlePeriodicCAlphaTranslateIsometry h w) =
        littlePeriodicCAlphaTranslateIsometry h (Q v w))
    (R : ℝ) (hR : 0 < R)
    (sourceA : ℝ × M → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (sourcef : ℝ × M → EuclideanSpace ℝ (Fin N))
    (hA : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I)
      𝓘(ℝ, EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N)) ∞
      sourceA (Metric.ball (0 : ℝ) R ×ˢ univ))
    (hf : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I)
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ sourcef (Metric.ball (0 : ℝ) R ×ˢ univ))
    (hf0 : ∀ x : M, sourcef (0, x) = 0)
    (i : ι) (b : B) (K : Set EB) (hK : IsCompact K)
    (hKU : K ⊆ S.nativeBundleBaseSet i b) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ f : EB × ℝ → LittlePeriodicCAlphaFunction a N 2 α,
      ∃ A : EB × ℝ → LittlePeriodicCAlphaFunction a d 2 α →L[ℝ]
          LittlePeriodicCAlphaFunction a N 2 α,
        (∀ z ∈ S.nativeBundleBaseSet i b ×ˢ Metric.ball (0 : ℝ) R, ∀ y,
          (f z).val.toFun y = S.nativeSourcePullback sourcef i b z y) ∧
        (∀ z ∈ S.nativeBundleBaseSet i b ×ˢ Metric.ball (0 : ℝ) R,
          ∀ (u : LittlePeriodicCAlphaFunction a d 2 α) y,
            (A z u).val.toFun y = S.nativeSourcePullback sourceA i b z y (u.val.toFun y)) ∧
        ∃ V : Set EB, IsOpen V ∧ K ⊆ V ∧ V ⊆ S.nativeBundleBaseSet i b ∧
          ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ δ < R ∧
            ∃ v : EB × ℝ → LittlePeriodicCAlphaFunction a N 2 α,
              ContDiffOn ℝ ∞ v (V ×ˢ Metric.ball (0 : ℝ) δ) ∧
              (∀ p ∈ V, v (p, 0) = 0) ∧
              (∀ z ∈ V ×ˢ Metric.ball (0 : ℝ) δ,
                v z = f z + A z (Q (v z) (v z)) ∧ ‖v z‖ ≤ C * |z.2| ∧
                  ‖(2 : ℝ) • (A z).comp (Q (v z))‖ < 1) ∧
              (∀ z ∈ V ×ˢ Metric.ball (0 : ℝ) δ,
                ‖z.2 • v z‖ ≤ C * z.2 ^ 2) ∧
              ContMDiffOn ((𝓘(ℝ, EB × ℝ)).prod
                𝓘(ℝ, EuclideanSpace ℝ (Fin a)))
                𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
                (fun z : (EB × ℝ) × PeriodOneTorus a ↦
                  littlePeriodicCAlphaTorusValue (z.1.2 • v z.1) z.2)
                ((V ×ˢ Metric.ball (0 : ℝ) δ) ×ˢ univ) := by
  obtain ⟨f, A, hfvalue, hAvalue, _, _⟩ :=
    S.native_local_source_data (Metric.ball (0 : ℝ) R) Metric.isOpen_ball
      sourceA sourcef hA hf i b hα0 hα1
  obtain ⟨hsA, hperiodA⟩ :=
    S.native_source_pullback_smooth_periodic (Metric.ball (0 : ℝ) R) sourceA hA i b
  obtain ⟨hsf, hperiodf⟩ :=
    S.native_source_pullback_smooth_periodic (Metric.ball (0 : ℝ) R) sourcef hf i b
  have hlocal0 (p : EB) (_hp : p ∈ S.nativeBundleBaseSet i b)
      (y : EuclideanSpace ℝ (Fin a)) : S.nativeSourcePullback sourcef i b (p, 0) y = 0 :=
    hf0 _
  obtain ⟨V, hV, hKV, hclU, _hclcompact, δ, C, hδ, hC, hδR, v,
      hv, hv0, hspec, _huniq, _hvτ, _hvvalue, _hvnative, hcorrection⟩ :=
    littlePeriodicCAlpha_compact_source_correction Q hQsym hQτ
      (S.nativeBundleBaseSet i b) K (S.isOpen_nativeBundleBaseSet i b) hK hKU R hR
      A f (S.nativeSourcePullback sourceA i b) (S.nativeSourcePullback sourcef i b)
      hsA hsf hperiodA hperiodf hAvalue hfvalue hlocal0 hα0 hα1
  obtain ⟨_hu, _hu0, hubound, _hdu0, _huτ, hunative⟩ := hcorrection
  refine ⟨f, A, hfvalue, hAvalue, V, hV, hKV, ?_, δ, C, hδ, hC, hδR,
    v, hv, hv0, ?_, ?_, hunative⟩
  · exact subset_closure.trans hclU
  · intro z hz
    exact ⟨(hspec z hz).1, (hspec z hz).2.1,
      (hspec z hz).2.2.1.trans_lt (by norm_num)⟩
  · intro z hz
    exact (hubound z hz).1

#print axioms native_compact_source_correction

end PrincipalTorusBundle
end GlobalEmbedding.Paper
