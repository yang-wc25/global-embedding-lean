import Round2.AtlasNormGeometry

/-!
# The actual two-jet estimate through a chart transition

The original component C² norm controls the actual native derivatives of the
inner coordinate representative.  Mathlib's iterated chain-rule estimate then
uses both derivatives of the true chart transition.  Equality of the two
coordinate representatives is proved on the open overlap, so no derivative
of a merely pointwise identity is used.
-/

noncomputable section
open Function Filter Manifold Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open Paper GlobalEmbedding.Offline

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "P" => Fin n → ℝ

/-- The pointwise bound at a genuine compact overlap point.  Both order-one
and order-two chart-transition terms are controlled; only the original
`probeAtlasCj A 2` norm of the same map is used. -/
theorem atlasNormOverlap_coordinate_twoJet_bound
    (A B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hB : IsSmoothBufferedAtlas B) (i : Fin A.count) (j : Fin B.count)
    {D : ℝ} (hD : 1 ≤ D)
    (htransition : ∀ z ∈ atlasNormOverlapSupport A B i j,
      ‖iteratedFDeriv ℝ 1 (atlasNormTransition A B i j) z‖ ≤ D ∧
      ‖iteratedFDeriv ℝ 2 (atlasNormTransition A B i j) z‖ ≤ D)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    {b : ℝ} (hb : 0 ≤ b) (hbound : probeAtlasCj A 2 F ≤ ENNReal.ofReal b)
    {k : ℕ} (hk : k ≤ 2) {z : P} (hz : z ∈ atlasNormOverlapSupport A B i j) :
    ‖iteratedFDeriv ℝ k
      (fun y ↦ (EuclideanSpace.equiv (Fin N) ℝ)
        (F ((B.chart j).symm ((EuclideanSpace.equiv (Fin n) ℝ).symm y)))) z‖ ≤
      (2 * ((n : ℝ) + 1) ^ 2 * D ^ 2) * b := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let v := EuclideanSpace.equiv (Fin N) ℝ
  let f : P → Fin N → ℝ := fun y ↦ v (F ((B.chart j).symm (e.symm y)))
  let g : P → Fin N → ℝ := fun y ↦ v (F ((A.chart i).symm (e.symm y)))
  let T := atlasNormTransition A B i j
  let U := atlasNormTransitionDomain A B i j
  let O := e '' (A.chart i).target
  let S := e '' ((A.chart i) '' A.support i)
  have hU : IsOpen U := atlasNormTransitionDomain_isOpen A B i j
  have hzU : z ∈ U := atlasNormOverlapSupport_subset_domain A B hA hB i j hz
  have hO : IsOpen O := e.toHomeomorph.isOpenMap _ (A.chart i).open_target
  have hSO : S ⊆ O := by
    rintro y ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨A.chart i x, (A.chart i).map_source (hA.support_subset i hx), rfl⟩
  have hmap : MapsTo T U O := by
    intro y hy
    change e.symm y ∈ ((B.chart j).symm.trans (A.chart i)).source at hy
    rw [OpenPartialHomeomorph.trans_source] at hy
    exact ⟨A.chart i ((B.chart j).symm (e.symm y)), (A.chart i).map_source hy.2, rfl⟩
  have hsupp : T z ∈ S := by
    rcases hz with ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    have hBx := hB.support_subset j hx.1
    refine ⟨A.chart i x, ⟨x, hx.2, rfl⟩, ?_⟩
    simp only [T, atlasNormTransition, e, ContinuousLinearEquiv.symm_apply_apply,
      (B.chart j).left_inv hBx]
  have hg : ContDiffOn ℝ ∞ g O := probeAtlas_coordinate_smooth A hA F hF i
  have hT : ContDiffOn ℝ ∞ T U := atlasNormTransition_contDiffOn A B hA hB i j
  have hlocal : paperCoordinateCj 2 g O S ≤ ENNReal.ofReal b :=
    (le_iSup (fun q ↦ paperCoordinateCj 2
      (fun y ↦ v (F ((A.chart q).symm (e.symm y))))
      (e '' (A.chart q).target) (e '' ((A.chart q) '' A.support q))) i).trans hbound
  have hC : ∀ a, a ≤ k →
      ‖iteratedFDerivWithin ℝ a g O (T z)‖ ≤ ((n : ℝ) + 1) ^ 2 * b := by
    intro a ha
    rw [iteratedFDerivWithin_of_isOpen a hO (hSO hsupp)]
    have hbase := iteratedFDeriv_le_of_paperCoordinateCj_le
      hO hSO hg hb hlocal (ha.trans hk) hsupp
    refine hbase.trans (mul_le_mul_of_nonneg_right ?_ hb)
    exact (pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) a).trans
      (pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (ha.trans hk))
  have hD' : ∀ a, 1 ≤ a → a ≤ k →
      ‖iteratedFDerivWithin ℝ a T U z‖ ≤ D ^ a := by
    intro a ha hka
    rw [iteratedFDerivWithin_of_isOpen a hU hzU]
    rcases (show a = 1 ∨ a = 2 by omega) with rfl | rfl
    · simpa only [pow_one] using (htransition z hz).1
    · exact ((htransition z hz).2).trans (by nlinarith)
  have heq : f =ᶠ[𝓝 z] g ∘ T := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    change e.symm y ∈ ((B.chart j).symm.trans (A.chart i)).source at hy
    rw [OpenPartialHomeomorph.trans_source] at hy
    simp only [f, g, T, atlasNormTransition, comp_apply, e,
      ContinuousLinearEquiv.symm_apply_apply, (A.chart i).left_inv hy.2]
  have hc := norm_iteratedFDerivWithin_comp_le hg hT (show (k : ℕ∞ω) ≤ ∞ by simp)
    hO.uniqueDiffOn hU.uniqueDiffOn hmap hzU hC hD'
  rw [iteratedFDerivWithin_of_isOpen k hU hzU] at hc
  change ‖iteratedFDeriv ℝ k f z‖ ≤ _
  rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
  have hfac : (k.factorial : ℝ) ≤ 2 := by interval_cases k <;> norm_num
  have hdim : 0 ≤ ((n : ℝ) + 1) ^ 2 * b := mul_nonneg (sq_nonneg _) hb
  calc
    _ ≤ (k.factorial : ℝ) * (((n : ℝ) + 1) ^ 2 * b) * D ^ k := hc
    _ ≤ 2 * (((n : ℝ) + 1) ^ 2 * b) * D ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hfac hdim)
        (pow_le_pow_right₀ hD hk) (pow_nonneg (by linarith) _)
        (mul_nonneg (by norm_num) hdim)
    _ = _ := by ring

end GlobalEmbedding.Upgrade
