import Smoothing.ParameterGeometryCoefficient
import Smoothing.ParameterTransferBounds

/-!
# Actual spatial two-jet under parameter-dependent source coordinates

The source change may depend on the parameter. Only the parameter component
is independent of the source. The Hessian chain term is retained explicitly.
All additional derivatives are joint derivatives of this actual identity.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
variable {Ep Es Y : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es] [FiniteDimensional ℝ Es]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
attribute [local instance] spatialNativeJetNormedAddCommGroup spatialNativeJetNormedSpace
attribute [local instance] spatialTransferInputNormedAddCommGroup spatialTransferInputNormedSpace

theorem round4SpatialJetTransfer_one
    (b₁ : Es →L[ℝ] Es) (b₂ : Es →L[ℝ] Es →L[ℝ] Es) :
    spatialJetTransfer (Y := Y) 1 0 0 b₁ b₂ = spatialJetPullback b₁ b₂ := by
  apply ContinuousLinearMap.ext
  intro w
  simp [spatialJetTransfer, spatialJetWeight]

def round4SpatialTriangularCoefficient (v : Ep × Es → Es) :
    Ep × Es → SpatialNativeJet Es Y →L[ℝ] SpatialNativeJet Es Y :=
  spatialTransferModel (Es := Es) Y ∘ spatialTransferInputField (fun _ => (1 : ℝ)) v

theorem round4SpatialTriangularCoefficient_apply (v : Ep × Es → Es) (z : Ep × Es) :
    round4SpatialTriangularCoefficient (Y := Y) v z =
      spatialJetPullback (fderiv ℝ (fun x => v (z.1,x)) z.2)
        (fderiv ℝ (fderiv ℝ (fun x => v (z.1,x))) z.2) := by
  simp only [round4SpatialTriangularCoefficient, comp_apply, spatialTransferModel,
    spatialTransferInputField, spatialNativeJet, fderiv_fun_const, fderiv_zero, Pi.zero_apply, round4SpatialJetTransfer_one]

theorem round4_spatialNativeJet_triangular
    (a : Ep → Ep) (v : Ep × Es → Es) (u : Ep × Es → Y)
    (O V : Set (Ep × Es)) (hO : IsOpen O) (hV : IsOpen V)
    (hv : ContDiffOn ℝ ∞ v O) (hu : ContDiffOn ℝ ∞ u V)
    (hmap : MapsTo (fun y => (a y.1, v y)) O V)
    {z : Ep × Es} (hz : z ∈ O) :
    spatialNativeJet (fun y => u (a y.1, v y)) z =
      round4SpatialTriangularCoefficient v z (spatialNativeJet u (a z.1, v z)) := by
  rw [round4SpatialTriangularCoefficient_apply]
  let Os := (fun x : Es => (z.1,x)) ⁻¹' O
  have hOs : IsOpen Os := hO.preimage (continuous_const.prodMk continuous_id)
  have hb : ContDiffOn ℝ ∞ (fun x : Es => v (z.1,x)) Os :=
    hv.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ h => h)
  have hm : ∀ p ∈ ({z.1} : Set Ep), ∀ x ∈ Os, (a p, v (z.1,x)) ∈ V := by
    intro p hp x hx
    rw [mem_singleton_iff] at hp
    subst p
    exact hmap hx
  exact spatialNativeJet_pullback a hOs hV hu hb hm ⟨mem_singleton z.1, hz⟩

theorem round4SpatialTriangularCoefficient_contDiffOn
    {v : Ep × Es → Es} {O : Set (Ep × Es)} (hO : IsOpen O)
    (hv : ContDiffOn ℝ ∞ v O) :
    ContDiffOn ℝ ∞ (round4SpatialTriangularCoefficient (Y := Y) v) O :=
  (spatialTransferModel_contDiff (Es := Es) Y).comp_contDiffOn
    (spatialTransferInputField_contDiffOn hO contDiffOn_const hv)

theorem round4SpatialTriangularCoefficient_jet_le
    (a : Ep → Ep) {v : Ep × Es → Es} {O : Set (Ep × Es)} (hO : IsOpen O)
    (ht : ContDiffOn ℝ ∞ (fun y => (a y.1,v y)) O)
    (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j) {z : Ep × Es} (hz : z ∈ O) (k : ℕ)
    (htransition : ∀ j, 1 ≤ j → j ≤ k+2 →
      ‖iteratedFDeriv ℝ j (fun y => (a y.1,v y)) z‖ ≤ T j) :
    ‖iteratedFDeriv ℝ k (round4SpatialTriangularCoefficient (Y := Y) v) z‖ ≤
      parameterSpatialTransferCoefficient Es Y (fun _ => 1) T k := by
  have hconst (j : ℕ) : ‖iteratedFDeriv ℝ j (fun _ : Ep × Es => (1 : ℝ)) z‖ ≤ 1 := by
    by_cases hj : j = 0
    · subst j
      simp only [norm_iteratedFDeriv_zero, norm_one, le_refl]
    · simp only [iteratedFDeriv_const_of_ne hj, Pi.zero_apply, norm_zero]
      exact zero_le_one
  have hw : ∀ j ≤ k+2, ‖iteratedFDeriv ℝ j (fun _ : Ep × Es => (1 : ℝ)^2) z‖ ≤
      bufferedCutoffSquareConstant (fun _ => 1) j := by
    intro j hj
    exact parameter_square_jet_le hO contDiffOn_const (fun _ => 1) (fun _ => zero_le_one)
      hz j (fun l _ => hconst l)
  have hbound : ∀ j, 1 ≤ j → j ≤ k+2 →
      ‖iteratedFDeriv ℝ j v z‖ ≤ T j := fun j hj hjk =>
    (parameter_source_component_jet_le hO ht hz j).trans (htransition j hj hjk)
  have h := spatialTransferModel_composed_jet_le (Y := Y) hO contDiffOn_const ht.snd
    (bufferedCutoffSquareConstant (fun _ => 1)) T
    (bufferedCutoffSquareConstant_nonneg (fun _ => zero_le_one)) hT hz k hw hbound
  simpa only [one_pow, round4SpatialTriangularCoefficient, parameterSpatialTransferCoefficient] using h

/-- Weighted transfer consumes only the genuine spatial packet at the source. -/
theorem round4_spatial_triangular_slow_jet
    (a : Ep → Ep) (v : Ep × Es → Es) (u : Ep × Es → Y)
    (O V : Set (Ep × Es)) (hO : IsOpen O) (hV : IsOpen V)
    (ht : ContDiffOn ℝ ∞ (fun y => (a y.1,v y)) O)
    (hu : ContDiffOn ℝ ∞ u V) (hmap : MapsTo (fun y => (a y.1,v y)) O V)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    {z : Ep × Es} (hz : z ∈ O) (j : ℕ) (ell R : ℝ)
    (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hjets : ∀ k ≤ j, ell^k * ‖iteratedFDeriv ℝ k (spatialNativeJet u) (a z.1,v z)‖ ≤ R)
    (htransition : ∀ k, 1 ≤ k → k ≤ j+2 →
      ‖iteratedFDeriv ℝ k (fun y => (a y.1,v y)) z‖ ≤ T k) :
    ell^j * ‖iteratedFDeriv ℝ j (spatialNativeJet (fun y => u (a y.1,v y))) z‖ ≤
      parameterJetTransferCore (parameterSpatialTransferCoefficient Es Y (fun _ => 1) T) T j * R := by
  let C := parameterSpatialTransferCoefficient Es Y (fun _ => 1) T
  have hC : ∀ k, 0 ≤ C k := parameterSpatialTransferCoefficient_nonneg Es Y (fun _ => zero_le_one) hT
  have houter (k : ℕ) (hk : k ≤ j) :
      ‖iteratedFDeriv ℝ k (spatialNativeJet u) (a z.1,v z)‖ ≤ R/ell^j := by
    apply (le_div_iff₀ (pow_pos hell j)).2
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hell.le hell1 hk)
      (norm_nonneg _)).trans (hjets k hk)
  have heq : spatialNativeJet (fun y => u (a y.1,v y)) =ᶠ[𝓝 z]
      (fun y => round4SpatialTriangularCoefficient v y (spatialNativeJet u (a y.1,v y))) := by
    filter_upwards [hO.mem_nhds hz] with y hy
    exact round4_spatialNativeJet_triangular a v u O V hO hV ht.snd hu hmap hy
  rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
  have h := parameter_operator_transfer_jet_le C T hC hT hO hV
    (round4SpatialTriangularCoefficient_contDiffOn hO ht.snd) ht
    (spatialNativeJet_contDiffOn hV hu) hmap hz j (R/ell^j)
    (fun k hk => round4SpatialTriangularCoefficient_jet_le a hO ht T hT hz k
      (fun l hl hlk => htransition l hl (by omega)))
    (fun k hk hkj => htransition k hk (by omega)) houter
  calc
    _ ≤ ell^j * (parameterJetTransferCore C T j * (R/ell^j)) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg hell.le j)
    _ = _ := by
      field_simp [(pow_pos hell j).ne']
      dsimp only [C]
      ring

#print axioms round4_spatialNativeJet_triangular
#print axioms round4_spatial_triangular_slow_jet
end GlobalEmbedding.Continuation
