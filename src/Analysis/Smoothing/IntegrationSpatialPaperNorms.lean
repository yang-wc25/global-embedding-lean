import Smoothing.IntegrationSpatialJetNorms

/-!
# Original anisotropic coordinate norms and native spatial-jet estimates

The original coordinate norm is the base-zero norm of the LITERAL spatial
0/1/2 derivative packet. All its extra derivatives are joint derivatives.
These two directions transfer actual native global estimates to that norm,
and transfer actual source-coordinate bounds back to native local estimates.
The constants depend only on dimensions and the joint derivative order.
Finiteness is proved before any ENNReal.toReal use on an output norm.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Filter Set Function
open scoped ContDiff Topology ENNReal BigOperators

namespace GlobalEmbedding.Continuation

attribute [local instance] spatialNativeJetNormedAddCommGroup spatialNativeJetNormedSpace

/-- Cumulative joint Cj norm of the genuine original spatial two-jet. -/
def parameterSpatialCj {ι : Type*} [Fintype ι] {n d q : ℕ}
    (j : ℕ) (f : ι → (Fin (n+d) → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin (n+d) → ℝ)) : ℝ≥0∞ :=
  paperAtlasCj j (parameterSpatialPacket (n := n) (d := d) f)
    (fun iw => O iw.1) (fun iw => S iw.1)

/-- Inverse-coordinate cost, with both source-model and output-jet costs explicit. -/
def parameterSpatialNativeFactor (n d q j : ℕ) : ℝ :=
  spatialJetReconstructionConstant n q * nativeCoordinateFactor (sourceFirstCoordinates n d) j

/-- Forward-coordinate cost for a cumulative native spatial-jet bound. -/
def parameterSpatialCoordinateFactor (n d q j : ℕ) : ℝ :=
  spatialJetEvaluationConstant n q * linearModelFactor (sourceFirstCoordinates n d).symm j

theorem parameterSpatialNativeFactor_nonneg (n d q j : ℕ) :
    0 ≤ parameterSpatialNativeFactor n d q j :=
  mul_nonneg (spatialJetReconstructionConstant_nonneg n q)
    (nativeCoordinateFactor_nonneg _ j)

theorem parameterSpatialCoordinateFactor_nonneg (n d q j : ℕ) :
    0 ≤ parameterSpatialCoordinateFactor n d q j :=
  mul_nonneg (spatialJetEvaluationConstant_nonneg n q) (linearModelFactor_nonneg _ j)

theorem parameterSpatialCoordinateFactor_mono (n d q : ℕ) {k j : ℕ} (hkj : k ≤ j) :
    parameterSpatialCoordinateFactor n d q k ≤ parameterSpatialCoordinateFactor n d q j :=
  mul_le_mul_of_nonneg_left (linearModelFactor_mono _ hkj)
    (spatialJetEvaluationConstant_nonneg n q)

/-- Genuine local equality of the actual native evaluation and original packet. -/
theorem native_spatial_word_eventuallyEq {n d q : ℕ}
    {f : (Fin (n+d) → ℝ) → Fin q → ℝ} {O : Set (Fin (n+d) → ℝ)}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    {z : (Fin d → ℝ) × (Fin n → ℝ)} (hz : sourceFirstCoordinates n d z ∈ O)
    (w : ParameterSpatialWord n) :
    (spatialJetEvaluation w ∘ spatialNativeJet (f ∘ sourceFirstCoordinates n d))
      =ᶠ[𝓝 z] (parameterSpatialJet f w ∘ sourceFirstCoordinates n d) := by
  have hU := hO.preimage (sourceFirstCoordinates n d).continuous
  filter_upwards [hU.mem_nhds hz] with y hy
  exact (parameterSpatialJet_eq_native_evaluation hO hf hy w).symm

/-- Source bounds in the original anisotropic coordinate norm supply every
native joint derivative of the same spatial jet, without a chart-count factor. -/
theorem parameterSpatialCj_native_jet_le {ι : Type*} [Fintype ι] {n d q : ℕ}
    (j : ℕ) (f : ι → (Fin (n+d) → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin (n+d) → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (hfinite : parameterSpatialCj (n := n) (d := d) j f O S ≠ ⊤)
    (i : ι) {k : ℕ} (hk : k ≤ j)
    {z : (Fin d → ℝ) × (Fin n → ℝ)} (hz : sourceFirstCoordinates n d z ∈ S i) :
    ‖iteratedFDeriv ℝ k (spatialNativeJet (f i ∘ sourceFirstCoordinates n d)) z‖ ≤
      parameterSpatialNativeFactor n d q j * (parameterSpatialCj (n := n) (d := d) j f O S).toReal := by
  let c := sourceFirstCoordinates n d
  have hU : IsOpen (c ⁻¹' O i) := (hO i).preimage c.continuous
  have hfc : ContDiffOn ℝ ∞ (f i ∘ c) (c ⁻¹' O i) :=
    (hf i).comp c.contDiff.contDiffOn (fun _ hy => hy)
  have hj := (spatialNativeJet_contDiffOn hU hfc).contDiffAt (hU.mem_nhds (hSO i hz))
  have hpacket (iw : ι × ParameterSpatialWord n) :
      ContDiffOn ℝ ∞ (parameterSpatialPacket (n := n) (d := d) f iw) (O iw.1) :=
    parameterSpatialJet_contDiffOn (hO iw.1) (hf iw.1) iw.2
  have hw (w : ParameterSpatialWord n) :
      ‖iteratedFDeriv ℝ k
        (spatialJetEvaluation w ∘ spatialNativeJet (f i ∘ c)) z‖ ≤
      nativeCoordinateFactor c j * (parameterSpatialCj (n := n) (d := d) j f O S).toReal := by
    rw [((native_spatial_word_eventuallyEq (hO i) (hf i) (hSO i hz) w).iteratedFDeriv ℝ k).eq_of_nhds]
    have hc := paperAtlasCj_jet_le j (parameterSpatialPacket (n := n) (d := d) f)
      (fun iw => O iw.1) (fun iw => S iw.1) (fun iw => hO iw.1)
      (fun iw => hSO iw.1) hpacket hfinite (i,w) hk hz
    have ht := norm_iteratedFDeriv_comp_equiv_le c (parameterSpatialJet (f i) w) k z
    apply ht.trans
    calc
      _ ≤ (coordinateDimensionFactor (n+d) j *
          (parameterSpatialCj (n := n) (d := d) j f O S).toReal) * linearModelFactor c j :=
        mul_le_mul hc (linearModelFactor_mono c hk) (linearModelFactor_nonneg c k)
          (mul_nonneg (coordinateDimensionFactor_nonneg (n+d) j) ENNReal.toReal_nonneg)
      _ = _ := by unfold nativeCoordinateFactor; ring
  have hb := norm_iteratedFDeriv_nativeJet_of_word_bounds hj
    (nativeCoordinateFactor c j * (parameterSpatialCj (n := n) (d := d) j f O S).toReal)
    (mul_nonneg (nativeCoordinateFactor_nonneg c j) ENNReal.toReal_nonneg) hw
  simpa only [parameterSpatialNativeFactor, mul_assoc] using hb

/-- Local regularity of the SAME spatial jet after source-first model conversion. -/
theorem sourceFirst_spatialNativeJet_contDiffAt {n d q : ℕ}
    {f : (Fin (n+d) → ℝ) → Fin q → ℝ} {O : Set (Fin (n+d) → ℝ)}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) {x : Fin (n+d) → ℝ} (hx : x ∈ O) :
    ContDiffAt ℝ ∞ (spatialNativeJet (f ∘ sourceFirstCoordinates n d))
      ((sourceFirstCoordinates n d).symm x) := by
  let c := sourceFirstCoordinates n d
  have hU : IsOpen (c ⁻¹' O) := hO.preimage c.continuous
  have hfc : ContDiffOn ℝ ∞ (f ∘ c) (c ⁻¹' O) :=
    hf.comp c.contDiff.contDiffOn (fun _ hy => hy)
  exact (spatialNativeJet_contDiffOn hU hfc).contDiffAt
    (hU.mem_nhds (by
      change c (c.symm x) ∈ O
      simpa only [c.apply_symm_apply] using hx))

/-- Reverse local equality in the original flat coordinates. -/
theorem original_spatial_word_eventuallyEq {n d q : ℕ}
    {f : (Fin (n+d) → ℝ) → Fin q → ℝ} {O : Set (Fin (n+d) → ℝ)}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) {x : Fin (n+d) → ℝ} (hx : x ∈ O)
    (w : ParameterSpatialWord n) :
    parameterSpatialJet f w =ᶠ[𝓝 x]
      (spatialJetEvaluation w ∘ spatialNativeJet (f ∘ sourceFirstCoordinates n d)) ∘
        (sourceFirstCoordinates n d).symm := by
  filter_upwards [hO.mem_nhds hx] with y hy
  have hy' : sourceFirstCoordinates n d ((sourceFirstCoordinates n d).symm y) ∈ O := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hy
  simpa only [comp_apply, ContinuousLinearEquiv.apply_symm_apply] using
    parameterSpatialJet_eq_native_evaluation hO hf hy' w

/-- One genuine coordinate word at an arbitrary joint derivative order. -/
theorem norm_original_spatial_word_le_native {n d q k : ℕ}
    {f : (Fin (n+d) → ℝ) → Fin q → ℝ} {O : Set (Fin (n+d) → ℝ)}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) {x : Fin (n+d) → ℝ} (hx : x ∈ O)
    (w : ParameterSpatialWord n) :
    ‖iteratedFDeriv ℝ k (parameterSpatialJet f w) x‖ ≤
      parameterSpatialCoordinateFactor n d q k *
        ‖iteratedFDeriv ℝ k (spatialNativeJet (f ∘ sourceFirstCoordinates n d))
          ((sourceFirstCoordinates n d).symm x)‖ := by
  let c := sourceFirstCoordinates n d
  rw [((original_spatial_word_eventuallyEq hO hf hx w).iteratedFDeriv ℝ k).eq_of_nhds]
  have ht := norm_iteratedFDeriv_comp_equiv_le c.symm
    (spatialJetEvaluation w ∘ spatialNativeJet (f ∘ c)) k x
  have hn := norm_iteratedFDeriv_spatialJetEvaluation_le (j := k)
    (sourceFirst_spatialNativeJet_contDiffAt hO hf hx) w
  apply ht.trans
  have hh := mul_le_mul_of_nonneg_right hn (linearModelFactor_nonneg c.symm k)
  convert hh using 1 <;> unfold parameterSpatialCoordinateFactor <;> ring

/-- Native estimates imply the literal original anisotropic coordinate bound.
This is the forward bridge needed after global finite-overlap gluing. -/
theorem parameterSpatialCj_le_of_native_bound {ι : Type*} [Fintype ι] {n d q : ℕ}
    (j : ℕ) (f : ι → (Fin (n+d) → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin (n+d) → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ i, ∀ k ≤ j, ∀ z : (Fin d → ℝ) × (Fin n → ℝ),
      sourceFirstCoordinates n d z ∈ S i →
        ‖iteratedFDeriv ℝ k (spatialNativeJet (f i ∘ sourceFirstCoordinates n d)) z‖ ≤ R) :
    parameterSpatialCj (n := n) (d := d) j f O S ≤
      ENNReal.ofReal (parameterSpatialCoordinateFactor n d q j * R) := by
  let c := sourceFirstCoordinates n d
  have hpacket (iw : ι × ParameterSpatialWord n) :
      ContDiffOn ℝ ∞ (parameterSpatialPacket (n := n) (d := d) f iw) (O iw.1) :=
    parameterSpatialJet_contDiffOn (hO iw.1) (hf iw.1) iw.2
  refine paperAtlasCj_le_of_jet_bound (ι := ι × ParameterSpatialWord n) (d := n+d) (q := q)
    j (parameterSpatialPacket (n := n) (d := d) f)
    (fun iw => O iw.1) (fun iw => S iw.1) (fun iw => hO iw.1)
    (fun iw => hSO iw.1) hpacket (parameterSpatialCoordinateFactor n d q j * R) ?_
  intro iw k hk x hx
  rcases iw with ⟨i,w⟩
  change ‖iteratedFDeriv ℝ k (parameterSpatialJet (f i) w) x‖ ≤ _
  have ht := norm_original_spatial_word_le_native (k := k) (hO i) (hf i) (hSO i hx) w
  have hb := hbound i k hk (c.symm x) (by
    change c (c.symm x) ∈ S i
    simpa only [c.apply_symm_apply] using hx)
  apply ht.trans
  exact mul_le_mul (parameterSpatialCoordinateFactor_mono n d q hk) hb
    (norm_nonneg _) (parameterSpatialCoordinateFactor_nonneg n d q j)

/-- The same forward bridge proves non-topness before taking real values. -/
theorem parameterSpatialCj_finite_and_bound_of_native {ι : Type*} [Fintype ι] {n d q : ℕ}
    (j : ℕ) (f : ι → (Fin (n+d) → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin (n+d) → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ i, ∀ k ≤ j, ∀ z : (Fin d → ℝ) × (Fin n → ℝ),
      sourceFirstCoordinates n d z ∈ S i →
        ‖iteratedFDeriv ℝ k (spatialNativeJet (f i ∘ sourceFirstCoordinates n d)) z‖ ≤ R) :
    parameterSpatialCj (n := n) (d := d) j f O S ≠ ⊤ ∧
      (parameterSpatialCj (n := n) (d := d) j f O S).toReal ≤
        parameterSpatialCoordinateFactor n d q j * R := by
  have h := parameterSpatialCj_le_of_native_bound j f O S hO hSO hf R hR hbound
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top h, ?_⟩
  exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h)
    ENNReal.ofReal_ne_top).mpr h |>.trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg (parameterSpatialCoordinateFactor_nonneg n d q j) hR))

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.parameterSpatialCj_native_jet_le
#print axioms GlobalEmbedding.Continuation.parameterSpatialCj_le_of_native_bound
#print axioms GlobalEmbedding.Continuation.parameterSpatialCj_finite_and_bound_of_native
