import Upgrade.SupportedValueParameterTransport

/-!
# Actual value responses with the weights canceled in parameter directions

The prepared value frame is unweighted and fixed before the global wave list
and returned frequencies. Multiplication of an already differentiated column
by -lambda² cancels its principal -lambda⁻² factor. Only the genuine global
response errors acquire this fixed multiplier. No fast-angle coefficient is
differentiated, and no prepared neighborhood is shrunk after probes returns.
-/

noncomputable section
open Bundle Manifold Set Module Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper GlobalEmbedding.Offline

private theorem norm_weight_canceled_column
    {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : P →L[ℝ] W) (d : P) (v : W) (lam c : ℝ) (hlam : lam ≠ 0) :
    ‖L (-(lam ^ 2) • d) - c • v‖ =
      lam ^ 2 * ‖L d - c • (-((lam ^ 2)⁻¹) • v)‖ := by
  have he : -(lam ^ 2) * c * -((lam ^ 2)⁻¹) = c := by
    field_simp [hlam]
  have hid : L (-(lam ^ 2) • d) - c • v =
      -(lam ^ 2) • (L d - c • (-((lam ^ 2)⁻¹) • v)) := by
    rw [map_smul, smul_sub, smul_smul, smul_smul, he]
  rw [hid, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (sq_nonneg lam)]

private theorem value_probeTrig_abs_le_one (b : Bool) (θ : ℝ) :
    |probeTrig b θ| ≤ 1 := by
  cases b
  · exact Real.abs_cos_le_one θ
  · exact Real.abs_sin_le_one θ

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Actual parameter directions cancel the returned weight while preserving
the same unweighted geometric value field. -/
theorem ExactProbeFamily.value_unweighted_response
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))}
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius) (l : Fin r) (b : Bool) (z : M) :
    ‖fderiv ℝ (fun v ↦ probe.map t v z) u (-(probe.weight l ^ 2) • Pi.single (l,b) 1) -
      (t ^ ((56 : ℝ) / 5) * probeTrig b (probe.weight l * (waves l).phase z /
        t ^ ((6 : ℝ) / 5))) • (waves l).value z‖ ≤
      t ^ ((56 : ℝ) / 5) * (probe.weight l ^ 2 * (probe.etaV t + probe.constant * ‖u‖)) := by
  rw [norm_weight_canceled_column _ _ _ _ _ (probe.weight_pos l).ne']
  exact (mul_le_mul_of_nonneg_left
    (probe.value_response_principal t ht htt u hu l b z) (sq_nonneg _)).trans_eq (by ring)

/-- At the second point the whole actual derivative remains. Multiplication
of the parameter direction by -lambda² scales this genuine global tail. -/
theorem ExactProbeFamily.value_unweighted_response_away
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))}
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius) (l : Fin r) (b : Bool) (z : M)
    (haway : (waves l).cutoff z = 0) :
    ‖fderiv ℝ (fun v ↦ probe.map t v z) u (-(probe.weight l ^ 2) • Pi.single (l,b) 1)‖ ≤
      t ^ ((56 : ℝ) / 5) * (probe.weight l ^ 2 * (probe.etaV t + probe.constant * ‖u‖)) := by
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (sq_nonneg _)]
  exact (mul_le_mul_of_nonneg_left
    (probe.value_response_away t ht htt u hu l b z haway) (sq_nonneg _)).trans_eq (by ring)

/-- Comparison with the unweighted center value retains its actual variation.
The resulting beta can be chosen before the probe weights and parameter count. -/
theorem ExactProbeFamily.value_unweighted_response_reference
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))}
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius) (l : Fin r) (b : Bool) (z : M)
    (vref : V) (β : ℝ) (hβ : ‖(waves l).value z - vref‖ ≤ β) :
    ‖fderiv ℝ (fun v ↦ probe.map t v z) u (-(probe.weight l ^ 2) • Pi.single (l,b) 1) -
      (t ^ ((56 : ℝ) / 5) * probeTrig b (probe.weight l * (waves l).phase z /
        t ^ ((6 : ℝ) / 5))) • vref‖ ≤
      t ^ ((56 : ℝ) / 5) *
        (probe.weight l ^ 2 * (probe.etaV t + probe.constant * ‖u‖) + β) := by
  let a := t ^ ((56 : ℝ) / 5)
  let θ := probe.weight l * (waves l).phase z / t ^ ((6 : ℝ) / 5)
  have ha : 0 ≤ a := Real.rpow_nonneg ht.le _
  have hscale : |a * probeTrig b θ| ≤ a := by
    rw [abs_mul, abs_of_nonneg ha]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (value_probeTrig_abs_le_one b θ) ha
  have hvar : ‖(a * probeTrig b θ) • (waves l).value z - (a * probeTrig b θ) • vref‖ ≤ a * β := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hscale hβ (norm_nonneg _) ha
  have hraw := probe.value_unweighted_response t ht htt u hu l b z
  have herr := (norm_sub_le_norm_sub_add_norm_sub
    (fderiv ℝ (fun v ↦ probe.map t v z) u (-(probe.weight l ^ 2) • Pi.single (l,b) 1))
    ((a * probeTrig b θ) • (waves l).value z) ((a * probeTrig b θ) • vref)).trans
      (add_le_add hraw hvar)
  exact herr.trans_eq (mul_add a _ β).symm

#print axioms ExactProbeFamily.value_unweighted_response
#print axioms ExactProbeFamily.value_unweighted_response_away
#print axioms ExactProbeFamily.value_unweighted_response_reference

end GlobalEmbedding.Upgrade
