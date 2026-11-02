import Probes.ActualFullProbeFirstStep
import Probes.ActualEuclideanProbeHigherBounds

/-!
# Uniform native higher jets of the actual complete homogeneous first block

The free and BOTH original reconstructed channels are bounded in the actual
Euclidean target norm. The explicit finite constant includes the dictionary
sum and the true finite parameter dimension. It controls every spatial order
up to j and native parameter differentiation after each such spatial jet.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Continuation Set Manifold
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Offline

/-- One scale-independent constant for the entire actual finite first block. -/
def actualFullProbeJetConstant (m N p j order : ℕ) {r : ℕ}
    (weight Mphase Kfree Ksource : Fin r → ℝ) (Mg : ℝ) : ℝ :=
  euclideanFiniteProbeJetConstant N j weight Mphase Kfree +
    (p : ℝ) * ∑ l, actualRealHomogeneousConstant m N j order Mg (Ksource l) (Mphase l)

theorem actualFullProbeJetConstant_nonneg (m N p j order : ℕ) {r : ℕ}
    (weight Mphase Kfree Ksource : Fin r → ℝ) (Mg : ℝ)
    (hMg : 0 ≤ Mg) (hf : ∀ l, 0 ≤ Kfree l) (hs : ∀ l, 0 ≤ Ksource l) :
    0 ≤ actualFullProbeJetConstant m N p j order weight Mphase Kfree Ksource Mg :=
  add_nonneg (euclideanFiniteProbeJetConstant_nonneg N j weight Mphase Kfree hf)
    (mul_nonneg (Nat.cast_nonneg p) (Finset.sum_nonneg fun l _ ↦
      actualRealHomogeneousConstant_nonneg m N j order Mg (Ksource l) (Mphase l) hMg (hs l)))

/-- Native finite-column norm bookkeeping is separate from geometric
reconstruction, so it introduces no norm-instance conversion. -/
theorem weighted_finite_probe_jet_map_bound
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {p r : ℕ}
    (L : (Fin p → ℝ) →L[ℝ] Y) (R : Fin r → Fin p → Y)
    (q d Cfree : ℝ) (Cr : Fin r → ℝ) (hq : 0 ≤ q)
    (hf : q * ‖L‖ ≤ d * Cfree)
    (hr : ∀ l a, q * ‖R l a‖ ≤ d * Cr l) :
    q * ‖L + ∑ l, probeColumnMap (R l)‖ ≤
      d * (Cfree + (p : ℝ) * ∑ l, Cr l) := by
  have hs (l : Fin r) : q * ‖probeColumnMap (R l)‖ ≤ (p : ℝ) * (d * Cr l) := by
    have hh := weighted_norm_probeColumnMap_le (R l) q hq (fun _ ↦ d * Cr l) (hr l)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
  have hsum : q * ‖∑ l, probeColumnMap (R l)‖ ≤ d * ((p : ℝ) * ∑ l, Cr l) := by
    calc
      _ ≤ q * ∑ l, ‖probeColumnMap (R l)‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hq
      _ = ∑ l, q * ‖probeColumnMap (R l)‖ := Finset.mul_sum _ _ _
      _ ≤ ∑ l, (p : ℝ) * (d * Cr l) := Finset.sum_le_sum (fun l _ ↦ hs l)
      _ = _ := by simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring
  calc
    _ ≤ q * (‖L‖ + ‖∑ l, probeColumnMap (R l)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) hq
    _ = q * ‖L‖ + q * ‖∑ l, probeColumnMap (R l)‖ := by ring
    _ ≤ d * Cfree + d * ((p : ℝ) * ∑ l, Cr l) := add_le_add hf hsum
    _ = _ := by ring

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Cdata" => Fin (m + 1) → ℂ

/-- The full homogeneous first-step family and its ACTUAL native parameter
response have one uniform finite constant at every order n≤j. Source budgets
are on the original source, with the same solver order p at every observation.
There is no bound on a desired correction among the hypotheses. -/
theorem actualFullProbe_uniform_weighted_jets
    (label : (Fin r × Bool) ↪ Fin p) (δ τ ell : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → D → ℝ) (amplitude : Fin r → D → V)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (j order : ℕ) (k : Fin r → Fin p → D → Cdata)
    (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (hphaseSmooth : ∀ l, ContDiffOn ℝ ∞ (phase l) O)
    (hamplitude : ∀ l, ContDiffOn ℝ ∞ (amplitude l) O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) O)
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (hk : ∀ l q, ContDiffOn ℝ ∞ (k l q) O)
    (Mg : ℝ) (Kfree Ksource Mphase : Fin r → ℝ)
    (hδ : 0 ≤ δ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hτ : 0 < τ) (hτell : τ ≤ ell) (hMg : 0 ≤ Mg)
    (hKfree : ∀ l, 0 ≤ Kfree l) (hKsource : ∀ l, 0 ≤ Ksource l)
    (hAb : ∀ a ≤ j+order+1, ∀ y ∈ S,
      ell ^ a * ‖iteratedFDeriv ℝ a (incrementsModeComplexFirstOrderA F hF c) y‖ ≤ Mg)
    (hBb : ∀ a ≤ j+order+1, ∀ y ∈ S,
      ell ^ a * ‖iteratedFDeriv ℝ a (incrementsModeComplexFirstOrderB F hF c) y‖ ≤ Mg)
    (hGb : ∀ a ≤ j, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (fun z ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) z)) y‖ ≤ Mg)
    (hJb : ∀ a ≤ j, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (fun z ↦ (normalSpace (I := I) F (c z)).subtypeL.comp
        (incrementsModeCoordinateJ F hF c z)) y‖ ≤ Mg)
    (hT0b : ∀ a ≤ j, ∀ y ∈ S,
      ell ^ a * ‖iteratedFDeriv ℝ a (incrementsModeTransverseValue F c) y‖ ≤ Mg)
    (hkb : ∀ l q a, a ≤ j+order+1 → ∀ y ∈ S,
      ell ^ a * ‖iteratedFDeriv ℝ a (k l q) y‖ ≤ Ksource l * δ * τ)
    (hphase : ∀ l a, a < j → ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ (a+1) (fun z ↦ weight l * phase l z) y‖ ≤ Mphase l)
    (hamp : ∀ l a, a ≤ j → ∀ y ∈ S,
      ell ^ a * ‖iteratedFDeriv ℝ a (amplitude l) y‖ ≤ Kfree l) :
    let C := actualFullProbeJetConstant m N p j order weight Mphase Kfree Ksource Mg
    ∀ n ≤ j, ∀ x ∈ S, ∀ u : Fin p → ℝ,
      (τ ^ n * ‖fderiv ℝ (fun w ↦ iteratedFDeriv ℝ n
        (actualFiniteProbeWithReconstruction label δ τ weight phase amplitude F hF c order k w) x) u‖ ≤
        (δ * τ) * C) ∧
      (τ ^ n * ‖iteratedFDeriv ℝ n
        (actualFiniteProbeWithReconstruction label δ τ weight phase amplitude F hF c order k u) x‖ ≤
        ‖u‖ * (δ * τ) * C) := by
  dsimp only
  intro n hn x hx u
  let Cfree := euclideanFiniteProbeJetConstant N j weight Mphase Kfree
  let Cr (l : Fin r) := actualRealHomogeneousConstant m N j order Mg (Ksource l) (Mphase l)
  let Cmap : (Fin p → ℝ) →L[ℝ] D [×n]→L[ℝ] V := probePairedColumnMap label
    (fun i ↦ iteratedFDeriv ℝ n (actualProbeCosColumn δ τ (weight i) (phase i) (amplitude i)) x)
    (fun i ↦ iteratedFDeriv ℝ n (actualProbeSinColumn δ τ (weight i) (phase i) (amplitude i)) x)
  let Rmap (l : Fin r) : (Fin p → ℝ) →L[ℝ] D [×n]→L[ℝ] V :=
    probeColumnMap (fun q ↦ iteratedFDeriv ℝ n
      (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y) F hF c τ order (k l q)) x)
  have hf : τ ^ n * ‖Cmap‖ ≤ (δ * τ) * Cfree :=
    actualEuclideanFreeProbeJetMap_weighted_bound j n hn O hO label weight phase amplitude
      hphaseSmooth hamplitude x (hSO hx) δ τ ell Mphase Kfree hδ hτ hτell hell1 hKfree
      (fun l a ha ↦ hphase l a ha x hx) (fun l a ha ↦ hamp l a ha x hx)
  have hrc (l : Fin r) (q : Fin p) : τ ^ n * ‖iteratedFDeriv ℝ n
      (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y) F hF c τ order (k l q)) x‖ ≤
      Cr l * δ * τ := by
    have hh := actualRealHomogeneousProbe_weighted_bounds (fun y ↦ weight l * phase l y)
      F hF c j order O S hO hSO ((hphaseSmooth l).const_smul (weight l))
      hA hB hG hJ hT0 (k l q) (hk l q) δ ell τ Mg (Ksource l) (Mphase l)
      hδ hell hell1 hτ hτell hMg (hKsource l) hAb hBb hGb hJb hT0b (hkb l q) (hphase l) n hn x hx
    apply hh.trans
    change Cr l * δ * τ ^ 2 / ell ≤ Cr l * δ * τ
    have hCr : 0 ≤ Cr l := actualRealHomogeneousConstant_nonneg m N j order Mg (Ksource l)
      (Mphase l) hMg (hKsource l)
    calc
      _ = (Cr l * δ * τ) * (τ / ell) := by ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) ((div_le_one hell).mpr hτell)
  have hmap : τ ^ n * ‖actualReconstructedProbeJetMap label δ τ weight phase amplitude F hF c order k n x‖ ≤
      (δ * τ) * actualFullProbeJetConstant m N p j order weight Mphase Kfree Ksource Mg := by
    apply weighted_finite_probe_jet_map_bound Cmap
      (fun l q ↦ iteratedFDeriv ℝ n
        (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y) F hF c τ order (k l q)) x)
      (τ ^ n) (δ * τ) Cfree Cr (pow_nonneg hτ.le n) hf
    intro l q
    convert hrc l q using 1 <;> ring
  constructor
  · rw [(hasFDerivAt_actualFiniteProbeWithReconstruction_spatial_jet label δ τ weight phase amplitude
      F hF c order k O hO hphaseSmooth hamplitude hA hB hG hJ hT0 hk n u x (hSO hx)).fderiv]
    exact hmap
  · rw [actualFiniteProbeWithReconstruction_spatial_jet label δ τ weight phase amplitude
      F hF c order k O hO hphaseSmooth hamplitude hA hB hG hJ hT0 hk n u x (hSO hx)]
    calc
      _ ≤ τ ^ n * (‖actualReconstructedProbeJetMap label δ τ weight phase amplitude F hF c order k n x‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left
          ((actualReconstructedProbeJetMap label δ τ weight phase amplitude F hF c order k n x).le_opNorm u)
          (pow_nonneg hτ.le n)
      _ = ‖u‖ * (τ ^ n * ‖actualReconstructedProbeJetMap label δ τ weight phase amplitude F hF c order k n x‖) := by ring
      _ ≤ ‖u‖ * ((δ * τ) * actualFullProbeJetConstant m N p j order weight Mphase Kfree Ksource Mg) :=
        mul_le_mul_of_nonneg_left hmap (norm_nonneg _)
      _ = _ := by ring

/-- Native order-three conversion: plugging the proved full-family weighted
bound above gives exactly the original delta/tau² scale, for values AND for
their actual parameter derivative. -/
theorem probe_third_scale_of_weighted {Z : Type*} [SeminormedAddCommGroup Z]
    (z : Z) (δ τ C : ℝ) (hτ : 0 < τ) (h : τ ^ 3 * ‖z‖ ≤ (δ * τ) * C) :
    ‖z‖ ≤ C * (δ / τ ^ 2) := by
  apply (mul_le_mul_iff_right₀ (pow_pos hτ 3)).mp
  apply h.trans_eq
  field_simp

#print axioms actualFullProbe_uniform_weighted_jets
#print axioms probe_third_scale_of_weighted
end GlobalEmbedding.Offline
