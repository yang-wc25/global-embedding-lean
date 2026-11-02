import GlobalEmbedding.Paper.BalancedVerticalC2Size
import GlobalEmbedding.Paper.BalancedDirectionalCalculus
import GlobalEmbedding.Paper.LinearMapLowerBoundPerturbation
import GlobalEmbedding.Paper.LeastSingularNormPerturbation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-!
# Actual correction bounds for the normalized free columns

Source: `main.tex`, `thm:free`, lines489–495. DAG: `free-correction-stability`.
Use the actual first and sorted second manifold derivatives and the accepted
vertical C² size. The near/far patch mask selects the columns divided by epsilon;
the genuine patch projection is retained in every column.
-/

noncomputable section
open scoped Manifold ContDiff BigOperators

namespace GlobalEmbedding.Paper

section ActualColumns

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The actual ordered pairing columns are additive on smooth maps and smooth fields.
Proof: use native manifold derivative addition, and apply it once more to the
actual smooth first derivative fields for each genuine sorted second column. -/
theorem free_pairing_columns_add [IsManifold I ∞ M] {a N : ℕ}
    (P U : M → EuclideanSpace ℝ (Fin N))
    (hP : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ P)
    (hU : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U)
    (D : Fin a → ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (x : M) :
    balancedPairingColumns (P + U) (fun i ↦ D i) x =
      balancedPairingColumns P (fun i ↦ D i) x +
        balancedPairingColumns U (fun i ↦ D i) x := by
  funext k
  cases k with
  | inl i =>
    exact balanced_directional_add P U (D i) x
      (hP.mdifferentiable (by simp) x) (hU.mdifferentiable (by simp) x)
  | inr ij =>
    have hadd : balancedDirectionalDerivative (P + U) (D ij.val.2) =
        balancedDirectionalDerivative P (D ij.val.2) +
          balancedDirectionalDerivative U (D ij.val.2) := by
      funext y
      exact balanced_directional_add P U (D ij.val.2) y
        (hP.mdifferentiable (by simp) y) (hU.mdifferentiable (by simp) y)
    change balancedDirectionalDerivative
      (balancedDirectionalDerivative (P + U) (D ij.val.2)) (D ij.val.1) x = _
    rw [hadd]
    exact balanced_directional_add _ _ (D ij.val.1) x
      ((balanced_directional_contMDiff P hP (D ij.val.2)).mdifferentiable (by simp) x)
      ((balanced_directional_contMDiff U hU (D ij.val.2)).mdifferentiable (by simp) x)

/-- The accepted actual vertical C² bound controls every first/sorted second column.
Proof: specialize the accepted component bound to the genuine column index. -/
theorem free_pairing_column_norm_le {a N : ℕ}
    (D : Fin a → ∀ x : M, TangentSpace I x)
    (U : M → EuclideanSpace ℝ (Fin N)) (x : M) {B : ℝ}
    (hB : balancedVerticalC2Size D U x ≤ B) (k : BalancedPairingIndex a) :
    ‖balancedPairingColumns U D x k‖ ≤ B := by
  have h := balancedVerticalC2Size_components_le D U x hB
  cases k with
  | inl i => exact h.2.1 i
  | inr ij => exact h.2.2 ij.val.1 ij.val.2

end ActualColumns

section Normalization

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ι : Type*}

/-- Actual projected columns, divided by epsilon precisely at the masked indices. -/
def freeNormalizedColumns (prj : V →L[ℝ] V) (masked : ι → Bool) (ε : ℝ)
    (v : ι → V) : ι → V := fun i ↦
  if masked i then ε⁻¹ • prj (v i) else prj (v i)

/-- Actual projection and normalization turn an epsilon-squared column error into
an epsilon error uniformly over both kinds of indices.
Proof: the projection is contractive; division costs exactly epsilon inverse
on the masked indices, while epsilon²≤epsilon on the unmasked indices. -/
theorem free_normalized_columns_error (prj : V →L[ℝ] V) (hprj : ‖prj‖ ≤ 1)
    (masked : ι → Bool) {ε C : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
    (v w : ι → V) (herr : ∀ i, ‖w i - v i‖ ≤ C * ε ^ 2) (i : ι) :
    ‖freeNormalizedColumns prj masked ε w i -
      freeNormalizedColumns prj masked ε v i‖ ≤ C * ε := by
  have hp : ‖prj (w i - v i)‖ ≤ C * ε ^ 2 := by
    calc
      _ ≤ ‖prj‖ * ‖w i - v i‖ := prj.le_opNorm _
      _ ≤ 1 * ‖w i - v i‖ := mul_le_mul_of_nonneg_right hprj (norm_nonneg _)
      _ ≤ _ := by simpa using herr i
  unfold freeNormalizedColumns
  split
  · rw [← smul_sub, ← map_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hε)]
    calc
      _ ≤ ε⁻¹ * (C * ε ^ 2) := mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hε.le)
      _ = C * ε := by field_simp
  · rw [← map_sub]
    exact hp.trans (mul_le_mul_of_nonneg_left (by nlinarith) hC)

end Normalization

section ColumnOperator

variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The actual finite column operator, with the original Euclidean coefficient norm. -/
def freeColumnOperator (v : ι → V) : EuclideanSpace ℝ ι →L[ℝ] V :=
  ∑ i, (EuclideanSpace.proj i).smulRight (v i)

/-- The actual column operator sends coefficients to their genuine linear combination. -/
theorem freeColumnOperator_apply (v : ι → V) (u : EuclideanSpace ℝ ι) :
    freeColumnOperator v u = ∑ i, (u i) • v i := by
  simp [freeColumnOperator]

/-- Uniform column bounds give an actual Euclidean operator norm bound.
Proof: sum the triangle estimates and bound each Euclidean coordinate by the
Euclidean vector norm. The empty index set also satisfies the estimate. -/
theorem freeColumnOperator_norm_le (v : ι → V) {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ i, ‖v i‖ ≤ B) : ‖freeColumnOperator v‖ ≤ (Fintype.card ι : ℝ) * B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [freeColumnOperator_apply]
  calc
    _ ≤ ∑ i, ‖(u i) • v i‖ := norm_sum_le _ _
    _ ≤ ∑ _ : ι, ‖u‖ * B := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le u i) (hv i) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

/-- The difference of actual column operators is the operator of actual column differences. -/
theorem freeColumnOperator_sub (v w : ι → V) :
    freeColumnOperator (w - v) = freeColumnOperator w - freeColumnOperator v := by
  ext u
  simp only [freeColumnOperator_apply, sub_apply, Pi.sub_apply, smul_sub,
    Finset.sum_sub_distrib]

/-- Actual column independence is exactly injectivity of the Euclidean column operator.
Proof: use the finite linear-combination criterion, with the genuine Euclidean
coefficient vector identified by its actual coordinates. -/
theorem freeColumnOperator_injective_iff (v : ι → V) :
    Function.Injective (freeColumnOperator v) ↔ LinearIndependent ℝ v := by
  constructor
  · intro hinj
    apply Fintype.linearIndependent_iff.mpr
    intro g hg i
    have hzero : freeColumnOperator v (WithLp.toLp 2 g) = 0 := by
      simpa [freeColumnOperator_apply] using hg
    have hu : WithLp.toLp 2 g = 0 := hinj (by simpa using hzero)
    exact congrArg (fun u : EuclideanSpace ℝ ι ↦ u i) hu
  · intro hv
    apply (injective_iff_map_eq_zero (freeColumnOperator v)).mpr
    intro u hu
    have hg := Fintype.linearIndependent_iff.mp hv (fun i ↦ u i)
      (by simpa [freeColumnOperator_apply] using hu)
    ext i
    exact hg i

/-- The actual normalized operator error follows from the individual actual column errors.
Proof: use the genuine column-operator difference and its finite Euclidean norm bound. -/
theorem free_normalized_column_operator_error (prj : V →L[ℝ] V) (hprj : ‖prj‖ ≤ 1)
    (masked : ι → Bool) {ε C : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
    (v w : ι → V) (herr : ∀ i, ‖w i - v i‖ ≤ C * ε ^ 2) :
    ‖freeColumnOperator (freeNormalizedColumns prj masked ε w) -
      freeColumnOperator (freeNormalizedColumns prj masked ε v)‖ ≤
        (Fintype.card ι : ℝ) * C * ε := by
  rw [← freeColumnOperator_sub]
  exact (freeColumnOperator_norm_le _ (mul_nonneg hC hε.le)
    (free_normalized_columns_error prj hprj masked hε hε1 hC v w herr)).trans_eq
      (by ring)

omit [Fintype ι] in
/-- Independence after actual projection and nonzero diagonal normalization implies
independence of the original columns.
Proof: multiply each normalized column by the inverse unit scale, then use
Mathlib's independence-under-linear-image implication for the actual projection. -/
theorem free_columns_independent_of_normalized (prj : V →L[ℝ] V) (masked : ι → Bool)
    {ε : ℝ} (hε : ε ≠ 0) (v : ι → V)
    (hv : LinearIndependent ℝ (freeNormalizedColumns prj masked ε v)) :
    LinearIndependent ℝ v := by
  classical
  let units : ι → ℝˣ := fun i ↦ if masked i then Units.mk0 ε hε else 1
  have hp : LinearIndependent ℝ (fun i ↦ prj (v i)) := by
    convert hv.units_smul units using 1
    funext i
    change prj (v i) = (units i) • freeNormalizedColumns prj masked ε v i
    dsimp only [freeNormalizedColumns, units]
    split <;> simp_all [smul_smul]
  exact hp.of_comp prj.toLinearMap

end ColumnOperator

section CompactMargins

variable {Q V W : Type*} [TopologicalSpace Q]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Actual continuous injective operators on a compact patch have one positive rank margin.
Proof: the accepted actual least singular norm is continuous and positive at
every injective operator. Minimize it on the compact patch; an empty patch uses1. -/
theorem free_compact_injective_lower_bound {K : Set Q} (hK : IsCompact K)
    (A : Q → V →L[ℝ] W) (hA : ContinuousOn A K)
    (hinj : ∀ x ∈ K, Function.Injective (A x)) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x ∈ K, ∀ u, μ * ‖u‖ ≤ ‖A x u‖ := by
  have hc : ContinuousOn (fun x ↦ leastSingularNorm (A x)) K :=
    least_singular_norm_perturbation.2.2.comp_continuousOn hA
  have hp (x) (hx : x ∈ K) : 0 < leastSingularNorm (A x) :=
    (least_singular_norm_attainment (A x)).2.2.mpr (hinj x hx)
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hc
    refine ⟨leastSingularNorm (A x), hp x hx, ?_⟩
    intro y hy u
    exact (mul_le_mul_of_nonneg_right (hmin hy) (norm_nonneg u)).trans
      ((least_singular_norm_bound (A y)).2.1 u)
  · exact ⟨1, by norm_num, fun x hx ↦ (hne ⟨x, hx⟩).elim⟩

end CompactMargins

section ActualError

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The actual balanced vertical C² correction estimate gives the genuine normalized
operator error, including all first and sorted second derivatives.
Proof: actual native derivative additivity identifies the column difference with
the columns of U. The accepted C² component bound and actual projection/scale
estimate then give the claimed Euclidean operator bound. -/
theorem free_actual_normalized_column_error {a N : ℕ}
    (P U : M → EuclideanSpace ℝ (Fin N))
    (hP : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ P)
    (hU : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U)
    (D : Fin a → ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (x : M)
    (prj : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (hprj : ‖prj‖ ≤ 1) (masked : BalancedPairingIndex a → Bool)
    {ε C : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
    (hbound : balancedVerticalC2Size (fun i ↦ D i) U x ≤ C * ε ^ 2) :
    ‖freeColumnOperator (freeNormalizedColumns prj masked ε
        (balancedPairingColumns (P + U) (fun i ↦ D i) x)) -
      freeColumnOperator (freeNormalizedColumns prj masked ε
        (balancedPairingColumns P (fun i ↦ D i) x))‖ ≤
      (Fintype.card (BalancedPairingIndex a) : ℝ) * C * ε := by
  apply free_normalized_column_operator_error prj hprj masked hε hε1 hC
  intro k
  rw [free_pairing_columns_add P U hP hU D x, Pi.add_apply, add_sub_cancel_left]
  exact free_pairing_column_norm_le (fun i ↦ D i) U x hbound k

/-- One common small positive epsilon preserves actual corrected column independence
at every point of every patch with the common normalized lower bound.
Proof: choose a single threshold using the shared finite column count, C, and μ.
The actual C² estimate gives an operator error at most μ/2, so the accepted
operator perturbation theorem leaves a positive μ/2 lower bound. Undo actual
projection and nonzero diagonal normalization to recover all original columns. -/
theorem free_actual_correction_rank_stability {a N : ℕ} {Patch : Type*}
    (D : Fin a → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    {C μ εbar : ℝ}
    (P U : ℝ → M → EuclideanSpace ℝ (Fin N))
    (hP : ∀ ε, 0 < ε → ε < εbar →
      ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (P ε))
    (hU : ∀ ε, 0 < ε → ε < εbar →
      ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (U ε))
    (K : Patch → Set M)
    (prj : Patch → M → EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (masked : Patch → BalancedPairingIndex a → Bool)
    (hprj : ∀ p x, x ∈ K p → ‖prj p x‖ ≤ 1)
    (hC : 0 ≤ C) (hμ : 0 < μ) (hbar : 0 < εbar)
    (hbound : ∀ ε, 0 < ε → ε < εbar → ∀ p x, x ∈ K p →
      balancedVerticalC2Size (fun i ↦ D i) (U ε) x ≤ C * ε ^ 2)
    (hmargin : ∀ ε, 0 < ε → ε < εbar → ∀ p x, x ∈ K p →
      ∀ u, μ * ‖u‖ ≤ ‖freeColumnOperator
        (freeNormalizedColumns (prj p x) (masked p) ε
          (balancedPairingColumns (P ε) (fun i ↦ D i) x)) u‖) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ εbar ∧ ∀ ε, 0 < ε → ε < ε₀ → ∀ p x, x ∈ K p →
      LinearIndependent ℝ (balancedPairingColumns (P ε + U ε) (fun i ↦ D i) x) := by
  let L : ℝ := (Fintype.card (BalancedPairingIndex a) : ℝ) * C
  have hL : 0 ≤ L := mul_nonneg (Nat.cast_nonneg _) hC
  let ρ := μ / (2 * (L + 1))
  have hρ : 0 < ρ := div_pos hμ (by positivity)
  refine ⟨min εbar (min 1 ρ), lt_min hbar (lt_min (by norm_num) hρ), min_le_left _ _, ?_⟩
  intro ε hε hsmall p x hx
  have hb : ε < εbar := lt_of_lt_of_le hsmall (min_le_left _ _)
  have hε1 : ε ≤ 1 := (lt_of_lt_of_le hsmall
    ((min_le_right _ _).trans (min_le_left _ _))).le
  have heρ : ε < ρ := lt_of_lt_of_le hsmall
    ((min_le_right _ _).trans (min_le_right _ _))
  have hgap : L * ε ≤ μ / 2 := by
    have hh := (lt_div_iff₀ (show 0 < 2 * (L + 1) by positivity)).mp heρ
    nlinarith
  let A := freeColumnOperator (freeNormalizedColumns (prj p x) (masked p) ε
    (balancedPairingColumns (P ε) (fun i ↦ D i) x))
  let B := freeColumnOperator (freeNormalizedColumns (prj p x) (masked p) ε
    (balancedPairingColumns (P ε + U ε) (fun i ↦ D i) x))
  have herr : ‖A - B‖ ≤ μ / 2 := by
    rw [norm_sub_rev]
    exact (free_actual_normalized_column_error (P ε) (U ε) (hP ε hε hb) (hU ε hε hb) D x
      (prj p x) (hprj p x hx) (masked p) hε hε1 hC (hbound ε hε hb p x hx)).trans hgap
  have hlower (u) : (μ / 2) * ‖u‖ ≤ ‖B u‖ := by
    have hh := linear_map_lower_bound_perturbation A B μ (μ / 2)
      (hmargin ε hε hb p x hx) herr u
    convert hh using 1; ring
  have hinj : Function.Injective B := by
    apply (injective_iff_map_eq_zero B).mpr
    intro u hu
    have hh := hlower u
    rw [hu, norm_zero] at hh
    by_contra hzero
    exact (not_lt_of_ge hh) (mul_pos (by linarith) (norm_pos_iff.mpr hzero))
  exact free_columns_independent_of_normalized (prj p x) (masked p) hε.ne' _
    ((freeColumnOperator_injective_iff _).mp hinj)

end ActualError

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.free_pairing_columns_add
#print axioms GlobalEmbedding.Paper.free_pairing_column_norm_le
#print axioms GlobalEmbedding.Paper.freeNormalizedColumns
#print axioms GlobalEmbedding.Paper.free_normalized_columns_error
#print axioms GlobalEmbedding.Paper.freeColumnOperator
#print axioms GlobalEmbedding.Paper.freeColumnOperator_apply
#print axioms GlobalEmbedding.Paper.freeColumnOperator_norm_le
#print axioms GlobalEmbedding.Paper.freeColumnOperator_sub
#print axioms GlobalEmbedding.Paper.freeColumnOperator_injective_iff
#print axioms GlobalEmbedding.Paper.free_normalized_column_operator_error
#print axioms GlobalEmbedding.Paper.free_columns_independent_of_normalized
#print axioms GlobalEmbedding.Paper.free_compact_injective_lower_bound
#print axioms GlobalEmbedding.Paper.free_actual_normalized_column_error
#print axioms GlobalEmbedding.Paper.free_actual_correction_rank_stability
