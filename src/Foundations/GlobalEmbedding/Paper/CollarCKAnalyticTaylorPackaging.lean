import GlobalEmbedding.Paper.CollarCKSpatialFormalSolution
import GlobalEmbedding.Paper.CollarCKAnalyticCoefficientRealization
import GlobalEmbedding.Paper.CollarCKAnalyticCoefficientBound
import GlobalEmbedding.Paper.CollarCKAnalyticNormalization

/-!
# Genuine analytic coefficients in the canonical CK RHS

Source: Gantumur, notes2, Theorem 18, printed pp. 9–10. The multilinear Taylor coefficients
already contain the Taylor normalization. A commutative monomial coefficient is the sum over
ordered coordinate words with its multiplicities, with no further factorial. The formal RHS
carrier is exactly the existing `CollarCKRHS`; the coordinate monomials are the accepted W5 ones.
-/

noncomputable section
open scoped BigOperators
namespace GlobalEmbedding.Paper

section Coordinates

variable {n m : ℕ}

/-- Explicit coordinates for the original spatial/time/value/first-spatial-jet RHS arguments.
Source: Gantumur, Theorem 18. This is an actual continuous linear equivalence, not a norm identity.
Spatial arguments are grouped first; the remaining slots are exactly the canonical W3 slots. -/
def collarCKRHSCoordinates :
    ((Fin n ⊕ CollarCKSlot n m) → ℝ) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n) × ℝ × (Fin m → ℝ) × (Fin n → Fin m → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun z ↦ (WithLp.toLp 2 (fun i ↦ z (Sum.inl i)),
        z (Sum.inr (Sum.inl ())), fun j ↦ z (Sum.inr (Sum.inr (Sum.inl j))),
        fun i j ↦ z (Sum.inr (Sum.inr (Sum.inr (i, j)))))
      invFun := fun z ↦ Sum.elim (fun i ↦ z.1 i)
        (Sum.elim (fun _ ↦ z.2.1)
          (Sum.elim (fun j ↦ z.2.2.1 j) (fun ij ↦ z.2.2.2 ij.1 ij.2)))
      left_inv := by
        intro z
        funext i
        rcases i with i | (_ | (j | ⟨i, j⟩)) <;> rfl
      right_inv := by intro z; rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

end Coordinates

section Coefficients

variable {σ F : Type*} [Fintype σ] [DecidableEq σ]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Reusing the accepted coordinate series recovers any actual multilinear series exactly.
Source: Gantumur, Theorem 18, Taylor expansion in all finite coordinates.
Expand every input into coordinate basis vectors by the native multilinear finite-sum theorem,
and move its scalar factors outside by the native multilinear scalar-product identity. -/
theorem collarCKCoordinateSeries_basis
    (p : FormalMultilinearSeries ℝ (σ → ℝ) F) :
    collarCKCoordinateSeries (fun k w ↦ p k (fun i ↦ Pi.single (w i) 1)) = p := by
  classical
  funext k
  ext z
  have hz : z = fun i ↦ ∑ a : σ, z i a • Pi.single a (1 : ℝ) := by
    funext i a
    simp [Pi.single_apply]
  rw [collarCKCoordinateSeries]
  simp only [sum_apply, collarCKCoordinateMonomial_apply]
  calc
    _ = ∑ w : Fin k → σ, p k (fun i ↦ z i (w i) • Pi.single (w i) 1) := by
      apply Finset.sum_congr rfl
      intro w _
      exact ((p k).toMultilinearMap.map_smul_univ (fun i ↦ z i (w i))
        (fun i ↦ Pi.single (w i) 1)).symm
    _ = p k (fun i ↦ ∑ a : σ, z i a • Pi.single a 1) :=
      ((p k).toMultilinearMap.map_sum (fun i a ↦ z i a • Pi.single a 1)).symm
    _ = p k z := congrArg (p k) hz.symm

/-- The multiplicities of an actual coordinate word, using native finitely supported indices.
Source: Gantumur, Theorem 18, commutative Taylor monomials. -/
def collarCKWordIndex {k : ℕ} (w : Fin k → σ) : σ →₀ ℕ :=
  ∑ i, Finsupp.single (w i) 1

omit [Fintype σ] [DecidableEq σ] in
/-- A word of length `k` has total degree `k`, including the empty word. -/
theorem collarCKWordIndex_degree {k : ℕ} (w : Fin k → σ) :
    (collarCKWordIndex w).degree = k := by
  classical
  simp [collarCKWordIndex, map_sum]

omit [Fintype σ] [DecidableEq σ] in
/-- Grouping a coordinate word into its multiplicities preserves its literal monomial.
Source: Gantumur, commutative Taylor expansion. The native finitely supported product rule
turns addition of exponents into multiplication, including the empty product. -/
theorem collarCKWordIndex_prod {k : ℕ} (w : Fin k → σ) (z : σ → ℝ) :
    (collarCKWordIndex w).prod (fun a e ↦ z a ^ e) = ∏ i, z (w i) := by
  classical
  unfold collarCKWordIndex
  rw [← Finsupp.prod_finsetSum_index (fun a ↦ pow_zero (z a))
    (fun a b c ↦ pow_add (z a) b c)]
  simp [Finsupp.prod_single_index]

/-- The exact finite set of words contributing to one commutative Taylor coefficient.
Source: Gantumur, Theorem 18, Taylor expansion with the existing normalized multilinear terms. -/
def collarCKWordFiber (d : σ →₀ ℕ) : Finset (Fin d.degree → σ) := by
  classical
  exact Finset.univ.filter (fun w ↦ collarCKWordIndex w = d)

/-- The unscaled, genuine Taylor coefficient is a finite word-fiber sum, with no extra factorial.
Source: Gantumur, Theorem 18. -/
def collarCKTaylorCoeff (p : FormalMultilinearSeries ℝ (σ → ℝ) F) (d : σ →₀ ℕ) : F :=
  ∑ w ∈ collarCKWordFiber d, p d.degree (fun i ↦ Pi.single (w i) 1)

/-- A zero constant multilinear term gives the actual zero origin coefficient.
Source: the zero-origin normalization in Gantumur, Theorem 18. This does not assert that the
normal-zero coefficient vanishes as an entire spatial power series. -/
theorem collarCKTaylorCoeff_zero (p : FormalMultilinearSeries ℝ (σ → ℝ) F)
    (hp : ∀ v, p 0 v = 0) : collarCKTaylorCoeff p 0 = 0 := by
  unfold collarCKTaylorCoeff
  apply Finset.sum_eq_zero
  intro w _
  exact hp _

/-- The grouped Taylor coefficients represent the very same homogeneous analytic term.
Source: Gantumur, Theorem 18. Partition the finite set of words by their native multiindices;
each fiber has one common coordinate monomial, and its coefficient is the prescribed sum. -/
theorem collarCKTaylorCoeff_homogeneous
    (p : FormalMultilinearSeries ℝ (σ → ℝ) F) (k : ℕ) (z : σ → ℝ) :
    p k (fun _ ↦ z) =
      ∑ d ∈ Finset.univ.image (collarCKWordIndex (σ := σ) (k := k)),
        (d.prod (fun a e ↦ z a ^ e)) • collarCKTaylorCoeff p d := by
  classical
  have hexpand : p k (fun _ ↦ z) =
      ∑ w : Fin k → σ, (∏ i, z (w i)) • p k (fun i ↦ Pi.single (w i) 1) := by
    calc
      _ = collarCKCoordinateSeries
          (fun k w ↦ p k (fun i ↦ Pi.single (w i) 1)) k (fun _ ↦ z) :=
        congrArg (fun q : FormalMultilinearSeries ℝ (σ → ℝ) F ↦ q k (fun _ ↦ z))
          (collarCKCoordinateSeries_basis p).symm
      _ = _ := collarCKCoordinateSeries_apply _ _ _
  rw [hexpand]
  symm
  calc
    _ = ∑ d ∈ Finset.univ.image (collarCKWordIndex (σ := σ) (k := k)),
        ∑ w ∈ Finset.univ.filter (fun w : Fin k → σ ↦ collarCKWordIndex w = d),
          (∏ i, z (w i)) • p k (fun i ↦ Pi.single (w i) 1) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdegree : d.degree = k := by
        obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hd
        exact collarCKWordIndex_degree v
      subst k
      simp only [collarCKTaylorCoeff, collarCKWordFiber, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      have hmon : d.prod (fun a e ↦ z a ^ e) = ∏ i, z (v i) := by
        calc
          _ = (collarCKWordIndex v).prod (fun a e ↦ z a ^ e) :=
            congrArg (fun b : σ →₀ ℕ ↦ b.prod (fun a e ↦ z a ^ e))
              (Finset.mem_filter.mp hv).2.symm
          _ = _ := collarCKWordIndex_prod v z
      exact congrArg (fun a : ℝ ↦ a • p d.degree (fun i ↦ Pi.single (v i) 1)) hmon
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun w hw ↦ Finset.mem_image_of_mem collarCKWordIndex hw) _

end Coefficients

section Packaging

variable {n m : ℕ}

/-- Package the actual analytic expansion in exactly the canonical spatial-algebra RHS carrier.
Source: Gantumur, Theorem 18. Spatial and slot multiplicities are combined by native `sumElim`.
This defines only coefficients; analytic representation is established separately below. -/
def collarCKTaylorRHS
    (p : FormalMultilinearSeries ℝ ((Fin n ⊕ CollarCKSlot n m) → ℝ) (Fin m → ℝ)) :
    CollarCKRHS n m :=
  fun j d β ↦ collarCKTaylorCoeff p (β.sumElim d) j

/-- Every nested canonical coefficient is literally the genuine finite word-fiber sum.
Source: Gantumur, Theorem 18; no rescaling or alternative formal RHS is used. -/
theorem collarCKTaylorRHS_coeff
    (p : FormalMultilinearSeries ℝ ((Fin n ⊕ CollarCKSlot n m) → ℝ) (Fin m → ℝ))
    (j : Fin m) (d : CollarCKSlot n m →₀ ℕ) (β : Fin n →₀ ℕ) :
    MvPowerSeries.coeff β (MvPowerSeries.coeff d (collarCKTaylorRHS p j)) =
      ∑ w ∈ collarCKWordFiber (β.sumElim d),
        p (β.sumElim d).degree (fun i ↦ Pi.single (w i) 1) j := by
  simp only [MvPowerSeries.coeff_apply, collarCKTaylorRHS, collarCKTaylorCoeff,
    Finset.sum_apply]

/-- Every full argument multiindex is preserved by the spatial/slot grouping.
Source: Gantumur, Theorem 18. Use the native inverse identity for the two restrictions of a
sum-indexed finitely supported function; no second coefficient carrier is introduced. -/
theorem collarCKTaylorRHS_full_coeff
    (p : FormalMultilinearSeries ℝ ((Fin n ⊕ CollarCKSlot n m) → ℝ) (Fin m → ℝ))
    (j : Fin m) (a : (Fin n ⊕ CollarCKSlot n m) →₀ ℕ) :
    MvPowerSeries.coeff (a.comapDomain Sum.inl Sum.inl_injective.injOn)
      (MvPowerSeries.coeff (a.comapDomain Sum.inr Sum.inr_injective.injOn)
        (collarCKTaylorRHS p j)) = collarCKTaylorCoeff p a j := by
  change collarCKTaylorCoeff p (Finsupp.sumElim _ _) j = _
  rw [Finsupp.comapDomain_sumElim_comapDomain]

/-- Zero at the full origin is retained by the canonical grouped coefficients.
Source: Gantumur, Theorem 18, normalized zero constant term. Only both indices zero is asserted;
the entire normal-zero spatial coefficient need not vanish for an RHS. -/
theorem collarCKTaylorRHS_origin
    (p : FormalMultilinearSeries ℝ ((Fin n ⊕ CollarCKSlot n m) → ℝ) (Fin m → ℝ))
    (hp : ∀ v, p 0 v = 0) (j : Fin m) :
    MvPowerSeries.coeff 0 (MvPowerSeries.coeff 0 (collarCKTaylorRHS p j)) = 0 := by
  change collarCKTaylorCoeff p ((0 : Fin n →₀ ℕ).sumElim 0) j = 0
  rw [Finsupp.sumElim_zero_zero, collarCKTaylorCoeff_zero p hp]
  rfl

end Packaging

section OriginalData

variable {n m : ℕ}

/-- Actual original CK data produce a genuine analytic expansion in the fixed RHS coordinates,
zero constant term, and geometric bounds for every canonical grouped RHS coefficient.
Source: Gantumur, Theorem 18 and Corollary 20.
Use the accepted actual normalization, compose with the explicit coordinate equivalence, and
apply the accepted finite-word coefficient bound to coordinate basis vectors. The expansion is
also exactly the existing W5 coordinate series. Therefore the canonical W3 coefficients are
coefficients of this actual normalized function, rather than an arbitrary formal RHS premise.
This theorem constructs no formal solution, majorant domination, or analytic PDE solution. -/
theorem collarCKOriginalData_taylor
    (G : EuclideanSpace ℝ (Fin n) × ℝ × (Fin m → ℝ) × (Fin n → Fin m → ℝ) →
      Fin m → ℝ)
    (v₀ : EuclideanSpace ℝ (Fin n) → Fin m → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hv₀ : AnalyticAt ℝ v₀ x₀)
    (hG : AnalyticAt ℝ G (x₀, 0, v₀ x₀, collarCKInitialSpatialJet v₀ x₀)) :
    ∃ p : FormalMultilinearSeries ℝ ((Fin n ⊕ CollarCKSlot n m) → ℝ) (Fin m → ℝ),
      HasFPowerSeriesAt
        (collarCKNormalizedRHS G v₀ x₀ ∘ collarCKRHSCoordinates) p 0 ∧
      HasFPowerSeriesAt
        (collarCKNormalizedRHS G v₀ x₀ ∘ collarCKRHSCoordinates)
        (collarCKCoordinateSeries (fun k w ↦ p k (fun i ↦ Pi.single (w i) 1))) 0 ∧
      (∀ v, p 0 v = 0) ∧
      ∃ M R : ℝ, 0 < M ∧ 0 < R ∧
        ∀ (j : Fin m) (d : CollarCKSlot n m →₀ ℕ) (β : Fin n →₀ ℕ),
          |MvPowerSeries.coeff β (MvPowerSeries.coeff d (collarCKTaylorRHS p j))| ≤
            M / R ^ (β.sumElim d).degree := by
  classical
  obtain ⟨hhat, hhat0⟩ := collarCKNormalizedRHS_analyticAt G v₀ x₀ hv₀ hG
  have ha : AnalyticAt ℝ
      (collarCKNormalizedRHS G v₀ x₀ ∘ collarCKRHSCoordinates) 0 := by
    exact hhat.comp_of_eq (collarCKRHSCoordinates.toContinuousLinearMap.analyticAt 0)
      (map_zero _)
  have ha0 : (collarCKNormalizedRHS G v₀ x₀ ∘ collarCKRHSCoordinates) 0 = 0 := by
    simpa only [Function.comp_apply, map_zero] using hhat0
  have he (a : Fin n ⊕ CollarCKSlot n m) :
      ‖(Pi.single a (1 : ℝ) : (Fin n ⊕ CollarCKSlot n m) → ℝ)‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    by_cases hi : i = a <;> simp [hi]
  obtain ⟨p, hp, hp0, M, R, hM, hR, hbound⟩ :=
    collarCKNormalizedAnalyticFiniteCoordinateBound _ ha ha0
      (fun a ↦ Pi.single a (1 : ℝ)) he
  refine ⟨p, hp, ?_, hp0, M, R, hM, hR, ?_⟩
  · simpa only [collarCKCoordinateSeries_basis] using hp
  · intro j d β
    have hb := hbound (β.sumElim d).degree (collarCKWordFiber (β.sumElim d))
    have hc := norm_le_pi_norm (collarCKTaylorCoeff p (β.sumElim d)) j
    change ‖collarCKTaylorCoeff p (β.sumElim d)‖ ≤ _ at hb
    have hcomponent : |collarCKTaylorCoeff p (β.sumElim d) j| ≤
        ‖collarCKTaylorCoeff p (β.sumElim d)‖ := by
      simpa only [Real.norm_eq_abs] using hc
    exact hcomponent.trans hb

end OriginalData
end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarCKRHSCoordinates
#print axioms GlobalEmbedding.Paper.collarCKCoordinateSeries_basis
#print axioms GlobalEmbedding.Paper.collarCKWordIndex
#print axioms GlobalEmbedding.Paper.collarCKWordIndex_degree
#print axioms GlobalEmbedding.Paper.collarCKWordIndex_prod
#print axioms GlobalEmbedding.Paper.collarCKWordFiber
#print axioms GlobalEmbedding.Paper.collarCKTaylorCoeff
#print axioms GlobalEmbedding.Paper.collarCKTaylorCoeff_zero
#print axioms GlobalEmbedding.Paper.collarCKTaylorCoeff_homogeneous
#print axioms GlobalEmbedding.Paper.collarCKTaylorRHS
#print axioms GlobalEmbedding.Paper.collarCKTaylorRHS_coeff
#print axioms GlobalEmbedding.Paper.collarCKTaylorRHS_full_coeff
#print axioms GlobalEmbedding.Paper.collarCKTaylorRHS_origin
#print axioms GlobalEmbedding.Paper.collarCKOriginalData_taylor
