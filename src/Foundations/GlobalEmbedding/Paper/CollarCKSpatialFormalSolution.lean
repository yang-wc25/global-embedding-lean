import GlobalEmbedding.Paper.CollarCKFormalCausalRecursion
import GlobalEmbedding.Paper.CollarCKFormalSubstitutionCausality
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.Basic.Real.Basic

/-!
# The actual spatial formal Cauchy problem

Source: Gantumur, notes2, Theorem 18, formal normal-variable recursion.
Spatial variables remain in the coefficient ring. Only the normal variable, unknowns and
their genuine coefficientwise spatial derivatives are substituted in the normal series.
This file proves formal existence and uniqueness; convergence is a separate obligation.
-/

namespace GlobalEmbedding.Paper

abbrev CollarCKSpatial (n : ℕ) := MvPowerSeries (Fin n) ℝ

abbrev CollarCKVector (n m : ℕ) := PowerSeries (Fin m → CollarCKSpatial n)

abbrev CollarCKSlot (n m : ℕ) := Unit ⊕ (Fin m ⊕ (Fin n × Fin m))

abbrev CollarCKRHS (n m : ℕ) :=
  Fin m → MvPowerSeries (CollarCKSlot n m) (CollarCKSpatial n)

abbrev CollarCKFullIndex (n : ℕ) := Unit ⊕ Fin n

variable {n m : ℕ}

/-- The actual component of a vector normal series, retaining every spatial coefficient. -/
noncomputable def collarCKComponent (u : CollarCKVector n m) (j : Fin m) :
    PowerSeries (CollarCKSpatial n) :=
  PowerSeries.mk fun k ↦ (PowerSeries.coeff k u) j

@[simp]
theorem collarCKComponent_coeff (u : CollarCKVector n m) (j : Fin m) (k : ℕ) :
    PowerSeries.coeff k (collarCKComponent u j) = (PowerSeries.coeff k u) j := by
  exact PowerSeries.coeff_mk _ _

/-- Differentiate the actual spatial coefficient series, without shifting normal degree. -/
noncomputable def collarCKSpatialDeriv (i : Fin n) (u : CollarCKVector n m) :
    CollarCKVector n m :=
  PowerSeries.mk fun k j ↦ MvPowerSeries.pderiv i ((PowerSeries.coeff k u) j)

@[simp]
theorem collarCKSpatialDeriv_coeff (i : Fin n) (u : CollarCKVector n m) (k : ℕ)
    (j : Fin m) : (PowerSeries.coeff k (collarCKSpatialDeriv i u)) j =
      MvPowerSeries.pderiv i ((PowerSeries.coeff k u) j) := by
  simp only [collarCKSpatialDeriv, PowerSeries.coeff_mk]

/-- Normal time, actual unknown components, and their actual spatial first derivatives. -/
noncomputable def collarCKSlots (u : CollarCKVector n m) :
    CollarCKSlot n m → PowerSeries (CollarCKSpatial n)
  | Sum.inl _ => PowerSeries.X
  | Sum.inr (Sum.inl j) => collarCKComponent u j
  | Sum.inr (Sum.inr (i, j)) => collarCKComponent (collarCKSpatialDeriv i u) j

/-- Assemble the actual nonlinear substitution, component by component. On zero-initial
series every slot satisfies genuine `HasSubst`, as proved below. -/
noncomputable def collarCKSubstitutedRHS (G : CollarCKRHS n m) (u : CollarCKVector n m) :
    CollarCKVector n m :=
  PowerSeries.mk fun k j ↦ PowerSeries.coeff k (MvPowerSeries.subst (collarCKSlots u) (G j))

@[simp]
theorem collarCKSubstitutedRHS_coeff (G : CollarCKRHS n m) (u : CollarCKVector n m)
    (k : ℕ) (j : Fin m) : (PowerSeries.coeff k (collarCKSubstitutedRHS G u)) j =
      PowerSeries.coeff k (MvPowerSeries.subst (collarCKSlots u) (G j)) := by
  simp only [collarCKSubstitutedRHS, PowerSeries.coeff_mk]

/-- A total extension used only to invoke the unrestricted causal recursion theorem.
The solution has zero initial coefficient, so its equation uses the genuine substitution. -/
noncomputable def collarCKFormalOperator (G : CollarCKRHS n m) (u : CollarCKVector n m) :
    CollarCKVector n m := by
  classical
  exact if PowerSeries.constantCoeff u = 0 then collarCKSubstitutedRHS G u else 0

/-- Every actual normal substitution slot has zero constant coefficient on the initial fiber.
Spatial variables themselves are never slots, and need not have zero normal constant. -/
theorem collarCKSlots_constantCoeff (u : CollarCKVector n m)
    (hu : PowerSeries.constantCoeff u = 0) (s : CollarCKSlot n m) :
    PowerSeries.constantCoeff (collarCKSlots u s) = 0 := by
  have huj (j : Fin m) : (PowerSeries.coeff 0 u) j = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hu]
    rfl
  rcases s with _ | (j | ⟨i, j⟩)
  · exact PowerSeries.constantCoeff_X
  · simpa only [collarCKSlots, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      collarCKComponent_coeff] using huj j
  · simp only [collarCKSlots, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      collarCKComponent_coeff, collarCKSpatialDeriv_coeff, huj, map_zero]

/-- The substitution is genuinely admissible, rather than the native default zero case. -/
theorem collarCKSlots_hasSubst (u : CollarCKVector n m)
    (hu : PowerSeries.constantCoeff u = 0) : MvPowerSeries.HasSubst (collarCKSlots u) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (collarCKSlots_constantCoeff u hu)

/-- Coefficientwise spatial differentiation preserves every finite normal prefix. -/
theorem collarCKSlots_prefix (p q : CollarCKVector n m) (k : ℕ)
    (hpq : ∀ l ≤ k, PowerSeries.coeff l p = PowerSeries.coeff l q)
    (s : CollarCKSlot n m) (l : ℕ) (hl : l ≤ k) :
    PowerSeries.coeff l (collarCKSlots p s) =
      PowerSeries.coeff l (collarCKSlots q s) := by
  rcases s with _ | (j | ⟨i, j⟩)
  · rfl
  · simp only [collarCKSlots, collarCKComponent_coeff, hpq l hl]
  · simp only [collarCKSlots, collarCKComponent_coeff, collarCKSpatialDeriv_coeff, hpq l hl]

/-- The genuine nonlinear spatial RHS is causal on its zero-initial fiber. -/
theorem collarCKSubstitutedRHS_causal (G : CollarCKRHS n m) (p q : CollarCKVector n m)
    (hp : PowerSeries.constantCoeff p = 0) (hq : PowerSeries.constantCoeff q = 0)
    (k : ℕ) (hpq : ∀ l ≤ k, PowerSeries.coeff l p = PowerSeries.coeff l q) :
    PowerSeries.coeff k (collarCKSubstitutedRHS G p) =
      PowerSeries.coeff k (collarCKSubstitutedRHS G q) := by
  funext j
  simp only [collarCKSubstitutedRHS_coeff]
  exact collarCKFormalSubstitutionCausality (G j) (collarCKSlots p) (collarCKSlots q)
    (collarCKSlots_constantCoeff p hp) (collarCKSlots_constantCoeff q hq) k
    (collarCKSlots_prefix p q k hpq)

/-- The actual PDE operator has the unrestricted causality required by the accepted recurrence.
Agreement through k includes degree zero, so both inputs enter the same extension branch. -/
theorem collarCKFormalOperator_causal (G : CollarCKRHS n m) (p q : CollarCKVector n m)
    (k : ℕ) (hpq : ∀ l ≤ k, PowerSeries.coeff l p = PowerSeries.coeff l q) :
    PowerSeries.coeff k (collarCKFormalOperator G p) =
      PowerSeries.coeff k (collarCKFormalOperator G q) := by
  have hzero : PowerSeries.constantCoeff p = PowerSeries.constantCoeff q := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hpq 0 (Nat.zero_le k)
  classical
  by_cases hp : PowerSeries.constantCoeff p = 0
  · have hq : PowerSeries.constantCoeff q = 0 := hzero ▸ hp
    simp only [collarCKFormalOperator, hp, hq, ite_true]
    exact collarCKSubstitutedRHS_causal G p q hp hq k hpq
  · have hq : PowerSeries.constantCoeff q ≠ 0 := fun h ↦ hp (hzero.trans h)
    simp only [collarCKFormalOperator, hp, hq, ite_false]

/-- The unique genuine spatial formal solution of the normalized first-order CK system.

Source: Gantumur, notes2, Theorem 18, formal coefficient recursion. For the given actual formal
RHS G, spatial variables stay in A and actual coefficientwise spatial derivatives enter the
substitution. Zero normal initial data makes every substituted slot admissible. Prefix
agreement is preserved by spatial differentiation and actual substitution. The total zero
extension is globally causal, so the accepted rational-algebra recurrence gives a unique
zero-initial solution. It lies on the genuine branch; the same holds for every competitor.
No convergence, analyticity, desired solution or supplied causal operator is assumed. -/
theorem collarCKSpatialFormalSolution (G : CollarCKRHS n m) :
    ∃! u : CollarCKVector n m, PowerSeries.constantCoeff u = 0 ∧
      PowerSeries.derivative u = collarCKSubstitutedRHS G u := by
  obtain ⟨u, ⟨hu0, hdu⟩, huniq⟩ :=
    collarCKFormalCausalRecursion (collarCKFormalOperator G) 0 (collarCKFormalOperator_causal G)
  have hbranch (v : CollarCKVector n m) (hv : PowerSeries.constantCoeff v = 0) :
      collarCKFormalOperator G v = collarCKSubstitutedRHS G v := by
    classical
    simp only [collarCKFormalOperator, hv, ite_true]
  refine ⟨u, ⟨hu0, (hbranch u hu0) ▸ hdu⟩, ?_⟩
  rintro v ⟨hv0, hdv⟩
  exact huniq v ⟨hv0, (hbranch v hv0).symm ▸ hdv⟩

/-- The literal scalar spatial/normal coefficient; no factorial rescaling is introduced. -/
noncomputable def collarCKCoeff (u : CollarCKVector n m) (k : ℕ)
    (β : Fin n →₀ ℕ) (j : Fin m) : ℝ :=
  MvPowerSeries.coeff β ((PowerSeries.coeff k u) j)

/-- The true normal derivative coefficient, with its usual degree factor. -/
theorem collarCKCoeff_normalDeriv (u : CollarCKVector n m) (k : ℕ)
    (β : Fin n →₀ ℕ) (j : Fin m) :
    collarCKCoeff (PowerSeries.derivative u) k β j =
      collarCKCoeff u (k + 1) β j * (k + 1 : ℝ) := by
  unfold collarCKCoeff
  rw [PowerSeries.coeff_derivative]
  simp only [Pi.mul_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
  have hcast : (k : CollarCKSpatial n) + 1 = MvPowerSeries.C ((k : ℝ) + 1) := by
    simp only [map_add, map_natCast, map_one]
  change MvPowerSeries.coeff β
    ((PowerSeries.coeff (k + 1) u) j * ((k : CollarCKSpatial n) + 1)) = _
  rw [hcast, MvPowerSeries.coeff_mul_C]

/-- The true spatial derivative coefficient, leaving normal degree unchanged. -/
theorem collarCKCoeff_spatialDeriv (u : CollarCKVector n m) (i : Fin n) (k : ℕ)
    (β : Fin n →₀ ℕ) (j : Fin m) :
    collarCKCoeff (collarCKSpatialDeriv i u) k β j =
      collarCKCoeff u k (β + Finsupp.single i 1) j * (β i + 1 : ℝ) := by
  simp only [collarCKCoeff, collarCKSpatialDeriv_coeff, MvPowerSeries.coeff_pderiv]

/-- All spatial coefficients on the initial normal hypersurface vanish. -/
theorem collarCKCoeff_initial (u : CollarCKVector n m)
    (hu : PowerSeries.constantCoeff u = 0) (β : Fin n →₀ ℕ) (j : Fin m) :
    collarCKCoeff u 0 β j = 0 := by
  simp only [collarCKCoeff, PowerSeries.coeff_zero_eq_constantCoeff_apply, hu,
    Pi.zero_apply, map_zero]

/-- The actual PDE determines the next normal coefficient, retaining every spatial index. -/
theorem collarCKCoeff_equation (G : CollarCKRHS n m) (u : CollarCKVector n m)
    (hu : PowerSeries.derivative u = collarCKSubstitutedRHS G u)
    (k : ℕ) (β : Fin n →₀ ℕ) (j : Fin m) :
    collarCKCoeff u (k + 1) β j * (k + 1 : ℝ) =
      MvPowerSeries.coeff β
        (PowerSeries.coeff k (MvPowerSeries.subst (collarCKSlots u) (G j))) := by
  rw [← collarCKCoeff_normalDeriv, hu]
  simp only [collarCKCoeff, collarCKSubstitutedRHS_coeff]

/-- A fixed choice of the actual unique formal solution, for use in coefficient estimates. -/
noncomputable def collarCKFormalSolution (G : CollarCKRHS n m) : CollarCKVector n m :=
  (collarCKSpatialFormalSolution G).exists.choose

theorem collarCKFormalSolution_spec (G : CollarCKRHS n m) :
    PowerSeries.constantCoeff (collarCKFormalSolution G) = 0 ∧
      PowerSeries.derivative (collarCKFormalSolution G) =
        collarCKSubstitutedRHS G (collarCKFormalSolution G) :=
  (collarCKSpatialFormalSolution G).exists.choose_spec

/-- Every genuine zero-initial solution is the same fixed actual solution. -/
theorem collarCKFormalSolution_unique (G : CollarCKRHS n m) (v : CollarCKVector n m)
    (hv0 : PowerSeries.constantCoeff v = 0)
    (hv : PowerSeries.derivative v = collarCKSubstitutedRHS G v) :
    v = collarCKFormalSolution G :=
  (collarCKSpatialFormalSolution G).unique ⟨hv0, hv⟩ (collarCKFormalSolution_spec G)

/-- Restrict a full time/spatial multiindex to its spatial coordinates. -/
noncomputable def collarCKSpatialIndex (d : CollarCKFullIndex n →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.comapDomain Sum.inr d Sum.inr_injective.injOn

@[simp]
theorem collarCKSpatialIndex_apply (d : CollarCKFullIndex n →₀ ℕ) (i : Fin n) :
    collarCKSpatialIndex d i = d (Sum.inr i) := rfl

/-- Combine the normal degree and actual spatial multiindex without reindexing coefficients. -/
noncomputable def collarCKMultiIndex (k : ℕ) (β : Fin n →₀ ℕ) :
    CollarCKFullIndex n →₀ ℕ :=
  Finsupp.sumElim (Finsupp.single () k) β

@[simp]
theorem collarCKMultiIndex_time (k : ℕ) (β : Fin n →₀ ℕ) :
    collarCKMultiIndex k β (Sum.inl ()) = k := by
  simp only [collarCKMultiIndex, Finsupp.sumElim_inl, Finsupp.single_eq_same]

@[simp]
theorem collarCKMultiIndex_space (k : ℕ) (β : Fin n →₀ ℕ) :
    collarCKSpatialIndex (collarCKMultiIndex k β) = β := by
  ext i
  rfl

@[simp]
theorem collarCKMultiIndex_split (d : CollarCKFullIndex n →₀ ℕ) :
    collarCKMultiIndex (d (Sum.inl ())) (collarCKSpatialIndex d) = d := by
  ext s
  rcases s with ⟨⟩ | i
  · exact collarCKMultiIndex_time _ _
  · rfl

/-- The genuine full time/spatial formal component, defined by its unchanged coefficients.
This is a rearrangement of coefficient indices, not a convergence assertion. -/
noncomputable def collarCKFlatten (u : CollarCKVector n m) (j : Fin m) :
    MvPowerSeries (CollarCKFullIndex n) ℝ :=
  fun d ↦ collarCKCoeff u (d (Sum.inl ())) (collarCKSpatialIndex d) j

theorem collarCKFlatten_coeff (u : CollarCKVector n m) (j : Fin m)
    (d : CollarCKFullIndex n →₀ ℕ) :
    MvPowerSeries.coeff d (collarCKFlatten u j) =
      collarCKCoeff u (d (Sum.inl ())) (collarCKSpatialIndex d) j := rfl

@[simp]
theorem collarCKFlatten_coeff_multiIndex (u : CollarCKVector n m) (j : Fin m)
    (k : ℕ) (β : Fin n →₀ ℕ) :
    MvPowerSeries.coeff (collarCKMultiIndex k β) (collarCKFlatten u j) =
      collarCKCoeff u k β j := by
  simp only [collarCKFlatten_coeff, collarCKMultiIndex_time, collarCKMultiIndex_space]

/-- Recover exactly the same iterated series from full-variable formal components. -/
noncomputable def collarCKUnflatten
    (v : Fin m → MvPowerSeries (CollarCKFullIndex n) ℝ) : CollarCKVector n m :=
  PowerSeries.mk (R := Fin m → CollarCKSpatial n)
    fun k j β ↦ MvPowerSeries.coeff (collarCKMultiIndex k β) (v j)

@[simp]
theorem collarCKUnflatten_coeff (v : Fin m → MvPowerSeries (CollarCKFullIndex n) ℝ)
    (k : ℕ) (β : Fin n →₀ ℕ) (j : Fin m) :
    collarCKCoeff (collarCKUnflatten v) k β j =
      MvPowerSeries.coeff (collarCKMultiIndex k β) (v j) := by
  exact congrArg (fun a : Fin m → CollarCKSpatial n ↦ MvPowerSeries.coeff β (a j))
    (PowerSeries.coeff_mk k (fun k j β ↦
      MvPowerSeries.coeff (collarCKMultiIndex k β) (v j)))

@[simp]
theorem collarCKUnflatten_flatten (u : CollarCKVector n m) :
    collarCKUnflatten (collarCKFlatten u) = u := by
  apply PowerSeries.ext
  intro k
  funext j
  apply MvPowerSeries.ext
  intro β
  exact (collarCKUnflatten_coeff (collarCKFlatten u) k β j).trans
    (collarCKFlatten_coeff_multiIndex u j k β)

@[simp]
theorem collarCKFlatten_unflatten
    (v : Fin m → MvPowerSeries (CollarCKFullIndex n) ℝ) (j : Fin m) :
    collarCKFlatten (collarCKUnflatten v) j = v j := by
  ext d
  simp only [collarCKFlatten_coeff, collarCKUnflatten_coeff, collarCKMultiIndex_split]

/-- Increasing spatial degree in the full index leaves normal degree unchanged. -/
theorem collarCKSpatialIndex_add_single (d : CollarCKFullIndex n →₀ ℕ) (i : Fin n) :
    collarCKSpatialIndex (d + Finsupp.single (Sum.inr i) 1) =
      collarCKSpatialIndex d + Finsupp.single i 1 := by
  classical
  ext l
  simp only [collarCKSpatialIndex_apply, Finsupp.add_apply, Finsupp.single_apply,
    Sum.inr.injEq]

/-- Increasing normal degree leaves every spatial degree unchanged. -/
theorem collarCKSpatialIndex_add_time (d : CollarCKFullIndex n →₀ ℕ) :
    collarCKSpatialIndex (d + Finsupp.single (Sum.inl ()) 1) =
      collarCKSpatialIndex d := by
  ext i
  simp only [collarCKSpatialIndex_apply, Finsupp.add_apply, Finsupp.single_eq_of_ne
    (by simp : Sum.inr i ≠ (Sum.inl () : CollarCKFullIndex n)), add_zero]

/-- Rearrangement preserves actual normal differentiation in the full formal ring. -/
theorem collarCKFlatten_normalDeriv (u : CollarCKVector n m) (j : Fin m) :
    collarCKFlatten (PowerSeries.derivative u) j =
      MvPowerSeries.pderiv (Sum.inl ()) (collarCKFlatten u j) := by
  ext d
  simp only [collarCKFlatten_coeff, collarCKCoeff_normalDeriv, MvPowerSeries.coeff_pderiv,
    collarCKSpatialIndex_add_time, Finsupp.add_apply, Finsupp.single_eq_same]

/-- Rearrangement preserves actual spatial differentiation in the full formal ring. -/
theorem collarCKFlatten_spatialDeriv (u : CollarCKVector n m) (j : Fin m) (i : Fin n) :
    collarCKFlatten (collarCKSpatialDeriv i u) j =
      MvPowerSeries.pderiv (Sum.inr i) (collarCKFlatten u j) := by
  ext d
  simp only [collarCKFlatten_coeff, collarCKCoeff_spatialDeriv, MvPowerSeries.coeff_pderiv,
    collarCKSpatialIndex_add_single, collarCKSpatialIndex_apply, Finsupp.add_apply,
    Finsupp.single_eq_of_ne (by simp : Sum.inl () ≠ (Sum.inr i : CollarCKFullIndex n)),
    add_zero]

end GlobalEmbedding.Paper
