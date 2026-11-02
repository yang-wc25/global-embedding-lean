import GlobalEmbedding.Offline.PairedValueCoincidenceRank

/-!
# Native derivatives of one global paired leading wave and one global remainder

Source: the actual leading value term of (8.3), its responses (8.1), and the
final value-coincidence step in `thm:upgrade`. The fixed negative weights and
cutoffs are included in the ambient leading vector fields below.

The maps are actual global functions. Only their leading vector fields vanish
at the second source point; the SAME global remainder is differentiated and
estimated at both endpoints. The geometric finite solver and exact-metric
repair construction remain upstream providers of the displayed decomposition
and remainder bounds.
-/

noncomputable section

open Function Filter Manifold Bundle Set GlobalEmbedding.Paper
open scoped Topology ContDiff

namespace GlobalEmbedding.Offline

section PrincipalMap

variable {p r : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The literal finite leading value wave, linear in the actual `Fin p`
parameter coordinates. The embedding records distinct real parameter labels,
so this is compatible with any larger finite probe family. -/
def pairedValuePrincipalMap (label : (Fin r × Bool) ↪ Fin p)
    (theta : Fin r → ℝ) (a : ℝ) (v : Fin r → V) : (Fin p → ℝ) →L[ℝ] V :=
  ∑ i, ((ContinuousLinearMap.proj (label (i, false))).smulRight
      ((a * Real.cos (theta i)) • v i) +
    (ContinuousLinearMap.proj (label (i, true))).smulRight
      ((a * Real.sin (theta i)) • v i))

/-- Evaluating the actual leading map on its cosine coordinate gives precisely
the source's cosine value column. Distinct labels remove every other wave. -/
theorem pairedValuePrincipalMap_cos_column
    (label : (Fin r × Bool) ↪ Fin p) (theta : Fin r → ℝ) (a : ℝ)
    (v : Fin r → V) (i : Fin r) :
    pairedValuePrincipalMap label theta a v (Pi.single (label (i, false)) 1) =
      (a * Real.cos (theta i)) • v i := by
  classical
  simp [pairedValuePrincipalMap, Pi.single_apply, label.injective.eq_iff]

/-- Evaluating the actual leading map on its sine coordinate gives precisely
the source's sine value column, in the same parameter family. -/
theorem pairedValuePrincipalMap_sin_column
    (label : (Fin r × Bool) ↪ Fin p) (theta : Fin r → ℝ) (a : ℝ)
    (v : Fin r → V) (i : Fin r) :
    pairedValuePrincipalMap label theta a v (Pi.single (label (i, true)) 1) =
      (a * Real.sin (theta i)) • v i := by
  classical
  simp [pairedValuePrincipalMap, Pi.single_apply, label.injective.eq_iff]

/-- Native differentiation of the ACTUAL same global family decomposed into
a parameter-independent base, the literal paired leading map, and one global
remainder. No derivative identification is a hypothesis. -/
theorem hasFDerivAt_paired_value_global_decomposition
    {M : Type*} (G : (Fin p → ℝ) → M → V) (F0 : M → V)
    (R : (Fin p → ℝ) → M → V)
    (label : (Fin r × Bool) ↪ Fin p) (theta : Fin r → M → ℝ) (a : ℝ)
    (v : Fin r → M → V)
    (hsplit : ∀ w z, G w z = F0 z +
      pairedValuePrincipalMap label (fun i ↦ theta i z) a (fun i ↦ v i z) w + R w z)
    (u : Fin p → ℝ) (x : M) (hR : DifferentiableAt ℝ (fun w ↦ R w x) u) :
    HasFDerivAt (fun w ↦ G w x)
      (pairedValuePrincipalMap label (fun i ↦ theta i x) a (fun i ↦ v i x) +
        fderiv ℝ (fun w ↦ R w x) u) u := by
  have hfun : (fun w ↦ G w x) = (fun w ↦ F0 x +
      pairedValuePrincipalMap label (fun i ↦ theta i x) a (fun i ↦ v i x) w) +
        (fun w ↦ R w x) :=
    funext (fun w ↦ hsplit w x)
  rw [hfun]
  exact ((pairedValuePrincipalMap label (fun i ↦ theta i x) a
    (fun i ↦ v i x)).hasFDerivAt.const_add (F0 x)).add hR.hasFDerivAt

/-- The actual native parameter derivative of the same global decomposition. -/
theorem fderiv_paired_value_global_decomposition
    {M : Type*} (G : (Fin p → ℝ) → M → V) (F0 : M → V)
    (R : (Fin p → ℝ) → M → V)
    (label : (Fin r × Bool) ↪ Fin p) (theta : Fin r → M → ℝ) (a : ℝ)
    (v : Fin r → M → V)
    (hsplit : ∀ w z, G w z = F0 z +
      pairedValuePrincipalMap label (fun i ↦ theta i z) a (fun i ↦ v i z) w + R w z)
    (u : Fin p → ℝ) (x : M) (hR : DifferentiableAt ℝ (fun w ↦ R w x) u) :
    fderiv ℝ (fun w ↦ G w x) u =
      pairedValuePrincipalMap label (fun i ↦ theta i x) a (fun i ↦ v i x) +
        fderiv ℝ (fun w ↦ R w x) u :=
  (hasFDerivAt_paired_value_global_decomposition G F0 R label theta a v hsplit u x hR).fderiv

/-- The actual global cosine and sine responses follow by native
differentiation of the single global decomposition, including the actual
derivative of its remainder at the displayed source point. -/
theorem fderiv_paired_value_global_columns
    {M : Type*} (G : (Fin p → ℝ) → M → V) (F0 : M → V)
    (R : (Fin p → ℝ) → M → V)
    (label : (Fin r × Bool) ↪ Fin p) (theta : Fin r → M → ℝ) (a : ℝ)
    (v : Fin r → M → V)
    (hsplit : ∀ w z, G w z = F0 z +
      pairedValuePrincipalMap label (fun i ↦ theta i z) a (fun i ↦ v i z) w + R w z)
    (u : Fin p → ℝ) (x : M) (hR : DifferentiableAt ℝ (fun w ↦ R w x) u)
    (i : Fin r) :
    (fderiv ℝ (fun w ↦ G w x) u (Pi.single (label (i, false)) 1) =
      (a * Real.cos (theta i x)) • v i x +
        fderiv ℝ (fun w ↦ R w x) u (Pi.single (label (i, false)) 1)) ∧
    (fderiv ℝ (fun w ↦ G w x) u (Pi.single (label (i, true)) 1) =
      (a * Real.sin (theta i x)) • v i x +
        fderiv ℝ (fun w ↦ R w x) u (Pi.single (label (i, true)) 1)) := by
  rw [fderiv_paired_value_global_decomposition G F0 R label theta a v hsplit u x hR]
  constructor
  · rw [add_apply, pairedValuePrincipalMap_cos_column]
  · rw [add_apply, pairedValuePrincipalMap_sin_column]

end PrincipalMap

section ActualNormalRank

variable {p q r N : ℕ} {E M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- Selected independent columns of ONE complete global wave packet give the
true normal parameter rank. Derivative identities are proved, and both points'
derivatives of the SAME global remainder are retained. Only the SELECTED
leading fields vanish at the second point; unselected global waves remain in
the actual family and need not vanish there. -/
theorem coincidence_normal_rank_of_global_paired_decomposition
    (G : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N))
    (F0 : M → EuclideanSpace ℝ (Fin N))
    (R : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N))
    (label : (Fin r × Bool) ↪ Fin p) (select : Fin q ↪ Fin r) (theta : Fin r → M → ℝ)
    (v : Fin r → M → EuclideanSpace ℝ (Fin N))
    {a m eta eps : ℝ} (ha : 0 < a) (heta : 0 ≤ eta) (heps : 0 ≤ eps)
    (hsplit : ∀ w z, G w z = F0 z +
      pairedValuePrincipalMap label (fun i ↦ theta i z) a (fun i ↦ v i z) w + R w z)
    (u : Fin p → ℝ) (x y : M)
    (hx : DifferentiableAt ℝ (fun w ↦ R w x) u)
    (hy : DifferentiableAt ℝ (fun w ↦ R w y) u)
    (hframe : ∀ c : Fin q → ℝ, m * ‖c‖ ≤ ‖∑ i, c i • v (select i) x‖)
    (hyzero : ∀ i, v (select i) y = 0)
    (hproj : ∀ i, ‖(normalSpace (I := 𝓘(ℝ, E)) (G u) x).starProjection (v (select i) x) - v (select i) x‖ ≤ eta)
    (hRx : ∀ i b, ‖fderiv ℝ (fun w ↦ R w x) u (Pi.single (label (select i, b)) 1)‖ ≤ a * eps)
    (hRy : ∀ i b, ‖fderiv ℝ (fun w ↦ R w y) u (Pi.single (label (select i, b)) 1)‖ ≤ a * eps)
    (hsmall : (q : ℝ) * (eta + 4 * eps) < m) :
    q ≤ Module.finrank ℝ (LinearMap.range
      (coincidenceParameterNormalDerivative (E := E) G u x y).toLinearMap) := by
  have hGx := (hasFDerivAt_paired_value_global_decomposition
    G F0 R label theta a v hsplit u x hx).differentiableAt
  have hGy := (hasFDerivAt_paired_value_global_decomposition
    G F0 R label theta a v hsplit u y hy).differentiableAt
  apply coincidence_parameter_normal_rank_of_paired_responses G u x y ha heta heps
    (fun i ↦ theta (select i) x) (fun i ↦ Pi.single (label (select i, false)) 1)
    (fun i ↦ Pi.single (label (select i, true)) 1) (fun i ↦ v (select i) x)
    (fun i ↦ fderiv ℝ (fun w ↦ R w x) u (Pi.single (label (select i, false)) 1))
    (fun i ↦ fderiv ℝ (fun w ↦ R w y) u (Pi.single (label (select i, false)) 1))
    (fun i ↦ fderiv ℝ (fun w ↦ R w x) u (Pi.single (label (select i, true)) 1))
    (fun i ↦ fderiv ℝ (fun w ↦ R w y) u (Pi.single (label (select i, true)) 1))
    hGx hGy hframe
  · intro i
    exact (fderiv_paired_value_global_columns G F0 R label theta a v hsplit u x hx (select i)).1
  · intro i
    simpa only [hyzero, smul_zero, zero_add] using
      (fderiv_paired_value_global_columns G F0 R label theta a v hsplit u y hy (select i)).1
  · intro i
    exact (fderiv_paired_value_global_columns G F0 R label theta a v hsplit u x hx (select i)).2
  · intro i
    simpa only [hyzero, smul_zero, zero_add] using
      (fderiv_paired_value_global_columns G F0 R label theta a v hsplit u y hy (select i)).2
  · exact hproj
  · exact fun i ↦ hRx i false
  · exact fun i ↦ hRy i false
  · exact fun i ↦ hRx i true
  · exact fun i ↦ hRy i true
  · exact hsmall

/-- One fixed reference-normal independent frame supplies positive C¹ and
normalized global-remainder tolerances BEFORE all parameter dimensions, actual
families, labels, arbitrary phase functions, and amplitudes. The actual global
decomposition then forces the normal parameter rank; it does not assume the
response formulas, current-normal bounds, or desired rank.

All four remainder columns are literal derivatives of the SAME global `R`.
Only the leading fields vanish at `y`. The geometric probe-family construction
and its uniform bounds are the remaining upstream obligations. -/
theorem exists_global_paired_rank_tolerances_of_reference_frame
    [FiniteDimensional ℝ E]
    [RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    (F : M → EuclideanSpace ℝ (Fin N)) (x : M) {lam : ℝ} (hlam : 0 < lam)
    (hF : ∀ w : TangentSpace 𝓘(ℝ, E) x,
      lam * ‖w‖ ^ 2 ≤ ‖mvfderiv 𝓘(ℝ, E) F x w‖ ^ 2)
    (v : Fin r → M → EuclideanSpace ℝ (Fin N)) (select : Fin q ↪ Fin r)
    (hv : LinearIndependent ℝ (fun i ↦ v (select i) x))
    (hnormal : ∀ i, v (select i) x ∈ normalSpace (I := 𝓘(ℝ, E)) F x) :
    ∃ eps delta : ℝ, 0 < eps ∧ 0 < delta ∧
      ∀ (p : ℕ) (G : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N))
        (F0 : M → EuclideanSpace ℝ (Fin N))
        (R : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N))
        (label : (Fin r × Bool) ↪ Fin p) (theta : Fin r → M → ℝ)
        (a : ℝ), 0 < a →
        (∀ w z, G w z = F0 z +
          pairedValuePrincipalMap label (fun i ↦ theta i z) a (fun i ↦ v i z) w + R w z) →
        ∀ (u : Fin p → ℝ) (y : M),
          DifferentiableAt ℝ (fun w ↦ R w x) u →
          DifferentiableAt ℝ (fun w ↦ R w y) u →
          ‖mvfderiv 𝓘(ℝ, E) F x - mvfderiv 𝓘(ℝ, E) (G u) x‖ ≤ delta →
          (∀ i, v (select i) y = 0) →
          (∀ i b, ‖fderiv ℝ (fun w ↦ R w x) u (Pi.single (label (select i, b)) 1)‖ ≤ a * eps) →
          (∀ i b, ‖fderiv ℝ (fun w ↦ R w y) u (Pi.single (label (select i, b)) 1)‖ ≤ a * eps) →
          q ≤ Module.finrank ℝ (LinearMap.range
            (coincidenceParameterNormalDerivative (E := E) G u x y).toLinearMap) := by
  obtain ⟨eps, delta, heps, hdelta, hrank⟩ :=
    exists_paired_value_rank_tolerances_of_reference_frame F x hlam hF
      (fun i ↦ v (select i) x) hv hnormal
  refine ⟨eps, delta, heps, hdelta, ?_⟩
  intro p G F0 R label theta a ha hsplit u y hx hy hclose hyzero hRx hRy
  have hGx := (hasFDerivAt_paired_value_global_decomposition
    G F0 R label theta a v hsplit u x hx).differentiableAt
  have hGy := (hasFDerivAt_paired_value_global_decomposition
    G F0 R label theta a v hsplit u y hy).differentiableAt
  apply hrank p G u y a ha (fun i ↦ theta (select i) x)
    (fun i ↦ Pi.single (label (select i, false)) 1) (fun i ↦ Pi.single (label (select i, true)) 1)
    (fun i ↦ fderiv ℝ (fun w ↦ R w x) u (Pi.single (label (select i, false)) 1))
    (fun i ↦ fderiv ℝ (fun w ↦ R w y) u (Pi.single (label (select i, false)) 1))
    (fun i ↦ fderiv ℝ (fun w ↦ R w x) u (Pi.single (label (select i, true)) 1))
    (fun i ↦ fderiv ℝ (fun w ↦ R w y) u (Pi.single (label (select i, true)) 1))
    hGx hGy hclose
  · intro i
    exact (fderiv_paired_value_global_columns G F0 R label theta a v hsplit u x hx (select i)).1
  · intro i
    simpa only [hyzero, smul_zero, zero_add] using
      (fderiv_paired_value_global_columns G F0 R label theta a v hsplit u y hy (select i)).1
  · intro i
    exact (fderiv_paired_value_global_columns G F0 R label theta a v hsplit u x hx (select i)).2
  · intro i
    simpa only [hyzero, smul_zero, zero_add] using
      (fderiv_paired_value_global_columns G F0 R label theta a v hsplit u y hy (select i)).2
  · exact fun i ↦ hRx i false
  · exact fun i ↦ hRy i false
  · exact fun i ↦ hRx i true
  · exact fun i ↦ hRy i true

end ActualNormalRank

section FixedParameterBall

variable {p q r N : ℕ} {E M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]

/-- The source's order of choices is genuine: first fix one positive parameter
radius, THEN take sufficiently small positive scales. The actual global
remainder estimate `a(t)*(eta(t)+C*‖u‖)` and native C¹ convergence yield the
same true parameter-normal rank uniformly on that fixed parameter ball and
all displayed second points. No smoothness or continuity in the scale `t` is
assumed beyond the two stated scalar error limits.

The same full packet, labels, global map `G t`, and global remainder `R t` are
used throughout. The selected leading vectors vanish at `y`; the actual global
remainder derivative at `y` is explicitly bounded and retained. -/
theorem exists_fixed_parameter_ball_eventually_actual_normal_rank
    (F : M → EuclideanSpace ℝ (Fin N)) (x : M) {lam : ℝ} (hlam : 0 < lam)
    (hF : ∀ w : TangentSpace 𝓘(ℝ, E) x,
      lam * ‖w‖ ^ 2 ≤ ‖mvfderiv 𝓘(ℝ, E) F x w‖ ^ 2)
    (v : Fin r → M → EuclideanSpace ℝ (Fin N)) (select : Fin q ↪ Fin r)
    (hv : LinearIndependent ℝ (fun i ↦ v (select i) x))
    (hnormal : ∀ i, v (select i) x ∈ normalSpace (I := 𝓘(ℝ, E)) F x)
    (Y : Set M) (hY : ∀ y ∈ Y, ∀ i, v (select i) y = 0)
    (label : (Fin r × Bool) ↪ Fin p)
    (G : ℝ → (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N))
    (F0 : ℝ → M → EuclideanSpace ℝ (Fin N))
    (R : ℝ → (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N))
    (theta : ℝ → Fin r → M → ℝ) (a eta d : ℝ → ℝ)
    (C rho0 : ℝ) (hC : 0 ≤ C) (hrho0 : 0 < rho0)
    (heta : Tendsto eta (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hd : Tendsto d (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hsplit : ∀ t w z, G t w z = F0 t z +
      pairedValuePrincipalMap label (fun i ↦ theta t i z) (a t) (fun i ↦ v i z) w + R t w z)
    (hprovider : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < a t ∧
      ∀ u : Fin p → ℝ, ‖u‖ < rho0 →
        (∀ z ∈ insert x Y, DifferentiableAt ℝ (fun w ↦ R t w z) u) ∧
        ‖mvfderiv 𝓘(ℝ, E) F x - mvfderiv 𝓘(ℝ, E) (G t u) x‖ ≤ d t ∧
        ∀ z ∈ insert x Y, ∀ i b,
          ‖fderiv ℝ (fun w ↦ R t w z) u (Pi.single (label (select i, b)) 1)‖ ≤
            a t * (eta t + C * ‖u‖)) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ rho0 ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ u : Fin p → ℝ, ‖u‖ < rho →
        ∀ y ∈ Y, q ≤ Module.finrank ℝ (LinearMap.range
          (coincidenceParameterNormalDerivative (E := E) (G t) u x y).toLinearMap) := by
  obtain ⟨eps, delta, heps, hdelta, hrank⟩ :=
    exists_global_paired_rank_tolerances_of_reference_frame F x hlam hF v select hv hnormal
  let rho := min rho0 (eps / (2 * (C + 1)))
  have hrho : 0 < rho := lt_min hrho0 (div_pos heps (by positivity))
  have hrho_le : rho ≤ rho0 := min_le_left _ _
  have hCrho : C * rho ≤ eps / 2 := by
    have h := (le_div_iff₀ (show 0 < 2 * (C + 1) by positivity)).mp
      (min_le_right rho0 (eps / (2 * (C + 1))))
    nlinarith
  refine ⟨rho, hrho, hrho_le, ?_⟩
  filter_upwards [hprovider, heta.eventually_lt_const (by positivity : 0 < eps / 2),
    hd.eventually_lt_const hdelta] with t hprov heta_t hd_t
  intro u hu y hy
  obtain ⟨ha, hlocal⟩ := hprov
  obtain ⟨hRdiff, hclose, hRbound⟩ := hlocal u (hu.trans_le hrho_le)
  have hnorm : eta t + C * ‖u‖ ≤ eps := by
    have hCu := mul_le_mul_of_nonneg_left hu.le hC
    linarith
  apply hrank p (G t) (F0 t) (R t) label (theta t) (a t) ha (hsplit t) u y
    (hRdiff x (Set.mem_insert x Y)) (hRdiff y (Set.mem_insert_of_mem x hy))
    (hclose.trans hd_t.le) (hY y hy)
  · intro i b
    exact (hRbound x (Set.mem_insert x Y) i b).trans
      (mul_le_mul_of_nonneg_left hnorm ha.le)
  · intro i b
    exact (hRbound y (Set.mem_insert_of_mem x hy) i b).trans
      (mul_le_mul_of_nonneg_left hnorm ha.le)

end FixedParameterBall

#print axioms pairedValuePrincipalMap_cos_column
#print axioms pairedValuePrincipalMap_sin_column
#print axioms hasFDerivAt_paired_value_global_decomposition
#print axioms fderiv_paired_value_global_decomposition
#print axioms fderiv_paired_value_global_columns
#print axioms coincidence_normal_rank_of_global_paired_decomposition
#print axioms exists_global_paired_rank_tolerances_of_reference_frame
#print axioms exists_fixed_parameter_ball_eventually_actual_normal_rank

end GlobalEmbedding.Offline
