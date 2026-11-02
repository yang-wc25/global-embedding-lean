import Probes.ActualOriginalIncrementRawNormsAllIndex
import GlobalEmbedding.Offline.OneStepScaleBounds

/-!
The literal finite sine/cosine displacement supplies the growing-order norm
used by the infinite repair series. The norm bound is obtained by calling the
actual original finite solver; it is not an assumption on a proposed U.
All observations use the same U, and the original atlas maximum is retained.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff Classical ENNReal BigOperators
namespace GlobalEmbedding.Continuation

private theorem round3_original_cj_of_weighted
    {ι : Type*} [Fintype ι] {a b : ℕ} (r j : ℕ) (hrj : r ≤ j)
    (tau K : ℝ) (htau : 0 < tau) (hK : 0 ≤ K)
    (f : ι → (Fin a → ℝ) → Fin b → ℝ) (O S : ι → Set (Fin a → ℝ))
    (hfinite : paperAtlasWeighted 0 j tau f O S ≠ ⊤)
    (hbound : (paperAtlasWeighted 0 j tau f O S).toReal ≤ K) :
    paperAtlasCj r f O S ≤ ENNReal.ofReal (K / tau^r) := by
  have hterm : ENNReal.ofReal tau ^ r * paperAtlasCj r f O S ≤
      paperAtlasWeighted 0 j tau f O S := by
    simpa only [paperAtlasWeighted, Nat.add_zero] using
      (Finset.single_le_sum (fun i hi => (show (0 : ℝ≥0∞) ≤
        ENNReal.ofReal tau ^ i * paperAtlasCj (i+0) f O S from bot_le))
        (show r ∈ Finset.range (j+1) by simp; omega))
  have htermfinite := ne_top_of_le_ne_top hfinite hterm
  have hweight : ENNReal.ofReal tau ^ r ≠ 0 :=
    ENNReal.pow_ne_zero (ENNReal.ofReal_ne_zero_iff.2 htau) r
  have hnorm : paperAtlasCj r f O S ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top hweight] at htermfinite
    exact htermfinite rfl
  have hreal := (ENNReal.toReal_mono hfinite hterm).trans hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal htau.le] at hreal
  rw [← ENNReal.ofReal_toReal hnorm]
  apply ENNReal.ofReal_le_ofReal
  exact (le_div_iff₀ (pow_pos htau r)).2 (by simpa only [mul_comm] using hreal)

private theorem round3_repair_displacement_power_identity
    {t : ℝ} (ht : 0 < t) (k r : ℕ) (C : ℝ) :
    C*t^k*t^(6/5 : ℝ)/(t^(6/5 : ℝ))^r =
      C*t^((k : ℝ)+(6/5 : ℝ)*(1-(r : ℝ))) := by
  have hpow : (t^(6/5 : ℝ))^r = t^((6/5 : ℝ)*(r : ℝ)) := by
    rw [Real.rpow_mul ht.le, Real.rpow_natCast]
  calc
    _ = C*(t^(k : ℝ)*t^(6/5 : ℝ)/t^((6/5 : ℝ)*(r : ℝ))) := by
      rw [Real.rpow_natCast, hpow]
      ring
    _ = C*t^((k : ℝ)+(6/5 : ℝ)-(6/5 : ℝ)*(r : ℝ)) := by
      rw [← Real.rpow_add ht, ← Real.rpow_sub ht]
    _ = _ := by congr 2; ring

private theorem round3_repair_power_budget
    {t C rho : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hC : 0 ≤ C)
    (k : ℕ) (hk : 10 ≤ k) (hsmall : t ≤ rho/(8*(C+1))) :
    C*t^((k : ℝ)+(6/5 : ℝ)*(1-((k/2 : ℕ) : ℝ))) ≤ (rho/8)*t := by
  have hk' : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hhalf : 2*((k/2 : ℕ) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (show 2*(k/2) ≤ k by omega)
  have hexponent : (2 : ℝ) ≤ (k : ℝ)+(6/5 : ℝ)*(1-((k/2 : ℕ) : ℝ)) := by
    linarith
  have hs := (le_div_iff₀ (by positivity : 0 < 8*(C+1))).1 hsmall
  have hCt : C*t ≤ rho/8 := by nlinarith
  calc
    _ ≤ C*t^(2 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge ht ht1 hexponent) hC
    _ = (C*t)*t := by rw [Real.rpow_two]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hCt ht.le

/-- Extract the exact growing-order original MAX from the literal weighted
increment estimate. This is used on the same U as the pair recurrence. -/
theorem round3_repair_growing_order_budget_of_weighted
    {ι : Type*} [Fintype ι] {a b : ℕ} (k j : ℕ) (hk : 10 ≤ k) (hkj : k/2 ≤ j)
    (t C : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hC : 0 ≤ C)
    (f : ι → (Fin a → ℝ) → Fin b → ℝ) (O S : ι → Set (Fin a → ℝ))
    (hfinite : paperAtlasWeighted 0 j (t^(6/5 : ℝ)) f O S ≠ ⊤)
    (hbound : (paperAtlasWeighted 0 j (t^(6/5 : ℝ)) f O S).toReal ≤
      C*t^k*t^(6/5 : ℝ)) :
    paperAtlasCj (k/2) f O S ≤
      ENNReal.ofReal (C*t^((k : ℝ)+(6/5 : ℝ)*(1-((k/2 : ℕ) : ℝ)))) ∧
    ∀ rho : ℝ, t ≤ rho/(8*(C+1)) →
      paperAtlasCj (k/2) f O S ≤ ENNReal.ofReal ((rho/8)*t) := by
  have htau := Real.rpow_pos_of_pos ht (6/5 : ℝ)
  have h := round3_original_cj_of_weighted (k/2) j hkj
    (t^(6/5 : ℝ)) (C*t^k*t^(6/5 : ℝ)) htau (by positivity) f O S hfinite hbound
  rw [round3_repair_displacement_power_identity ht] at h
  exact ⟨h,fun rho hsmall => h.trans (ENNReal.ofReal_le_ofReal
    (round3_repair_power_budget ht ht1 hC k hk hsmall))⟩

variable {m d N : ℕ} {M Tr : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

/-- The original finite solver, at the actual paper scales, supplies the
growing-order displacement budget needed by the full repair series. The
constant precedes all actual atlases, geometry, functions and scales. -/
theorem round3_actual_original_increment_growing_order_budget
    (k nInput nSolve Rsub Lprimary Rsecondary : ℕ) (hk : 10 ≤ k)
    (hSolve : k/2+2+(40*(k+1)+2) ≤ nSolve)
    (hInput : nSolve+2+(40*(k+1)+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd)
    (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs TP : ℕ → ℝ)
    (hT : ∀ j, 0 ≤ T j) (hTinv : ∀ j, 0 ≤ Tinv j)
    (hTobs : ∀ j, 0 ≤ Tobs j) (hTP : ∀ j, 0 ≤ TP j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Label SubPrimary SubSecondary : Type*)
      [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary], ∀
      (pcount : ℕ) (A : BufferedAtlas M D) (B : Fin pcount → OpenPartialHomeomorph Ep Ep)
      (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
      (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
      (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
        (Λ := Label) (Β := SubPrimary) F)
      (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (W : Set (Ep × M)) (primary : Label → Set (Ep × M))
      (S : Fin A.count × Fin pcount → Set (Fin (m+1+d) → ℝ))
      (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
      (t Delta : ℝ) (ht : 0 < t) (ht1 : t ≤ 1),
    let ell := t^(11/10 : ℝ)
    let delta := t^k
    let tau := t^(6/5 : ℝ)
    ∀ (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m)
      (raw : ActualOriginalSecondaryRawData (Tr := Tr) F hF g input inputbar
        nInput nSolve (k/2) (40*(k+1)) Rsub Lprimary reserve Bnd Mg Kcut T Tinv
        W primary ell delta tau Delta choice)
      (Omega : Fin A.count × Fin pcount → Set X)
      (obs : ∀ i : Fin A.count × Fin pcount,
        ActualOriginalSecondaryObservationData raw Tobs Rsecondary (A.chart i.1) (Omega i)
          (parameterRound2_meanParameterMap (m := m) (B i.2) ''
            ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)))
      (hParam : ∀ i : Fin A.count × Fin pcount, ∀ z : X,
        parameterTensorModelEquiv (m+1) d z ∈ S i → ∀ j, 1 ≤ j → j ≤ k/2+1 →
          ell^(j-1)*‖iteratedFDeriv ℝ j (parameterRound2_meanParameterMap (m := m) (B i.2)) z‖ ≤ TP j),
    let U := actualOriginalIncrementMap F hF g input (40*(k+1)+2) tau delta choice
    let coordinates := incrementsOriginalMapCoordinates A B U
    paperAtlasCj (k/2) coordinates (incrementsOriginalDifferentiation A B) S ≤
      ENNReal.ofReal (C*t^((k : ℝ)+(6/5 : ℝ)*(1-((k/2 : ℕ) : ℝ)))) ∧
    ∀ rho : ℝ, t ≤ rho/(8*(C+1)) →
      paperAtlasCj (k/2) coordinates (incrementsOriginalDifferentiation A B) S ≤
        ENNReal.ofReal ((rho/8)*t) := by
  obtain ⟨C,hC,hraw⟩ := actual_original_increment_raw_paper_norms_uniform_all_index
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    nInput nSolve (k/2) (40*(k+1)) Rsub Lprimary Rsecondary (by omega)
    hSolve hInput reserve Bnd Mg Kcut hc hBnd hMg hKcut T Tinv Tobs TP hT hTinv hTobs hTP
  refine ⟨C,hC,?_⟩
  intro Label SubPrimary SubSecondary _ _ _ _ pcount A B hA hB F hF g input inputbar
    W primary S hSO t Delta ht ht1 ell delta tau choice raw Omega obs hParam U coordinates
  have htau : 0 < tau := Real.rpow_pos_of_pos ht _
  have hscales := repair_step_scale_order ht ht1 k hk
  have hdelta : 0 ≤ delta := pow_nonneg ht.le k
  have h := hraw Label SubPrimary SubSecondary pcount A B hA hB F hF g input inputbar
    W primary S hSO ell delta tau Delta htau hscales.2.2.1 (hscales.2.2.2.trans ht1)
    hdelta hscales.2.1 choice raw Omega obs hParam
  have hbound := round3_original_cj_of_weighted (k/2) (k/2+1) (by omega)
    tau (C*delta*tau) htau (by positivity) coordinates
    (incrementsOriginalDifferentiation A B) S h.2.1.1 h.2.1.2
  change paperAtlasCj (k/2) coordinates (incrementsOriginalDifferentiation A B) S ≤
    ENNReal.ofReal (C*t^k*t^(6/5 : ℝ)/(t^(6/5 : ℝ))^(k/2)) at hbound
  rw [round3_repair_displacement_power_identity ht] at hbound
  refine ⟨hbound,?_⟩
  intro rho hsmall
  exact hbound.trans (ENNReal.ofReal_le_ofReal
    (round3_repair_power_budget ht ht1 hC k hk hsmall))

#print axioms round3_actual_original_increment_growing_order_budget

end GlobalEmbedding.Continuation
