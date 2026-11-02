import Probes.Round4ParameterProbeForcedReserve
import Probes.Round4ParameterProbeMeanResidual
import Smoothing.ParameterRound2TensorGermSpace

/-! The forced finite reserve is consumed by the actual original global
background mean, driven by the complete prescribed probe. Its genuine germ
space keeps the original atlas and seminorms. The numerical threshold is
fixed before the probe parameter. The original raw size and difference
estimates are still explicit inputs; no iterate reserve or final residual
bound is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N p r count : ℕ} {M Λ Β : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

/-- Outside the original reserve only the auxiliary germ-valued operator is
totalized. Every produced finite iterate lies inside the reserve, where the
value is the literal original global primary mean error. -/
def round4ParameterProbeActualGermError
    (atlas : BufferedAtlas M D) (param : Fin count → OpenPartialHomeomorph Ep Ep)
    (S : Fin atlas.count × Fin count → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (seminorm : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace atlas param S W))
    (H : parameterRound2_originalTensorGermSpace atlas param S W) (rho : ℝ)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I:=𝓙) (m:=m) (N:=N) (Λ:=Λ) (Β:=Β) F)
    (length : ℕ) (tau : ℝ)
    (hsm : ∀ K : parameterRound2_originalTensorGermSpace atlas param S W,
      seminorm 0 (K-H) < rho → incrementsGlobalPrimaryMeanError F hF g K.val length tau ∈
        parameterRound2_originalTensorGermSpace atlas param S W)
    (K : parameterRound2_originalTensorGermSpace atlas param S W) :
    parameterRound2_originalTensorGermSpace atlas param S W :=
  if hK : seminorm 0 (K-H) < rho then
    ⟨incrementsGlobalPrimaryMeanError F hF g K.val length tau,hsm K hK⟩ else 0

theorem round4ParameterProbeActualGermError_val
    (atlas : BufferedAtlas M D) (param : Fin count → OpenPartialHomeomorph Ep Ep)
    (S : Fin atlas.count × Fin count → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (seminorm : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace atlas param S W))
    (H : parameterRound2_originalTensorGermSpace atlas param S W) (rho : ℝ)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I:=𝓙) (m:=m) (N:=N) (Λ:=Λ) (Β:=Β) F)
    (length : ℕ) (tau : ℝ)
    (hsm : ∀ K : parameterRound2_originalTensorGermSpace atlas param S W,
      seminorm 0 (K-H) < rho → incrementsGlobalPrimaryMeanError F hF g K.val length tau ∈
        parameterRound2_originalTensorGermSpace atlas param S W)
    (K : parameterRound2_originalTensorGermSpace atlas param S W)
    (hK : seminorm 0 (K-H) < rho) :
    (round4ParameterProbeActualGermError atlas param S W seminorm H rho F hF g length tau hsm K).val =
      incrementsGlobalPrimaryMeanError F hF g K.val length tau := by
  simp only [round4ParameterProbeActualGermError,dite_eq_left hK]

/-- Same actual background substitutions, same complete probe, and the
derived physical mean residual in the original native tensor germ space.
All later observation orders share the already fixed entrance threshold. -/
theorem round4ParameterProbe_actual_forced_mean_finite_residual
    (atlas : BufferedAtlas M D) (param : Fin count → OpenPartialHomeomorph Ep Ep)
    (S : Fin atlas.count × Fin count → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (seminorm : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace atlas param S W))
    (H : parameterRound2_originalTensorGermSpace atlas param S W) (HBound : ℕ → ℝ)
    (hH : ∀ s, seminorm s H ≤ HBound s) (rho : ℝ) (hrho : 0 < rho)
    (B : ℕ → ℝ) (Csize Cdiff : ℕ → ℝ → ℝ) (q loss : ℕ)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I:=𝓙) (m:=m) (N:=N) (Λ:=Λ) (Β:=Β) F)
    (backgroundLength : ℕ) (tau delta epsilon : ℝ) (he : 0 < epsilon)
    (hecap : epsilon < round4ParameterProbeForcedCap HBound rho B Csize q loss)
    (hsm : ∀ K : parameterRound2_originalTensorGermSpace atlas param S W,
      seminorm 0 (K-H) < rho → incrementsGlobalPrimaryMeanError F hF g K.val backgroundLength tau ∈
        parameterRound2_originalTensorGermSpace atlas param S W) :
    let T := round4ParameterProbeActualGermError atlas param S W seminorm H rho F hF g backgroundLength tau hsm
    ∀ (_hsize : ∀ s R (K : parameterRound2_originalTensorGermSpace atlas param S W),
      seminorm 0 (K-H) < rho → seminorm (s+loss) K ≤ R → seminorm s (T K) ≤ epsilon*Csize s R)
      (_hdiff : ∀ s R (K L : parameterRound2_originalTensorGermSpace atlas param S W),
      seminorm 0 (K-H) < rho → seminorm 0 (L-H) < rho →
      seminorm (s+loss) K ≤ R → seminorm (s+loss) L ≤ R →
      seminorm s (T K-T L) ≤ epsilon*Cdiff s R*seminorm (s+loss) (K-L))
      (label : (Fin r × Bool) ↪ Fin p) (c : Fin r → Ep → D → M)
      (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I:=𝓙) (F b) (c l b x))
      (phase : Fin r → Ep × M → ℝ) (probeLength : ℕ)
      (a : Fin r → OpenPartialHomeomorph (Ep × M) X) (u : Fin p → ℝ)
      (P : parameterRound2_originalTensorGermSpace atlas param S W),
    P.val = (delta^2)⁻¹ • round4PrescribedNativeMean label F hF c vf phase tau probeLength a u →
    (∀ s, seminorm s P ≤ B s) → seminorm 0 P ≤ rho/4 →
    let A := round4ActualBackgroundMeanIterate F hF g backgroundLength tau delta H.val
      (round4PrescribedNativeMean label F hF c vf phase tau probeLength a)
    let R := round4ParameterProbeForcedProfile HBound B Csize loss
    let C0 := fun s => B s+max 0 (Csize s (HBound (s+loss)))
    let Cd := fun i s => max 0 (Cdiff s (max (R i (s+loss)) (R (i+1) (s+loss))))
    ∃ G : ℕ → parameterRound2_originalTensorGermSpace atlas param S W,
      (∀ i ≤ q+1, (G i).val = A i u ∧ seminorm 0 (G i-H) ≤ rho/2 ∧
        ∀ s, seminorm s (G i) ≤ R i s) ∧
      ∃ E : parameterRound2_originalTensorGermSpace atlas param S W,
        E.val = delta^2 • (incrementsGlobalPrimaryMeanError F hF g (A (q+1) u) backgroundLength tau -
          incrementsGlobalPrimaryMeanError F hF g (A q u) backgroundLength tau) ∧
        ∀ s, seminorm s E ≤ delta^2*(epsilon^(q+1)*parameterRound2_finiteMeanErrorCost C0 Cd loss (q+1) s) := by
  intro T hsize hdiff label c vf phase probeLength a u P hPv hP hP0 A R C0 Cd
  let G := round4ParameterProbeForcedIterate H P T
  have hmain := round4ParameterProbe_forced_finite_residual seminorm H HBound hH rho hrho B Csize Cdiff q loss
    P hP hP0 epsilon he hecap T hsize hdiff
  have hdom (i : ℕ) (hi : i ≤ q+1) : seminorm 0 (G i-H) < rho :=
    lt_of_le_of_lt (hmain.1 i hi).1 (by linarith)
  have hTv (i : ℕ) (hi : i ≤ q+1) : (T (G i)).val =
      incrementsGlobalPrimaryMeanError F hF g (G i).val backgroundLength tau :=
    round4ParameterProbeActualGermError_val atlas param S W seminorm H rho F hF g
      backgroundLength tau hsm (G i) (hdom i hi)
  have hGv : ∀ i ≤ q+1, (G i).val = A i u := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have hi' : i ≤ q+1 := by omega
      change H.val-P.val-(T (G i)).val = A (i+1) u
      rw [hPv,hTv i hi',ih hi']
      rfl
  let E0 := G (q+1)+P+T (G (q+1))-H
  let E := delta^2 • E0
  have hE0 : E0 = T (G (q+1))-T (G q) := by
    change (H-P-T (G q))+P+T (G (q+1))-H = _
    abel
  refine ⟨G,fun i hi => ⟨hGv i hi,(hmain.1 i hi).1,(hmain.1 i hi).2⟩,E,?_,?_⟩
  · change (delta^2 • E0).val = _
    rw [hE0]
    change delta^2 • ((T (G (q+1))).val-(T (G q)).val) = _
    rw [hTv (q+1) le_rfl,hTv q (by omega),hGv (q+1) le_rfl,hGv q (by omega)]
  · intro s
    change seminorm s (delta^2 • E0) ≤ _
    rw [map_smul_eq_mul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg delta)]
    exact mul_le_mul_of_nonneg_left (hmain.2 s) (sq_nonneg delta)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4ParameterProbe_actual_forced_mean_finite_residual
