import GlobalEmbedding.Paper.FreeHopfProductNative
import GlobalEmbedding.Paper.FreeCorrectionStability
import Mathlib.Topology.Compactness.Compact

/-!
# Uniform normalized margins on the actual whole Hopf product

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 477–495.
DAG: `free-hopf-uniform-normalized-margins`.
The UniformParameter section is W4's frozen compiled prefix, reused verbatim by sole publisher W5.
Provenance: W4UniformParameterPrefix.lean SHA a62c53f4231775eb8346c619d4a789ab84b3336d3e48390be3ed485a5a5ec03f.
W5 adds only the actual Hopf instantiation, zero-data branch, coverage and injectivity consequences.
The prior parallel W5 generic draft is preserved in history and is not a published provider.
-/

noncomputable section
namespace GlobalEmbedding.Paper

section UniformParameter

variable {X V E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual continuous normalized frames which are injective at zero on a compact patch have
one positive time interval and one positive lower bound on that entire patch. The existing compact
lower-bound theorem supplies the zero margin; the native tube lemma makes the actual perturbation
smaller than half that margin simultaneously at every point of the patch. -/
theorem free_compact_frame_time_interval (K : Set X) (hK : IsCompact K)
    (B : ℝ × X → V →L[ℝ] E) (hB : Continuous B)
    (hinj : ∀ x ∈ K, Function.Injective (B (0, x))) :
    ∃ δ μ : ℝ, 0 < δ ∧ 0 < μ ∧
      ∀ ε : ℝ, |ε| < δ → ∀ x ∈ K, ∀ u, μ * ‖u‖ ≤ ‖B (ε, x) u‖ := by
  obtain ⟨μ, hμ, hzero⟩ := free_compact_injective_lower_bound hK (fun x ↦ B (0, x))
    (hB.comp (continuous_const.prodMk continuous_id)).continuousOn hinj
  let N : Set (ℝ × X) := {p | ‖B p - B (0, p.2)‖ < μ / 2}
  have hN : IsOpen N := isOpen_lt
    ((hB.sub (hB.comp (continuous_const.prodMk continuous_snd))).norm) continuous_const
  have hbase : ({0} : Set ℝ) ×ˢ K ⊆ N := by
    rintro ⟨ε, x⟩ ⟨hε, hx⟩
    have he : ε = 0 := hε
    subst ε
    change ‖B (0, x) - B (0, x)‖ < μ / 2
    simpa only [sub_self, norm_zero] using half_pos hμ
  obtain ⟨U, W, hU, hW, h0U, hKW, hUW⟩ :=
    generalized_tube_lemma isCompact_singleton hK hN hbase
  have hzeroU : (0 : ℝ) ∈ U := h0U (by simp)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzeroU)
  refine ⟨δ, μ / 2, hδ, half_pos hμ, ?_⟩
  intro ε hε x hx u
  have heU : ε ∈ U := hball (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hε)
  have herr : ‖B (0, x) - B (ε, x)‖ ≤ μ / 2 := by
    rw [norm_sub_rev]
    exact (hUW ⟨heU, hKW hx⟩).le
  have hh := linear_map_lower_bound_perturbation (B (0, x)) (B (ε, x)) μ (μ / 2)
    (hzero x hx) herr u
  convert hh using 1; ring

/-- Shrinking the actual pivot buffer by a factor of two supplies two compact overlapping
patches. Actual limiting injectivity gives one common interval and one common positive margin
for both true normalized frame fields, including at parameter zero. -/
theorem free_two_patch_uniform_interval [CompactSpace X]
    (κ : X → ℝ) (hκ : Continuous κ) (D : ℝ) (hD : 0 < D)
    (Bn Bf : ℝ × X → V →L[ℝ] E) (hBn : Continuous Bn) (hBf : Continuous Bf)
    (hin : ∀ x, |κ x| < D → Function.Injective (Bn (0, x)))
    (hif : ∀ x, κ x ≠ 0 → Function.Injective (Bf (0, x))) :
    ∃ δ μ : ℝ, 0 < δ ∧ 0 < μ ∧ ∀ ε : ℝ, |ε| < δ → ∀ x,
      (|κ x| ≤ D / 2 → ∀ u, μ * ‖u‖ ≤ ‖Bn (ε, x) u‖) ∧
      (D / 6 ≤ |κ x| → ∀ u, μ * ‖u‖ ≤ ‖Bf (ε, x) u‖) := by
  have hKn : IsCompact {x | |κ x| ≤ D / 2} :=
    (isClosed_le hκ.abs continuous_const).isCompact
  have hKf : IsCompact {x | D / 6 ≤ |κ x|} :=
    (isClosed_le continuous_const hκ.abs).isCompact
  obtain ⟨δn, μn, hδn, hμn, hn⟩ := free_compact_frame_time_interval _ hKn Bn hBn
    (fun x hx ↦ hin x (by have hh : |κ x| ≤ D / 2 := hx; linarith))
  obtain ⟨δf, μf, hδf, hμf, hf⟩ := free_compact_frame_time_interval _ hKf Bf hBf
    (fun x hx ↦ hif x (by
      intro hz
      have hh : D / 6 ≤ |κ x| := hx
      rw [hz, abs_zero] at hh
      linarith))
  refine ⟨min δn δf, min μn μf, lt_min hδn hδf, lt_min hμn hμf, ?_⟩
  intro ε hε x
  constructor
  · intro hx u
    exact (mul_le_mul_of_nonneg_right (min_le_left μn μf) (norm_nonneg u)).trans
      (hn ε (lt_of_lt_of_le hε (min_le_left δn δf)) x hx u)
  · intro hx u
    exact (mul_le_mul_of_nonneg_right (min_le_right μn μf) (norm_nonneg u)).trans
      (hf ε (lt_of_lt_of_le hε (min_le_right δn δf)) x hx u)

end UniformParameter

/-- Actual epsilon-zero ranks on the true near/far regions yield one common
positive parameter interval and Euclidean lower bound on both closed buffered patches.
Proof: put d=d0/2. The two actual closed patches are compact; near lies strictly
inside the supplied rank buffer, and far excludes kappa zero. Apply the accepted
compact frame lower bound, Mathlib compact-neighborhood uniformization, and the
accepted operator perturbation estimate to each genuine family, then take common
minima. The actual coefficient space may be zero-dimensional and the source empty. -/
theorem freeHopf_uniform_normalized_margins {a N : ℕ} {Idx : Type*} [Fintype Idx]
    (C : Fin a → ℕ) (κ : FreeHopfProduct C → ℝ) (hκ : Continuous κ)
    {d0 : ℝ} (hd0 : 0 < d0)
    (Bnear Bfar : ℝ × FreeHopfProduct C →
      EuclideanSpace ℝ Idx →L[ℝ] EuclideanSpace ℝ (Fin N))
    (hnear : Continuous Bnear) (hfar : Continuous Bfar)
    (hinjNear : ∀ x, |κ x| < d0 → Function.Injective (Bnear (0, x)))
    (hinjFar : ∀ x, κ x ≠ 0 → Function.Injective (Bfar (0, x))) :
    ∃ d ε₀ μ : ℝ, d = d0 / 2 ∧ 0 < d ∧ 0 < ε₀ ∧ 0 < μ ∧
      (∀ x, |κ x| ≤ d ∨ d / 3 ≤ |κ x|) ∧
      (∀ ε, |ε| < ε₀ → ∀ x, |κ x| ≤ d →
        Function.Injective (Bnear (ε, x)) ∧ ∀ u, μ * ‖u‖ ≤ ‖Bnear (ε, x) u‖) ∧
      (∀ ε, |ε| < ε₀ → ∀ x, d / 3 ≤ |κ x| →
        Function.Injective (Bfar (ε, x)) ∧ ∀ u, μ * ‖u‖ ≤ ‖Bfar (ε, x) u‖) := by
  have huniform : ∃ δ μ : ℝ, 0 < δ ∧ 0 < μ ∧ ∀ ε : ℝ, |ε| < δ → ∀ x,
      (|κ x| ≤ d0 / 2 → ∀ u, μ * ‖u‖ ≤ ‖Bnear (ε, x) u‖) ∧
      (d0 / 6 ≤ |κ x| → ∀ u, μ * ‖u‖ ≤ ‖Bfar (ε, x) u‖) := by
    rcases subsingleton_or_nontrivial (EuclideanSpace ℝ Idx) with hzero | hnonzero
    · have : Subsingleton (EuclideanSpace ℝ Idx) := hzero
      refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
      intro ε _ x
      constructor <;> intro _ u <;> simp [Subsingleton.elim u 0]
    · have : Nontrivial (EuclideanSpace ℝ Idx) := hnonzero
      exact free_two_patch_uniform_interval κ hκ d0 hd0 Bnear Bfar hnear hfar
        hinjNear hinjFar
  obtain ⟨ε₀, μ, hε₀, hμ, hbound⟩ := huniform
  let d : ℝ := d0 / 2
  have hd : 0 < d := half_pos hd0
  have hscale : d / 3 = d0 / 6 := by dsimp only [d]; ring
  have hinj (A : EuclideanSpace ℝ Idx →L[ℝ] EuclideanSpace ℝ (Fin N))
      (hb : ∀ u, μ * ‖u‖ ≤ ‖A u‖) : Function.Injective A := by
    have ha : AntilipschitzWith (⟨μ⁻¹, inv_nonneg.mpr hμ.le⟩ : NNReal) A :=
      A.antilipschitz_of_bound (fun u ↦ (le_inv_mul_iff₀ hμ).mpr (hb u))
    exact ha.injective
  refine ⟨d, ε₀, μ, rfl, hd, hε₀, hμ, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : |κ x| ≤ d
    · exact Or.inl hx
    · exact Or.inr (by linarith [lt_of_not_ge hx])
  · intro ε hε x hx
    have hb := (hbound ε hε x).1 hx
    exact ⟨hinj _ hb, hb⟩
  · intro ε hε x hx
    have hb := (hbound ε hε x).2 (by rwa [← hscale])
    exact ⟨hinj _ hb, hb⟩

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.free_compact_frame_time_interval
#print axioms GlobalEmbedding.Paper.free_two_patch_uniform_interval
#print axioms GlobalEmbedding.Paper.freeHopf_uniform_normalized_margins
