import GlobalEmbedding.Paper.PeriodicCAlphaFunction

/-!
# Extensionality of the periodic Hölder carrier

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-carrier-injective`.
-/

namespace GlobalEmbedding.Paper

/-- An actual raw periodic Hölder element is determined by its underlying lift.

Proof: every other field is a proposition, so equality of the underlying functions determines
the structure by proof irrelevance. Source: `lem:balanced`, Hölder-carrier expansion. -/
theorem periodicCAlpha_toFun_injective {a N k : ℕ} {α : ℝ} :
    Function.Injective (PeriodicCAlphaFunction.toFun (a := a) (N := N) (k := k) (α := α)) := by
  intro f g h
  cases f
  cases g
  cases h
  rfl

#print axioms periodicCAlpha_toFun_injective

end GlobalEmbedding.Paper
