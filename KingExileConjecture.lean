/-
  KingExileConjecture.lean — the "king's exile" conjecture
  ========================================================

  The idea (by the repository author, 22 Nov 2026), in words:
    In a fluid moving on its own (no external force), a region where vorticity piles up too
    strongly gets pushed out into a wider region before it has time to blow up: if it is curved,
    it flies away by itself; if it is straight, its neighbours bend it and then push it away.
    Only with perfect symmetry (or an external force holding it in place) can the "waist" keep
    narrowing forever, that is, actually blow up.

  This file only STATES the conjecture precisely. It does NOT prove it (nobody knows whether it
  is true or false). There is no `sorry` and no `axiom`: the conjecture is a `Prop`, i.e. a
  statement that may be true or false.

  How to use it:
  * In the repository: keep the file next to `NavierStokesLemmas.lean` and add
    `KingExileConjecture` to `lakefile.toml`.
  * On live.lean-lang.org: DELETE the line `import NavierStokesLemmas` below, then paste
    everything else at the END of `NavierStokesLemmas.lean`.
-/

import NavierStokesLemmas

noncomputable section

open MeasureTheory Set

namespace NavierStokes

/-! ## 1. What blowing up means -/

/-- The solution `F` BLOWS UP at `F.T`: there is no classical solution (with the same
viscosity) that agrees with `F` on `[0, F.T)` and lives longer than `F.T`. -/
def BlowsUp (F : NSClassicalSolution) : Prop :=
  ¬ ∃ G : NSClassicalSolution, G.ν = F.ν ∧ F.T < G.T ∧ ∀ t ∈ Ico 0 F.T, G.u t = F.u t

/-! ## 2. Circular symmetry about the z-axis (the "perfectly symmetric house") -/

/-- Rotation by an angle `θ` about the z-axis. -/
def rotZ (θ : ℝ) (v : E3) : E3 :=
  (Real.cos θ * EuclideanSpace.proj 0 v - Real.sin θ * EuclideanSpace.proj 1 v) • basisVec 0
    + (Real.sin θ * EuclideanSpace.proj 0 v + Real.cos θ * EuclideanSpace.proj 1 v) • basisVec 1
    + EuclideanSpace.proj 2 v • basisVec 2

/-- A velocity field with circular symmetry about the z-axis: rotating the whole house by any
angle leaves the flow looking exactly the same. -/
def IsAxisymmetric (v : E3 → E3) : Prop :=
  ∀ (θ : ℝ) (x : E3), v (rotZ θ x) = rotZ θ (v x)

/-! ## 3. The king's exile conjecture -/

/-- **The king's exile conjecture (weak form): blow-up is not stable.**
If a solution `F` blows up at `F.T`, then perturbing the initial datum ever so slightly (an `L²`
difference smaller than any `ε`) and breaking its circular symmetry gives a solution `G` that
survives past time `F.T`: the mosquito flies in, and the king is pushed out onto the balcony.

Note: if Navier–Stokes never blows up, this conjecture holds trivially (see
`exile_of_global_regularity` below). The conjecture only has content if an unforced blow-up
exists. -/
def KingExileConjecture : Prop :=
  ∀ F : NSClassicalSolution, BlowsUp F →
    ∀ ε > 0, ∃ G : NSClassicalSolution,
      G.ν = F.ν ∧ F.T < G.T ∧
      normL2 (fun x => G.u 0 x - F.u 0 x) < ε ∧
      ¬ IsAxisymmetric (G.u 0)

/-- **The king's exile conjecture (strong form): only symmetric houses blow up.**
Every unforced blow-up starts from circularly symmetric initial data (about the z-axis, after
a suitable rotation of the coordinates).
WARNING: this is a very strong claim and may be false for other reasons, for example because
there are kinds of symmetry other than circular symmetry. It is recorded for comparison with the
weak form. -/
def KingExileConjectureStrong : Prop :=
  ∀ F : NSClassicalSolution, BlowsUp F → IsAxisymmetric (F.u 0)

/-! ## 4. A small theorem with a real proof -/

/-- If no solution blows up (i.e. Navier–Stokes is globally smooth), then the king's exile
conjecture holds trivially. In other words, the conjecture is WEAKER than the Millennium Problem,
and so may be easier to approach. -/
theorem exile_of_global_regularity
    (h : ∀ F : NSClassicalSolution, ¬ BlowsUp F) : KingExileConjecture := by
  intro F hF
  exact absurd hF (h F)

/-- The same for the strong form. -/
theorem exileStrong_of_global_regularity
    (h : ∀ F : NSClassicalSolution, ¬ BlowsUp F) : KingExileConjectureStrong := by
  intro F hF
  exact absurd hF (h F)

end NavierStokes
