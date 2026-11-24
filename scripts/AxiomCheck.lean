/-
  scripts/AxiomCheck.lean — prints the axioms used by the main theorems.
  Run: `lake env lean scripts/AxiomCheck.lean`
  Expected result for every line: `[propext, Classical.choice, Quot.sound]`.
-/
import NavierStokesLemmas
import KingExileConjecture
import NavierStokesTorus
import NavierStokesBlowup
import NavierStokesObstructions

-- Original file
#print axioms NavierStokes.conditional_regularity
#print axioms NavierStokes.lemma1_geometric_depletion
#print axioms NavierStokes.lemma2_enstrophy_bound
#print axioms NavierStokes.lemma3_bkm
#print axioms NavierStokes.lemma1_near_far_depletion
#print axioms NavierStokes.exile_of_global_regularity
-- Stage 1 (𝕋³)
#print axioms NavierStokes.Torus.integral_cubeQ_fderiv_eq_zero
#print axioms NavierStokes.Torus.integral_cubeQ_gradDot_self
#print axioms NavierStokes.Torus.NSPeriodicData.energy_equality
#print axioms NavierStokes.Torus.NSPeriodicData.enstrophy_balance
-- G1–G5
#print axioms NavierStokes.Blowup.riccati_blowup_time
#print axioms NavierStokes.Blowup.leray_rate_NS_of_GN
#print axioms NavierStokes.Blowup.small_data_enstrophy_bound
#print axioms NavierStokes.Blowup.blowup_requires_large_data_at
#print axioms NavierStokes.Blowup.NSBlowupConjecture.witness_constraints
-- H1–H2
#print axioms NavierStokes.Obstructions.NSSteadyState.exists_const
#print axioms NavierStokes.Obstructions.NSSteadyState.no_unstable_mode
#print axioms NavierStokes.Obstructions.riccati_requires_stretching_margin
-- H3
#print axioms NavierStokes.Blowup.reflectSol
#print axioms NavierStokes.Blowup.nsUnique
#print axioms NavierStokes.Blowup.oddSymmetry_invariant
#print axioms NavierStokes.Blowup.NSBlowupConjecture_of_leray
#print axioms NavierStokes.Blowup.NSBlowupConjecture_of_scenario
#print axioms NavierStokes.Blowup.NSBlowupConjecture_of_eulerType
-- H4
#print axioms NavierStokes.Blowup.toroidalDipoleInit_mem
#print axioms NavierStokes.Blowup.toroidalDipoleInit_smooth
#print axioms NavierStokes.Blowup.toroidalDipoleInit_ne_zero
-- H5 (Clay (D))
#print axioms NavierStokes.Blowup.ClaySmoothSolution.exists_periodic_pressure
#print axioms NavierStokes.Blowup.clay_problem_D_of_blowupConjecture
