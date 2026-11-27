import PurityBootstrap
import Lean.Util.CollectAxioms

/-! Axiom audit for every exported public theorem in `PurityBootstrap`, PLUS an exhaustive
fail-closed project-wide scan over all theorem constants defined by `PurityBootstrap.*`.
Every theorem must depend ONLY on a subset of `[propext, Classical.choice, Quot.sound]`. -/

#print axioms PurityBootstrap.purityUpdate_one_sub_cube
#print axioms PurityBootstrap.finset_purity_square_bound
#print axioms PurityBootstrap.tsum_purity_square_bound
#print axioms PurityBootstrap.finset_purity_rpow_mono
#print axioms PurityBootstrap.tsum_purity_rpow_mono
#print axioms PurityBootstrap.PuritySystem1D.rounded_coupled_update
#print axioms PurityBootstrap.PuritySystem1D.dyadic_purities
#print axioms PurityBootstrap.tsum_rpow_le_rpow_div
#print axioms PurityBootstrap.purity_interpolation
#print axioms PurityBootstrap.gibbs_purity_implies_unique_ground_and_gap
#print axioms PurityBootstrap.uniform_gap_from_purities
#print axioms PurityBootstrap.SpectralSystem1D.toPuritySystem1D
#print axioms PurityBootstrap.SpectralSystem1D.interp
#print axioms PurityBootstrap.SpectralSystem1D.spatial_purity_mono_even
#print axioms PurityBootstrap.SpectralSystem1D.uniform_gap
#print axioms PurityBootstrap.ExactCertificates.s1_filter_J_pos_ray
#print axioms PurityBootstrap.ExactCertificates.s1_filter_J_neg_ray
#print axioms PurityBootstrap.ExactCertificates.s1_filter_N_pos_ray
#print axioms PurityBootstrap.ExactCertificates.s1_filter_N_neg_ray
#print axioms PurityBootstrap.ExactCertificates.s1_dominant_existence_and_initial_bounds
#print axioms PurityBootstrap.ExactCertificates.s1_six_rounded_updates_exact
#print axioms PurityBootstrap.ExactCertificates.s1_six_rounds_to_2304
#print axioms PurityBootstrap.ExactCertificates.s2_all_scalar_initializations_exact
#print axioms PurityBootstrap.ExactCertificates.parameter_row_source1_exact
#print axioms PurityBootstrap.ExactCertificates.parameter_row_source2_exact
#print axioms PurityBootstrap.ExactCertificates.haldane_gap_source1_from_initial_36
#print axioms PurityBootstrap.ExactCertificates.haldane_gap_source2_from_initial_60
#print axioms PurityBootstrap.HigherDim.general_dim_quadratic_contraction
#print axioms PurityBootstrap.HigherDim.PuritySystem2D.doubling_round_2d
#print axioms PurityBootstrap.HigherDim.PuritySystem2D.dyadic_purities_2d_from_three
#print axioms PurityBootstrap.HigherDim.PuritySystem2D.uniform_gap_2d_from_three
#print axioms PurityBootstrap.HigherDim.PuritySystem2D.uniform_gap_2d
#print axioms PurityBootstrap.SymmetryTwists.ising_sector_ratio_bound
#print axioms PurityBootstrap.SymmetryTwists.twisted_sector_purity_bound
#print axioms PurityBootstrap.SymmetryTwists.ising_exponential_splitting
#print axioms PurityBootstrap.SymmetryTwists.ising_splitting_12uj
#print axioms PurityBootstrap.SymmetryTwists.gibbs_min_le_of_Z_le
#print axioms PurityBootstrap.SymmetryTwists.IsingTwistSystem.ising_multiplet_theorem
#print axioms PurityBootstrap.SymmetryTwists.IsingTwistSystem.ising_multiplet_sorted
#print axioms PurityBootstrap.SymmetryTwists.volume_law_fourth_power_step
#print axioms PurityBootstrap.SymmetryTwists.volume_law_iterated
#print axioms PurityBootstrap.MatrixTools.exp_rayleigh_le_matZ
#print axioms PurityBootstrap.MatrixTools.matZ_convex_combo_le
#print axioms PurityBootstrap.MatrixTools.log_convex_rectangle_le
#print axioms PurityBootstrap.MatrixTools.gershgorin_matZ_le
#print axioms PurityBootstrap.MatrixTools.exp_div_pow2_lower
#print axioms PurityBootstrap.MatrixTools.exp_neg_div_pow2_upper
#print axioms PurityBootstrap.MatrixTools.exp_neg_div_pow2_lower
#print axioms PurityBootstrap.IsingHamiltonian.H_ising_isHermitian
#print axioms PurityBootstrap.IsingHamiltonian.ising_seam_ordering
#print axioms PurityBootstrap.IsingMPS.mpsVec_norm_sq
#print axioms PurityBootstrap.IsingMPS.mpsVec_H_X
#print axioms PurityBootstrap.IsingMPS.mpsVec_H_XX
#print axioms PurityBootstrap.IsingMPS.mpsVec_H_ZZ
#print axioms PurityBootstrap.BlockGershgorin.certify_H8_matZ_upper
#print axioms PurityBootstrap.CandidateE.corner_15_47_Zplus_le
#print axioms PurityBootstrap.CandidateE.corner_15_48_Zplus_le
#print axioms PurityBootstrap.CandidateE.corner_16_47_Zplus_le
#print axioms PurityBootstrap.CandidateE.corner_16_48_Zplus_le
#print axioms PurityBootstrap.CandidateE.mps16_rayleigh_le_matZ
#print axioms PurityBootstrap.CandidateE.candidate_e_rectangle_Qplus_ge
#print axioms PurityBootstrap.CandidateE.candidate_e_three_rounded_updates_exact
#print axioms PurityBootstrap.CandidateE.candidate_e_three_rounds_to_64
#print axioms PurityBootstrap.CandidateE.candidate_e_rectangle_multiplet
#print axioms PurityBootstrap.LieTrotter.tendsto_trotter3
#print axioms PurityBootstrap.LieTrotter.exp_involutive
#print axioms PurityBootstrap.LieTrotter.trace_exp_eq_matZ
#print axioms PurityBootstrap.LieTrotter.psd_pair_spatial_ineqs
#print axioms PurityBootstrap.LieTrotter.TrotterIsingSystem.ising_multiplet_sorted_labeled
#print axioms PurityBootstrap.LieTrotter.TrotterIsingSystem.ising_multiplet_sorted
#print axioms PurityBootstrap.IsingTrotter.isingTrotterSystem
#print axioms PurityBootstrap.IsingTrotter.candidate_e_unconditional_rectangle_theorem
#print axioms PurityBootstrap.IsingTrotter.charpoly_blockDiagonal_bool
#print axioms PurityBootstrap.IsingTrotter.charpoly_full_hamiltonian_roots
#print axioms PurityBootstrap.IsingTrotter.candidate_e_unconditional_full_hamiltonian_theorem
#print axioms PurityBootstrap.ExactCertificates.s1_six_rounds_to_2304_exact
#print axioms PurityBootstrap.MomentInit.capped_mass_finset
#print axioms PurityBootstrap.MomentInit.capped_mass_tsum
#print axioms PurityBootstrap.MomentInit.uncapped_mass_tsum
#print axioms PurityBootstrap.MomentInit.polynomial_filter_tsum
#print axioms PurityBootstrap.MomentInit.filterPolyCoeffs_eval_eq
#print axioms PurityBootstrap.MomentInit.shiftedFilterCoeff_eval_eq
#print axioms PurityBootstrap.MomentInit.filter_ray_gt_of_check
#print axioms PurityBootstrap.MomentInit.source1_seed2304_from_projected_moments
#print axioms PurityBootstrap.MomentInit.source1_seed2304_from_raw_table
#print axioms PurityBootstrap.MomentInit.source1_gap_from_raw_thermal_table
#print axioms PurityBootstrap.MomentInit.source1_gap_from_thermal_table
#print axioms PurityBootstrap.CandidateA.ca_rays155_exact
#print axioms PurityBootstrap.CandidateA.ca_rays23_exact
#print axioms PurityBootstrap.CandidateA.ca_pows14_exact
#print axioms PurityBootstrap.CandidateA.ca_initial_bounds_exact
#print axioms PurityBootstrap.CandidateA.ca_four_rounded_updates_exact
#print axioms PurityBootstrap.CandidateA.ca_four_rounds_to_896_exact
#print axioms PurityBootstrap.CandidateA.temp_transfer_112
#print axioms PurityBootstrap.CandidateA.candidate_a_seed896_from_raw_table
#print axioms PurityBootstrap.CandidateA.candidate_a_uniform_gap_896
#print axioms PurityBootstrap.Spin1Hamiltonian.U_cart_to_sz_conj_S
#print axioms PurityBootstrap.Spin1Hamiltonian.U_cart_to_sz_conj_SzSq
#print axioms PurityBootstrap.Spin1Hamiltonian.Z_spin1_eq_sum_exp
#print axioms PurityBootstrap.Spin1Hamiltonian.exists_eig_le_of_rayleigh
#print axioms PurityBootstrap.Spin1Compactness.tendsto_trace_pow_of_first_order
#print axioms PurityBootstrap.Spin1Compactness.l2_seq_compact_moments
#print axioms PurityBootstrap.Spin1Transfer.K_mat_comm_U
#print axioms PurityBootstrap.Spin1Transfer.K_mat_hilbert_schmidt_le
#print axioms PurityBootstrap.Spin1Transfer.trace_K_pow_mul_U_eq_trace_T_slice_pow
#print axioms PurityBootstrap.Spin1Transfer.tendsto_trace_K_pow_mul_U
#print axioms PurityBootstrap.Spin1Transfer.spin1_D4_sector_moments
#print axioms PurityBootstrap.Spin1Transfer.spin1_D2_sector_moments
#print axioms PurityBootstrap.Spin1Transfer.spin1_spatial_eigs
#print axioms PurityBootstrap.Spin1PhysicalGap.spin1SpectralSystem
#print axioms PurityBootstrap.Spin1PhysicalGap.candidate_a_physical_spin1_gap_896
#print axioms PurityBootstrap.Spin1PhysicalGap.candidate_a_physical_spin1_charpoly_gap_896
#print axioms PurityBootstrap.Spin1PhysicalGap.source1_physical_spin1_gap_2304
#print axioms PurityBootstrap.Spin1PhysicalGap.source1_physical_spin1_charpoly_gap_2304
#print axioms PurityBootstrap.Spin1Interval.matZ_anti_of_le
#print axioms PurityBootstrap.Spin1Interval.spin1_S_transport
#print axioms PurityBootstrap.Spin1Interval.spin1_T_transport
#print axioms PurityBootstrap.Spin1Interval.int6_five_rounded_updates_exact
#print axioms PurityBootstrap.Spin1Interval.int7_four_rounded_updates_exact
#print axioms PurityBootstrap.Spin1Interval.candidate_a_physical_spin1_interval_gap_1792
#print axioms PurityBootstrap.Spin1Interval.candidate_a_physical_spin1_interval_charpoly_gap_1792
#print axioms PurityBootstrap.Spin1Interval.candidate_a_physical_spin1_interval_gap_896
#print axioms PurityBootstrap.Spin1Interval.candidate_a_physical_spin1_interval_charpoly_gap_896
#print axioms PurityBootstrap.Ising2DTrotter.Z_M_eq_trace_time
#print axioms PurityBootstrap.Ising2DTrotter.Z_M_eq_trace_Tx
#print axioms PurityBootstrap.Ising2DTrotter.Z_M_eq_trace_Ty
#print axioms PurityBootstrap.Ising2DTrotter.tendsto_Z_M
#print axioms PurityBootstrap.Ising2DSeed.matZ_bond2Q
#print axioms PurityBootstrap.Ising2DSeed.H_2d_2x2_midpoint
#print axioms PurityBootstrap.Ising2DSeed.Z_2d_2x2_le
#print axioms PurityBootstrap.Ising2DSeed.one_le_Z_2d_shift_one
#print axioms PurityBootstrap.Ising2DSeed.scalar_F5_pow16_le
#print axioms PurityBootstrap.Ising2DSeed.ising2d_seed_2x2
#print axioms PurityBootstrap.Ising2DGap.ising2DPuritySystem
#print axioms PurityBootstrap.Ising2DGap.ising2D_hInterp
#print axioms PurityBootstrap.Ising2DGap.ising_2d_unconditional_rectangle_gap
#print axioms PurityBootstrap.Ising2DGap.ising_2d_unconditional_rectangle_charpoly_gap

/-! Exhaustive fail-closed project-wide audit:
1. Verify all 29 tracked `PurityBootstrap` modules are present in the imported environment.
2. Reject ANY `.axiomInfo` declaration in any `PurityBootstrap` module (even unused axioms).
3. Verify EVERY theorem constant defined in `PurityBootstrap` modules (including private/generated
   lemmas) depends ONLY on a subset of `[propext, Classical.choice, Quot.sound]`. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expectedMods : Array Name := #[
    `PurityBootstrap,
    `PurityBootstrap.Basic,
    `PurityBootstrap.BlockGershgorin,
    `PurityBootstrap.CandidateA.Certificate,
    `PurityBootstrap.CandidateA.Data,
    `PurityBootstrap.CandidateE.Basis,
    `PurityBootstrap.CandidateE.Corner15_47,
    `PurityBootstrap.CandidateE.Corner15_48,
    `PurityBootstrap.CandidateE.Corner16_47,
    `PurityBootstrap.CandidateE.Corner16_48,
    `PurityBootstrap.CandidateE.RectangleTheorem,
    `PurityBootstrap.ExactCertificates,
    `PurityBootstrap.HigherDim,
    `PurityBootstrap.Ising2DGap,
    `PurityBootstrap.Ising2DSeed,
    `PurityBootstrap.Ising2DTrotter,
    `PurityBootstrap.IsingHamiltonian,
    `PurityBootstrap.IsingMPS,
    `PurityBootstrap.IsingTrotter,
    `PurityBootstrap.LieTrotter,
    `PurityBootstrap.MatrixTools,
    `PurityBootstrap.MomentInit,
    `PurityBootstrap.OneD,
    `PurityBootstrap.Spin1Compactness,
    `PurityBootstrap.Spin1Hamiltonian,
    `PurityBootstrap.Spin1Interval,
    `PurityBootstrap.Spin1PhysicalGap,
    `PurityBootstrap.Spin1Transfer,
    `PurityBootstrap.SymmetryTwists
  ]
  for modName in expectedMods do
    unless env.header.moduleNames.contains modName do
      throwError "Expected project module missing from audit closure: {modName}"
  let mut count : Nat := 0
  let mut publics : Nat := 0
  for (name, info) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      if `PurityBootstrap |>.isPrefixOf (env.header.moduleNames[idx.toNat]!) then
        if let .axiomInfo _ := info then
          throwError "Disallowed project axiom declaration found: {name}"
        if info.isTheorem then
          count := count + 1
          if `PurityBootstrap |>.isPrefixOf name then publics := publics + 1
          let axs ← collectAxioms name
          unless axs.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
            throwError "Unexpected axioms for {name}: {axs}"
  logInfo m!"PASS: Verified all {expectedMods.size} project modules, 0 project axioms, and all {count} project theorem constants ({publics} under PurityBootstrap.*): strictly [propext, Classical.choice, Quot.sound]."
