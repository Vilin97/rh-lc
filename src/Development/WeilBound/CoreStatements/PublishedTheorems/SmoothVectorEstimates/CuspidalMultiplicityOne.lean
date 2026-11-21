module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.ConvergenceEntriesGeneralLinearHolds
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.MinusculeCentralEigen
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.SatakeEigenvalues

@[expose] public section

namespace PositivityTheory.jumpWindows

theorem cuspidalMultiplicityOne : GlobalTheory.Published.CuspidalMultiplicityOne := by
  have h9 : G9 := whittaker_uniqueness_local
    PositivityTheory.JacquetShalikaLocal.minuscule_eigenvalue
    PositivityTheory.JacquetShalikaLocal.satake_eigenvalue_formula
    automorphic_basic_setup_holds whittaker_functional_exists_holds
  have h8 : G8 := smooth_vector_orbit_invariance automorphic_basic_setup_holds
    whittaker_functional_exists_holds smooth_vectors_regular_holds h9
    convergence_entries_general_linear_holds
  have hv : WhittakerVanishingImpliesZero := mirror_global_of
    positive_matrix_block_product_holds automorphic_basic_setup_holds
    whittaker_functional_exists_holds h9 convergence_entries_general_linear_holds
    local_uniqueness_auxiliary_holds good_inverse_dense_range_holds
  have hm : Meet := meet_of orthogonalSplitPolarizationVanishes
    positive_matrix_block_product_holds automorphic_basic_setup_holds multiplicity_one_holds
    almost_everywhere_spherical averaging_projection_linear_holds bounded_invariant_L2_holds
    hecke_operator_automorphic_holds whittaker_functional_exists_holds smooth_vectors_regular_holds
    whittaker_factorization_places_holds h8 adelic_character_condition_holds hv
  exact mean_convergence_of (smo_of (smonorm_of hm (finite_part_of_meet hm))
    finite_infinite_product_one_holds)

end PositivityTheory.jumpWindows
