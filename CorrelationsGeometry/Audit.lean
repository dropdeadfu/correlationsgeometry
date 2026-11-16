import CorrelationsGeometry.FieldContent
import CorrelationsGeometry.FormFields
import CorrelationsGeometry.Concavity
import CorrelationsGeometry.PoissonTrace
import CorrelationsGeometry.TwoModeExpansion

/-!
# Audit

Prints, for each main theorem, the axioms its proof depends on. A proof that used `sorry` would
list `sorryAx`. The expected output is at most the three standard axioms of Lean with classical
logic: `propext`, `Classical.choice`, `Quot.sound`.
-/

open CorrelationsGeometry

#print axioms theorem_3_11
#print axioms poisson_trace
#print axioms concaveOn_iInf_affine
#print axioms ConcaveOn.add_neg_le
#print axioms second_order_nonpos
#print axioms sum_response_eq_zero_iff
#print axioms sum_second_order_eq_zero_iff
#print axioms lam_le_one
#print axioms lam_eq_one_iff
#print axioms lam_scalar_three
#print axioms kappa_succ
#print axioms Content.relation_i
#print axioms Content.covariant_iff
#print axioms Content.no_induced_action
#print axioms Content.a_eq_zero_of_covariant_of_str1
#print axioms Content.lam_scalar_dirac_mem
#print axioms Masses.relation_ii
#print axioms Masses.relation_iii
#print axioms Masses.a_eq_zero_of_covariant
#print axioms Masses.ratio_of_covariant
#print axioms Masses.a_eq_zero_of_covariant_profile
#print axioms Masses.lf_pos_of_no_vector
#print axioms Masses.exists_Z_iff
#print axioms MassTerms.scalar_leading
#print axioms MassTerms.scalar_finite
#print axioms MassTerms.scalar_log
#print axioms MassTerms.dirac_all
#print axioms MassTerms.vector_all
#print axioms hasDerivAt_entropyFn
#print axioms hasDerivAt_entropyFnDeriv
#print axioms exists_abs_expansion_sub_le
#print axioms twoModeMI_neg
#print axioms two_mode_expansion
#print axioms two_mode_expansion_isBigO
