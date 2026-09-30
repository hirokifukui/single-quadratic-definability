import DiophCompression.QuadraticPPSeparation
import DiophCompression.AtomicDegreeRank
import DiophCompression.Folding
import DiophCompression.OneSorted
import DiophCompression.OneSortedPPCoding
import DiophCompression.OneSortedFragments
import DiophCompression.OneSortedPPFolding
import DiophCompression.APALLogicCore
import DiophCompression.FiniteFiberGrowth
import DiophCompression.PolynomialGraphs
import DiophCompression.SkolemReduction
import DiophCompression.FiniteFiberCardinality
import DiophCompression.FragmentLattice
import DiophCompression.MultivariatePolynomialGraphs
import DiophCompression.IntPrimrec
import DiophCompression.ComputabilityFragments
import DiophCompression.ComputableFunctions
import DiophCompression.HaltingTransport
import DiophCompression.UnaryDiagonal
import DiophCompression.QuadraticCodes
import DiophCompression.GlobalQuadraticCode
import DiophCompression.EffectiveDiagonal
import DiophCompression.DPRMTransport
import DiophCompression.InfiniteFiberCertificate
import DiophCompression.StructuredCertificates
import DiophCompression.OutputNegation
import DiophCompression.LeafExtraction
import DiophCompression.SummitTarget
import DiophCompression.BranchExhaustion
import DiophCompression.GSInputCompiler
import DiophCompression.SummitReduction
import DiophCompression.SemanticQuadratic.LeafDataD3D6
import DiophCompression.PeriodicProgressionCore
import DiophCompression.StructuredFamilyCore
import DiophCompression.PellOrbitCore
import DiophCompression.SemanticQuadratic.PellFiberOrbit
import DiophCompression.SemanticQuadratic.PellOrbitOfXPos
import DiophCompression.SemanticQuadraticTwoWitness.RankOneCoupledData
import DiophCompression.SemanticQuadratic.QuadraticFamilyData
import DiophCompression.SemanticQuadratic.OneWitnessFamilyData
import DiophCompression.SemanticQuadratic.FiberDichotomyData
import DiophCompression.SemanticQuadratic.PellDichotomyData
import DiophCompression.SemanticQuadratic.DegenerateDichotomyData
import DiophCompression.SemanticQuadraticTwoWitness.RankOneUncoupledData
import DiophCompression.SemanticQuadraticTwoWitness.RankOneNormalData
import DiophCompression.SemanticQuadraticMatrix.FullRankAssemblyData
import DiophCompression.SemanticQuadraticSingular.SingularDataCore
import DiophCompression.SemanticQuadraticGeneral.TopDichotomyData
import DiophCompression.SemanticQuadraticMatrix.QuadraticFamilyA2
import DiophCompression.PeriodicProgressionData
import DiophCompression.ArityZeroFragments
import DiophCompression.FunctionPhaseByArity
import DiophCompression.FunctionPhaseByArityNN
import DiophCompression.RelationPhaseAllPositiveArityClassical
import DiophCompression.APALStructuralTheoryCore
import DiophCompression.SummitClosure
import DiophCompression.GSCompilerComputable
import DiophCompression.SummitInstances
import MPUP.Quantitative
import MPUP.WeightedBound
import DiophCompression.SemanticQuadraticSingular.SingularAssembly
import DiophCompression.SemanticQuadraticSingular.QuadraticUniversalityCorollaries
import DiophCompression.SemanticQuadraticSingular.CorollariesAllR
import DiophCompression.QuadraticUniversalityConditional
#print axioms DiophCompression.SemanticQuadraticSingular.quadraticProjectionDichotomyZ_all
#print axioms DiophCompression.SemanticQuadraticSingular.quadraticWitnessInertiaZ
#print axioms DiophCompression.SemanticQuadraticSingular.graphAchievableZ_degree_two_iff
#print axioms DiophCompression.SemanticQuadraticSingular.universalCapacityZ_degree_two_le_three
#print axioms DiophCompression.SemanticQuadraticSingular.no_four_parameter_quadratic_universality
#print axioms DiophCompression.capBound_degree_two
#print axioms DiophCompression.quadratic_syntactic_semantic_gap
#print axioms DiophCompression.quadratic_gap_exact
#print axioms DiophCompression.quadratic_graph_degree_lower_bound
#print axioms DiophCompression.quadratic_graph_arity_inertia
#print axioms DiophCompression.withinZ_degree_two_is_decidable
#print axioms DiophCompression.withinN_degree_two_is_decidable
#print axioms DiophCompression.not_universalAchievableZ_one_degree_two
#print axioms DiophCompression.not_universalAchievableN_one_degree_two
#print axioms DiophCompression.universalCapacityZ_degree_two_eq_zero
#print axioms DiophCompression.universalCapacityN_degree_two_eq_zero
-- APAL Logic Pivot Gate 1 (s19): Theorems A / B / C headline declarations
#print axioms DiophCompression.atomGraph_degree_zero_iff
#print axioms DiophCompression.atomGraph_degree_one_iff
#print axioms DiophCompression.atomGraph_degree_two_iff
#print axioms DiophCompression.atomGraph_degree_three_ternary
#print axioms DiophCompression.atomGraph_degree_four_all
#print axioms DiophCompression.codingDegree_three_exact
#print axioms DiophCompression.codingDegree_ge_three_le_four
#print axioms DiophCompression.ppQuadratic_graph_all_arity
#print axioms DiophCompression.atom_two_implies_pp_quadratic
#print axioms DiophCompression.pp_quadratic_implies_single_quartic
#print axioms DiophCompression.single_quadratic_strict_pp_quadratic
#print axioms DiophCompression.ternarySkolem_atomicRank_three_zero
#print axioms DiophCompression.ternarySkolem_atomicRank_two_top
-- APAL Logic Pivot Gate 2 (s20): Theorem F (folding) and the degree-2 decision of its hypothesis
#print axioms DiophCompression.ppWitnessRankZ_eq_top_iff
#print axioms DiophCompression.ppWitnessRankZ_le_coe_iff
#print axioms DiophCompression.ppWitnessRankZ_le_atomicDegreeRankZ
#print axioms DiophCompression.preimageRel_imageRel
#print axioms DiophCompression.ppWitnessRankZ_preimage_le
#print axioms DiophCompression.ppWitnessRankZ_image_le
#print axioms DiophCompression.ppArityRankZ_fold
#print axioms DiophCompression.ternaryPair_ppWitnessRankZ_le_one
#print axioms DiophCompression.ppArityRankZ_two_three_le
#print axioms DiophCompression.ppArityRankZ_two_finite_transfer
#print axioms DiophCompression.atomicDegreeRankZ_ternary_two_top
#print axioms DiophCompression.atomicDegreeRankZ_preimage_le
-- APAL Logic Pivot Gate 3 (s20): one-sorted version (all variables in Z)
#print axioms DiophCompression.evalAtZZ_natCast
#print axioms DiophCompression.atomGraphZZ_degree_two_le_two
#print axioms DiophCompression.one_sorted_quadratic_no_injective_ternary_graph
#print axioms DiophCompression.atomGraphZZ_degree_one_one
#print axioms DiophCompression.zToNat_injective
#print axioms DiophCompression.zToNat_nonneg
#print axioms DiophCompression.ternaryPairZZ_injective
#print axioms DiophCompression.ppGraphZZ_degree_two_three
-- APAL r20 Gate 2 (s22): all-arity pp-quadratic coding over Z via eta(x) = 2x^2 - x
#print axioms DiophCompression.intToNatPoly_nonneg
#print axioms DiophCompression.intToNatPoly_injective
#print axioms DiophCompression.pairZ_inj
#print axioms DiophCompression.intTupleCode_injective
#print axioms DiophCompression.ppGraphZZ_step
#print axioms DiophCompression.intTupleCode_system
#print axioms DiophCompression.ppGraphZZ_degree_two_all
-- APAL r20 Gates 1+3 (s22): one-sorted fragments SE_d(k) / PP_d(k) and the chain SE_2 ⊊ PP_2 ⊆ SE_4 at k ≥ 4
#print axioms DiophCompression.withinSingleEquationZZ_iff
#print axioms DiophCompression.withinPPZZ_iff
#print axioms DiophCompression.atomGraphZZ_iff_within
#print axioms DiophCompression.ppGraphZZ_iff_within
#print axioms DiophCompression.singleEqFragmentZZ_subset_ppFragmentZZ
#print axioms DiophCompression.withinSingleEquationZZ_double_of_withinPPZZ
#print axioms DiophCompression.ppZZ_degree_two_subset_singleEquationZZ_degree_four
#print axioms DiophCompression.graphZZ_intTupleCode_withinPPZZ
#print axioms DiophCompression.graphZZ_not_withinSingleEquationZZ_two
#print axioms DiophCompression.pp_not_single_quadratic_at_arity
#print axioms DiophCompression.quadratic_fragment_strict_at_arity
#print axioms DiophCompression.quadratic_fragment_chain
-- APAL r20 Gate 4 (s22): pp arity folding over Z along intTupleCode
#print axioms DiophCompression.preimageRelZZ_imageRelZZ
#print axioms DiophCompression.withinPPZZ_preimage_of_systems
#print axioms DiophCompression.withinPPZZ_image_of_systems
#print axioms DiophCompression.withinPPZZ_preimage_intTupleCode
#print axioms DiophCompression.withinPPZZ_image_intTupleCode
#print axioms DiophCompression.pp_quadratic_internal_arity_collapse
#print axioms DiophCompression.ppFragmentZZ_two_arity_collapse
-- APAL r20 Gate 5 (s22): bundled core
#print axioms DiophCompression.apal_logic_core
-- Appendix C (s22): universal-pair obstruction layer (MPUP namespace) and its binomial form
#print axioms MPUP.coder_counting_bound
#print axioms MPUP.not_tupleCoderZ
#print axioms MPUP.not_tupleCoderN
#print axioms MPUP.multiUniversalZ_bound
#print axioms MPUP.multiUniversalN_bound
#print axioms MPUP.not_MPUP_Z_of_bound
#print axioms MPUP.not_MPUP_N_of_bound
#print axioms MPUP.multiUniversalN_degree_one
-- s34 Gate-8 F01/F02: the weighted counting obstruction of Appendix C.  Until s34 these
-- roots were outside this report; the module is now registered in full (19 theorems).
#print axioms MPUP.wtCount_le_crude
#print axioms MPUP.wtCount_mono
#print axioms MPUP.aux_arith_weighted
#print axioms MPUP.pval_efac
#print axioms MPUP.deg_finset_sum
#print axioms MPUP.aux_kappa_bound_weighted
#print axioms MPUP.aux_coeff_bound_weighted
#print axioms MPUP.aux_coeff_nat_weighted
#print axioms MPUP.aux_counting_weighted
#print axioms MPUP.coder_counting_bound_weighted
#print axioms MPUP.multiUniversalN_bound_weighted
#print axioms MPUP.multiUniversalZ_bound_weighted
#print axioms MPUP.not_MPUP_N_of_weighted_bound
#print axioms MPUP.monoCount_widen
#print axioms MPUP.monoCount_succ_right
#print axioms MPUP.monoCount_closed_form
#print axioms MPUP.wtCount_eq_sum_monoCount
#print axioms MPUP.wtCount_closed_form
#print axioms MPUP.not_MPUP_Z_of_weighted_bound
#print axioms DiophCompression.multiUniversalN_capBound
#print axioms DiophCompression.multiUniversalZ_capBound
-- APAL Functional-Definability Pivot, Gate 6 (s23): finite-fiber growth + definable functions
#print axioms DiophCompression.singleQuadratic_finiteFiber_height_scalar
#print axioms DiophCompression.singleQuadratic_finiteFiber_height_scalar_sup
#print axioms DiophCompression.singleQuadratic_finiteFiber_height_vector
#print axioms DiophCompression.singleQuadratic_function_quadratic_growth
#print axioms DiophCompression.singleQuadratic_injective_dimension_bound
#print axioms DiophCompression.atomGraphZZ_le_two_from_dimension_bound
-- APAL Functional-Definability Pivot, Gate 7 (s23): polynomial graphs, arity-2 separation, composition failure
#print axioms DiophCompression.polynomial_graph_singleQuadratic_of_degree_le
#print axioms DiophCompression.polynomial_graph_one_not_singleQuadratic
#print axioms DiophCompression.polynomial_graph_one_singleQuadratic_iff
#print axioms DiophCompression.powerGraph_not_withinSingleEquationZZ
#print axioms DiophCompression.cubic_graph_withinPPZZ
#print axioms DiophCompression.cubic_graph_not_withinSingleEquationZZ
#print axioms DiophCompression.quadratic_fragment_strict_arity_two
#print axioms DiophCompression.quadratic_fragment_strict_all_arity_ge_two
#print axioms DiophCompression.square_graph_singleQuadratic
#print axioms DiophCompression.fourth_power_graph_not_singleQuadratic
#print axioms DiophCompression.fourth_power_graph_ppQuadratic
#print axioms DiophCompression.singleQuadratic_functions_not_closed_under_composition
-- APAL Functional-Definability Pivot, Gate 8 (s23): Skolem reduction PP_2 = Dioph
#print axioms DiophCompression.skolemComputable_all
#print axioms DiophCompression.withinDiophZZ_of_withinPPZZ
#print axioms DiophCompression.withinPPZZ_two_of_withinDiophZZ
#print axioms DiophCompression.withinPPZZ_two_iff_withinDiophZZ
#print axioms DiophCompression.ppFragmentZZ_two_eq_diophFragmentZZ
#print axioms DiophCompression.ncard_le_of_abs_le
#print axioms DiophCompression.ncard_le_of_abs_le_vec
#print axioms DiophCompression.fiberCardBound_of_fiberHeightBound
#print axioms DiophCompression.fiberCardBoundVec_of_fiberHeightBoundVec
#print axioms DiophCompression.singleQuadratic_finiteFiber_cardinality_scalar
#print axioms DiophCompression.singleQuadratic_finiteFiber_cardinality_vector
#print axioms DiophCompression.singleQuadratic_finiteFiber_cardinality_scalar_sup
#print axioms DiophCompression.singleQuadratic_finiteFiber_cardinality_vector_sup
#print axioms DiophCompression.singleQuadraticFiniteValuedRelation_bounds
#print axioms DiophCompression.fiberVecZZ_eq_singleton_of_represents
#print axioms DiophCompression.singleQuadraticDefinableFunction_finiteValued
#print axioms DiophCompression.withinDiophZZ_of_withinSingleEquationZZ
#print axioms DiophCompression.singleEqFragmentZZ_subset_diophFragmentZZ
#print axioms DiophCompression.singleEqFragmentZZ_four_eq_ppFragmentZZ_two
#print axioms DiophCompression.singleEqFragmentZZ_four_eq_diophFragmentZZ
#print axioms DiophCompression.fragment_lattice_ZZ
#print axioms DiophCompression.eval_mul_of_isHomogeneous
#print axioms DiophCompression.topHomogeneous_ne_zero
#print axioms DiophCompression.exists_eval_ne_zero
#print axioms DiophCompression.linePoly_eval
#print axioms DiophCompression.linePoly_coeff
#print axioms DiophCompression.linePoly_natDegree
#print axioms DiophCompression.exists_line_natDegree_eq_totalDegree
#print axioms DiophCompression.polynomial_graph_not_singleQuadratic_of_degree_ge_three
#print axioms DiophCompression.polynomial_graph_singleQuadratic_iff
#print axioms DiophCompression.primrec₂_int_add
#print axioms DiophCompression.primrec₂_int_mul
#print axioms DiophCompression.primrec_eval_of_coords
#print axioms DiophCompression.computable_eval_of_coords
#print axioms DiophCompression.primrec_int_pow
#print axioms DiophCompression.computable_eval_mvPolynomial
#print axioms DiophCompression.primrec_evalAtZZ
#print axioms DiophCompression.primrecPred_evalAtZZ_eq_zero
#print axioms DiophCompression.primrec₂_solCheck
#print axioms DiophCompression.exists_solCheck_iff
#print axioms DiophCompression.rePred_exists_solCheck
#print axioms DiophCompression.powerGraphZZ_computablePred
#print axioms DiophCompression.dioph_relation_re
#print axioms DiophCompression.ppQuadratic_relation_re
#print axioms DiophCompression.ppRelation_re
#print axioms DiophCompression.singleEquation_relation_re
#print axioms DiophCompression.singleQuartic_relation_re
#print axioms DiophCompression.recFragmentZZ_subset_reFragmentZZ
#print axioms DiophCompression.singleQuadratic_relation_recursive
#print axioms DiophCompression.singleEqFragmentZZ_two_subset_recFragmentZZ
#print axioms DiophCompression.ppQuadratic_eq_re_of_DPRM
#print axioms DiophCompression.singleQuartic_eq_re_of_DPRM
#print axioms DiophCompression.relation_phase_diagram
#print axioms DiophCompression.computable_of_withinDiophZZ_graph
#print axioms DiophCompression.computablePred_graphVecZZ
#print axioms DiophCompression.compSys_sol_iff
#print axioms DiophCompression.ppQuadratic_total_function_computable
#print axioms DiophCompression.singleQuadratic_total_function_computable
#print axioms DiophCompression.computable_total_function_ppQuadratic_of_DPRM
#print axioms DiophCompression.ppQuadratic_functions_eq_totalComputable_of_DPRM
#print axioms DiophCompression.ppQuadratic_functions_eq_singleQuartic
#print axioms DiophCompression.ppQuadratic_functions_closed_under_composition
#print axioms DiophCompression.singleQuadratic_functions_proper_subset_totalComputable
#print axioms DiophCompression.function_phase_diagram
#print axioms DiophCompression.haltingRelZZ_re
#print axioms DiophCompression.haltingRelZZ_not_computablePred
#print axioms DiophCompression.recursive_strictly_contained_re
#print axioms DiophCompression.relation_phase_diagram_strict
#print axioms DiophCompression.decodePolyZZ_totalDegree_le_two
#print axioms DiophCompression.decodePolyZZ_surjective
#print axioms DiophCompression.quadraticSolvabilityDecidable_of_uniform
#print axioms DiophCompression.diagonalSetZZ_computablePred
#print axioms DiophCompression.diagonalSetZZ_not_singleQuadratic
#print axioms DiophCompression.singleQuadratic_strict_recursive_all_positive_arity
#print axioms DiophCompression.unary_singleQuadratic_strict_recursive
#print axioms DiophCompression.relation_phase_diagram_all_positive_arity
#print axioms DiophCompression.apal_structural_theory_core
-- s26 Gate 3 必須D-1/D-3 (ArityZeroFragments)
#print axioms DiophCompression.relation_phase_diagram_arity_zero
#print axioms DiophCompression.relation_phase_diagram_unary
#print axioms DiophCompression.relation_phase_diagram_arity_ge_two
-- s26 Gate 3 必須E (FunctionPhaseByArity)
#print axioms DiophCompression.singleQuadratic_functions_strict_of_pos_arity
#print axioms DiophCompression.singleQuadratic_functions_eq_at_zero_input
#print axioms DiophCompression.singleQuadratic_functions_eq_at_zero_output
#print axioms DiophCompression.function_phase_diagram_by_arity
-- s40 Gate-14 P09 (FunctionPhaseByArityNN): Theorem 7.1 under DPRM_NN directly
#print axioms DiophCompression.function_phase_diagram_by_arity_of_DPRM_NN
-- s41 Gate-15 F02 (RelationPhaseAllPositiveArityClassical): Theorem 6.8 under the two literature hypotheses directly
#print axioms DiophCompression.relation_phase_diagram_all_positive_arity_of_classical
-- s26 Gate 3 必須C (APALStructuralTheoryCore split)
#print axioms DiophCompression.apal_structural_core_unconditional
#print axioms DiophCompression.apal_structural_core_of_uniformGS
#print axioms DiophCompression.apal_structural_core_of_perEquationGS
#print axioms DiophCompression.apal_structural_core_of_DPRM
#print axioms DiophCompression.apal_full_phase_diagram
-- s26 Gate 3 必須A (QuadraticCodes)
#print axioms DiophCompression.quadraticCode_eval_primrec
#print axioms DiophCompression.quadraticCode_toPoly_totalDegree_le_two
#print axioms DiophCompression.quadraticCode_toPoly_eval
#print axioms DiophCompression.quadraticCode_surjective
#print axioms DiophCompression.decodePolyZZ_eq_codeOfNat
#print axioms DiophCompression.decodePolyZZ_natOfCode
#print axioms DiophCompression.uniformCodeGS_iff
#print axioms DiophCompression.uniformCodeGS_implies_perEquationGS
-- s26 Gate 3 宿題群2 (EffectiveDiagonal)
#print axioms DiophCompression.effDiagonal_computablePred
#print axioms DiophCompression.effDiagonal_not_mem
#print axioms DiophCompression.coded_family_ssubset_rec
#print axioms DiophCompression.singleQuadratic_strict_recursive_of_codes
-- s26 Gate 3 必須B (DPRMTransport)
#print axioms DiophCompression.rePred_diffPreimage
#print axioms DiophCompression.transportWitnessArity_eq
#print axioms DiophCompression.transportPoly_eval_eq_zero_iff
#print axioms DiophCompression.DPRM_ZZ_of_DPRM_NN
-- s27 Gate 4 必須D (transport degree resource)
#print axioms DiophCompression.transportPoly_totalDegree_le
#print axioms DiophCompression.dprmTransport_resource_bound
-- s27 Gate 4 必須B (GlobalQuadraticCode)
#print axioms DiophCompression.fixedArityCode_matches_QuadraticCode
#print axioms DiophCompression.fixedArityInstance_parameterArity
#print axioms DiophCompression.globalGS_implies_fixedArityGS
#print axioms DiophCompression.globalGS_implies_uniformGS
#print axioms DiophCompression.globalGS_implies_perEquationGS
-- s26 Gate 3 必須B corollaries (APALStructuralTheoryCore)
#print axioms DiophCompression.apal_structural_core_of_DPRM_NN
#print axioms DiophCompression.apal_full_phase_diagram_classical
#print axioms DiophCompression.apal_full_phase_diagram_literature
-- s27 Gate 4 必須E (StructuredCertificates + data form of the B2 step)
#print axioms DiophCompression.SemanticQuadraticSingular.moving_modulus_prime_step_data
#print axioms DiophCompression.PellUnitOrbitRealization.orbit_norm
#print axioms DiophCompression.MovingModulusStepOrbitSG.c_strictMono
#print axioms DiophCompression.movingModulusStepOrbitSG_of_base_zero
#print axioms DiophCompression.MovingModulusStepOrbitRealization.output_injective
#print axioms DiophCompression.fiber_infinite_of_structuredCertificate
#print axioms DiophCompression.boundedOrStructured_exclusive
#print axioms DiophCompression.finite_or_infinite_of_boundedOrStructured
#print axioms DiophCompression.StructuredCertificate.pullback_kind
#print axioms DiophCompression.polynomialProgression_of_periodic_shift
-- s26 Gate 3 必須F kernel layer (InfiniteFiberCertificate)
#print axioms DiophCompression.fiber_infinite_of_certificate
#print axioms DiophCompression.fiber_unbounded_of_certificate
#print axioms DiophCompression.certificate_pullback
#print axioms DiophCompression.primeProgression_index_infinite
#print axioms DiophCompression.StepFamilyRealization.point_strictMono
#print axioms DiophCompression.fiber_infinite_of_typedCertificate
#print axioms DiophCompression.boundedOrCertified_exclusive
#print axioms DiophCompression.finite_or_infinite_of_boundedOrCertified
-- s28 Gate 5 必須A (branch B4 = witness reflection, not output reflection)
#print axioms DiophCompression.SemanticQuadraticSingular.movingModulus_negSlope_witnessEquiv
#print axioms DiophCompression.SemanticQuadraticSingular.fiberSetSG_negSlope
#print axioms DiophCompression.SemanticQuadraticSingular.movingModulus_negSlope_dvd_transfer
#print axioms DiophCompression.SemanticQuadraticSingular.movingModulus_negSlope_strictMono_transfer
#print axioms DiophCompression.movingModulusStepOrbitSG_of_negSlope
#print axioms DiophCompression.extract_B4_movingStep_spec
-- s28 Gate 5 必須G (DPRM final representation resource bound)
#print axioms DiophCompression.transportedRepresentation_totalDegree_le
#print axioms DiophCompression.DPRM_ZZ_resource_bound_final
-- s28 Gate 5 必須C (output-negation transport; distinct from the B4 witness reflection)
#print axioms DiophCompression.evalAtZZ_negOutputPoly
#print axioms DiophCompression.mem_fiberZZ_negOutputPoly
#print axioms DiophCompression.fiberZZ_negOutputPoly
#print axioms DiophCompression.mem_fiberZZ_negOutputPoly_neg
#print axioms DiophCompression.StructuredCertificate.negOutput_kind
#print axioms DiophCompression.negOutputPoly_transport
#print axioms DiophCompression.structuredCertificate_of_flipZero_kind
#print axioms DiophCompression.infinite_integer_set_pos_or_neg
#print axioms DiophCompression.infinite_integer_fiber_pos_or_neg
-- s28 Gate 5 必須D (leaf extraction packagers)
#print axioms DiophCompression.injective_of_lt_succ_from
#print axioms DiophCompression.linearFamilyPoly_eval
#print axioms DiophCompression.extract_linear_family_q
#print axioms DiophCompression.quadraticFamilyPoly_eval
#print axioms DiophCompression.extract_periodic
#print axioms DiophCompression.extract_A3_periodic
#print axioms DiophCompression.extract_B1_fixed_periodic
#print axioms DiophCompression.pellFamily_coords_pos
#print axioms DiophCompression.pellFamily_X_strictMono
#print axioms DiophCompression.extract_B0_polynomial_kind
#print axioms DiophCompression.extract_A2_polynomial_kind
#print axioms DiophCompression.extract_A1_pell_kind
-- s28 Gate 5 必須B (strong summit target; the r25 predicate demoted to a corollary)
#print axioms DiophCompression.uniform_bound_certificate_exclusive
#print axioms DiophCompression.uniformQuadraticFiberStructureZZ_implies_boundedOrStructured
#print axioms DiophCompression.uniformQuadraticFiberStructureZZ_implies_finiteFiberHeight
#print axioms DiophCompression.uniformQuadraticFiberStructureZZ_implies_boundedOrInfinite
#print axioms DiophCompression.negOutputPoly_solution_transport
#print axioms DiophCompression.uniformQuadraticFiberStructureZZ_negOutputPoly
#print axioms DiophCompression.uniformQuadraticFiberStructureZZ_negOutputPoly_kind
-- s28 Gate 5 必須E (branch table as a kernel object; exhaustion of the three dispatch levels)
#print axioms DiophCompression.branch_kind_iff_not_bounded
#print axioms DiophCompression.no_unclassified_quadratic_branch
#print axioms DiophCompression.branch_table_partition
#print axioms DiophCompression.fullRank_structured_cases
#print axioms DiophCompression.fullRank_branch_kinds
#print axioms DiophCompression.singular_structured_cases
#print axioms DiophCompression.oneWitness_structured_cases
#print axioms DiophCompression.oneWitness_branch_kinds
#print axioms DiophCompression.singular_branch_kinds
-- s28 Gate 5 必須G (GS input compiler: our coding -> the classical coefficient-table input)
#print axioms DiophCompression.splitFactor_spec
#print axioms DiophCompression.substParamTerm_evalW
#print axioms DiophCompression.substParamCode_evalW
#print axioms DiophCompression.toConcreteEquation_witnessArity
#print axioms DiophCompression.globalInstance_eval_iff
#print axioms DiophCompression.globalInstance_solvable_iff
#print axioms DiophCompression.toConcreteEquation_parameterFree
#print axioms DiophCompression.rational_clearing_int_points
-- s28 Gate 5 必須F step 1 (the summit reduces to the infinite-side certificate supply)
#print axioms DiophCompression.uniformQuadraticFiberStructureZZ_of_infiniteFiberStructured
#print axioms DiophCompression.infiniteFiberStructured_of_uniformQuadraticFiberStructureZZ
#print axioms DiophCompression.uniformQuadraticFiberStructureZZ_iff_infiniteFiberStructured
#print axioms DiophCompression.infiniteFiberStructured_of_nonneg_halves
#print axioms DiophCompression.uniformQuadraticFiberStructureZZ_of_nonneg_halves
#print axioms DiophCompression.weak_target_trivial_on_finite_fibre
-- s28 Gate 5 必須F step 2 pilot (leaves D3, D4, D6 re-proved in data-carrying form)
#print axioms DiophCompression.SemanticQuadratic.linearFamily_nonempty
#print axioms DiophCompression.SemanticQuadratic.fiberSet_infinite_of_linearFamily
#print axioms DiophCompression.SemanticQuadratic.dichotomy_of_dichotomyLinearData
#print axioms DiophCompression.SemanticQuadratic.dichotomy_degenerate_C_zero_data
#print axioms DiophCompression.SemanticQuadratic.dichotomy_square_C_zero_data
#print axioms DiophCompression.SemanticQuadratic.dichotomy_square_C_ne_data
#print axioms DiophCompression.SemanticQuadratic.dichotomy_degenerate_C_zero_of_data
#print axioms DiophCompression.SemanticQuadratic.dichotomy_square_C_zero_of_data
#print axioms DiophCompression.SemanticQuadratic.dichotomy_square_C_ne_of_data
-- s28 Gate 5 必須F step 2 (periodic family pattern in data form; branch B1b demonstrated)
#print axioms DiophCompression.infinite_of_periodicProgression
#print axioms DiophCompression.periodicProgression_or_empty
#print axioms DiophCompression.periodic_infinite_or_empty_of_data
#print axioms DiophCompression.SemanticQuadraticTwoWitness.rank_one_uncoupled_periodic_data
-- s28 Gate 5 必須F step 2 (periodic leaves A3, B3 in data form)
#print axioms DiophCompression.SemanticQuadraticMatrix.alpha_zero_beta_zero_periodic_data
#print axioms DiophCompression.SemanticQuadraticSingular.dichotomySG_zero_periodic_data
-- s28 Gate 5 必須F step 2 (Pell orbit arithmetic core, shared by leaves A1 and D7)
#print axioms DiophCompression.pellOrbit_norm
#print axioms DiophCompression.pellOrbit_pos
#print axioms DiophCompression.pellOrbit_strictMono_fst
#print axioms DiophCompression.pellOrbit_congr
#print axioms DiophCompression.pellOrbit_unbounded_fst
-- s28 Gate 5 必須F step 2 (Pell orbit output layer: integrality and growth of the affine projection)
#print axioms DiophCompression.pellOrbit_output_dvd
#print axioms DiophCompression.pellOrbit_output_strictMono
#print axioms DiophCompression.pellOrbit_output
-- s28 Gate 5 必須F step 2 (leaf D7: every stage of the Pell orbit is a fibre point)
#print axioms DiophCompression.SemanticQuadratic.pell_fiber_orbit_mem
-- s28 Gate 5 必須F step 2 (Pell orbit: sign symmetry, so one sign choice at the base suffices)
#print axioms DiophCompression.pellOrbit_neg_snd
#print axioms DiophCompression.pellOrbit_strictMono_fst_neg
-- s28 Gate 5 必須F step 2 (the Pell hub in data form: serves leaves A1, D7 and the rank-two block)
#print axioms DiophCompression.SemanticQuadratic.pell_orbit_of_X_pos
-- s28 Gate 5 必須F step 2 (leaf B1c: the coupled rank-one prime step in data form)
#print axioms DiophCompression.SemanticQuadraticTwoWitness.rank_one_coupled_prime_step_data
-- s28 Gate 5 必須F step 2 (leaves D2 and A2: the quadratic families, in packager shape)
#print axioms DiophCompression.SemanticQuadratic.d2_quadratic_family
#print axioms DiophCompression.SemanticQuadratic.d2_leading_ne_zero
#print axioms DiophCompression.SemanticQuadratic.d2_family_growth
#print axioms DiophCompression.SemanticQuadraticMatrix.a2_quadratic_family
#print axioms DiophCompression.SemanticQuadraticMatrix.a2_leading_pos
#print axioms DiophCompression.SemanticQuadraticMatrix.a2_leading_ne_zero
#print axioms DiophCompression.SemanticQuadraticMatrix.a2_family_growth
-- s28 Gate 5 必須F step 3 (leaf certificate type for the one-witness normal form; soundness)
#print axioms DiophCompression.SemanticQuadratic.fiberSet_infinite_of_oneWitnessFamilyData
-- s28 Gate 5 必須F step 3 (one-witness aggregation at data level; D2/D7 wrappers isolated)
#print axioms DiophCompression.SemanticQuadratic.dichotomy_of_dichotomyOneWitnessData
#print axioms DiophCompression.SemanticQuadratic.dichotomyOneWitnessData_of_linear
#print axioms DiophCompression.SemanticQuadratic.dichotomy_definite_data
#print axioms DiophCompression.SemanticQuadratic.fiber_dichotomy_data
#print axioms DiophCompression.SemanticQuadratic.fiber_dichotomy_of_data
-- s28 Gate 5 必須F step 3 (leaf D7 wrapper in data form; the hub replaces the step iteration)
#print axioms DiophCompression.SemanticQuadratic.dichotomy_pell_data
-- s28 Gate 5 必須F step 3 (leaf D2 wrapper; the one-witness layer becomes unconditional in data form)
#print axioms DiophCompression.SemanticQuadratic.dichotomy_degenerate_C_ne_data
#print axioms DiophCompression.SemanticQuadratic.fiber_dichotomy_data_full
#print axioms DiophCompression.SemanticQuadratic.fiber_dichotomy_of_data_full
-- s28 Gate 5 必須F step 3 (set-generic family type for the assembly layers)
#print axioms DiophCompression.infinite_of_structuredFamily
-- s28 Gate 5 必須F step 3 (rank-one uncoupled layer in data form; pure transport)
#print axioms DiophCompression.SemanticQuadraticTwoWitness.dichotomy2_of_dichotomy2Data
#print axioms DiophCompression.SemanticQuadraticTwoWitness.rank_one_uncoupled_data
#print axioms DiophCompression.SemanticQuadraticTwoWitness.rank_one_uncoupled_of_data
-- s28 Gate 5 必須F step 3 (rank-one normal form in data form: B1a transport, B1c orbit, assembly)
#print axioms DiophCompression.SemanticQuadraticTwoWitness.dichotomy2Data_of_unimodular
#print axioms DiophCompression.SemanticQuadraticTwoWitness.b1c_orbit
#print axioms DiophCompression.SemanticQuadraticTwoWitness.rank_one_coupled_pos_data
#print axioms DiophCompression.SemanticQuadraticTwoWitness.dichotomy2_rank_one_normal_data
#print axioms DiophCompression.SemanticQuadraticTwoWitness.dichotomy2_rank_one_data
#print axioms DiophCompression.SemanticQuadraticTwoWitness.dichotomy2_rank_one_normal_of_data
#print axioms DiophCompression.SemanticQuadraticTwoWitness.dichotomy2_rank_one_of_data
-- s28 Gate 5 必須F step 3 (matrix-level data dichotomy; full-rank dispatch with the three leaves exposed)
#print axioms DiophCompression.SemanticQuadraticMatrix.dichotomyM_of_dichotomyMData
#print axioms DiophCompression.SemanticQuadraticMatrix.alpha_zero_beta_zero_family_data
#print axioms DiophCompression.SemanticQuadraticMatrix.full_rank_dichotomy_all_data
#print axioms DiophCompression.SemanticQuadraticMatrix.full_rank_root_bound_data
#print axioms DiophCompression.SemanticQuadraticMatrix.full_rank_alpha_zero_dichotomy_data
#print axioms DiophCompression.SemanticQuadraticMatrix.full_rank_dichotomy_all_data_of_dir
-- s28 Gate 5 必須F step 3 (A1 line family; full-rank block unconditional in data form)
#print axioms DiophCompression.SemanticQuadraticMatrix.fiberSetM_line_family
#print axioms DiophCompression.SemanticQuadraticMatrix.full_rank_dichotomy_of_direction_data
#print axioms DiophCompression.SemanticQuadraticMatrix.full_rank_dichotomy_all_data_full
#print axioms DiophCompression.SemanticQuadraticMatrix.full_rank_dichotomy_all_of_data
-- s28 Gate 5 必須F step 3 (singular block: data dichotomy and the b = 0 reduction)
#print axioms DiophCompression.SemanticQuadraticSingular.dichotomySG_of_dichotomySGData
-- s28 Gate 5 必須F step 3 (singular block: the rank-one quotient in data form)
-- s28 Gate 5 必須F step 3 (singular block: k₀ ≥ 2 dispatch at the data level)
#print axioms DiophCompression.SemanticQuadraticSingular.quotient_rank_ge_two_moving_dichotomy_data
#print axioms DiophCompression.SemanticQuadraticSingular.sg_pos_orbit
#print axioms DiophCompression.SemanticQuadraticSingular.dichotomySG_pos_data
#print axioms DiophCompression.SemanticQuadraticSingular.aux_dichotomySG_neg_data
#print axioms DiophCompression.SemanticQuadraticSingular.dichotomySG_zero_data
#print axioms DiophCompression.SemanticQuadraticSingular.dichotomyMData_of_dichotomySGData_zero
#print axioms DiophCompression.SemanticQuadraticSingular.quotient_rank_one_coupled_dichotomy_data
#print axioms DiophCompression.SemanticQuadraticSingular.quotient_rank_one_dichotomy_data
#print axioms DiophCompression.SemanticQuadraticSingular.dichotomyMData_of_unimodular
-- s28 Gate 5 必須F step 3 (singular assembly at the data level; k₀=0 leaf is the only hypothesis)
#print axioms DiophCompression.SemanticQuadraticSingular.singular_projection_dichotomy_all_r_data
-- s28 Gate 5 必須F step 3 MILESTONE: k₀=0 leaf, singular block unconditional, and the TOP
#print axioms DiophCompression.SemanticQuadraticSingular.quotient_rank_zero_dichotomy_data
#print axioms DiophCompression.SemanticQuadraticSingular.singular_projection_dichotomy_all_r_data_full
#print axioms DiophCompression.SemanticQuadraticGeneral.dichotomyG_of_dichotomyGData
#print axioms DiophCompression.SemanticQuadraticGeneral.quadraticProjectionDichotomyZ_all_data
#print axioms DiophCompression.SemanticQuadraticGeneral.quadraticProjectionDichotomyZ_all_of_data

-- s29 Gate 5 必須F steps 3-4: THE SUMMIT (homogenisation bridge + family->certificate + closure)
#print axioms DiophCompression.exists_fiberSetG_eq_fiberNatSigned
-- (structuredCertificate_of_family is a `def`; its footprint is subsumed by the theorem below)
#print axioms DiophCompression.structuredCertificate_of_half_infinite
#print axioms DiophCompression.infiniteFiberStructured_of_quadratic
#print axioms DiophCompression.uniformQuadraticFiberStructureZZ_of_quadratic
#print axioms DiophCompression.quadraticFiberBoundedOrStructured_of_quadratic
#print axioms DiophCompression.quadraticProjectionDichotomyZ_structured
#print axioms DiophCompression.singleQuadratic_fiber_bounded_or_structurallyInfinite
-- s29 必須G last item / 宿題群7-5: the GS input compiler is primitive recursive
#print axioms DiophCompression.primrec₂_splitFactor
#print axioms DiophCompression.primrec₂_substParamTerm
#print axioms DiophCompression.primrec₂_substParamCode
#print axioms DiophCompression.globalGS_input_compiler_computable
#print axioms DiophCompression.globalGS_input_compiler_comp
-- s29 Gate-5 homework instances: B4 sign edge cases, half overlap, the five fibre shapes, branch control
#print axioms DiophCompression.b4_edge_neg_one_zero
#print axioms DiophCompression.b4_edge_neg_b_pos_mu
#print axioms DiophCompression.b4_edge_neg_b_neg_mu
#print axioms DiophCompression.halves_inter
#print axioms DiophCompression.fibre_empty
#print axioms DiophCompression.fibre_univ
#print axioms DiophCompression.fibre_zero_only
#print axioms DiophCompression.fibre_two_points
#print axioms DiophCompression.fibre_neg_only
#print axioms DiophCompression.kindOmitB2_breaks_partition
