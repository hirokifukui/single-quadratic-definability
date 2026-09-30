# Appendix F — line-by-line Lean correspondence (artifact companion to the PDF appendix)

All in `DiophCompression/SemanticQuadraticMatrix/` except `Directions.lean` and `PellStep.lean`, which are in the sibling directory `DiophCompression/SemanticQuadraticTwoWitness/`; every named theorem prints axioms [propext, Classical.choice, Quot.sound].

|§ here|claim|Lean anchor|file : lines \\|
|---|---|---|---|
|0|data, W̃, α, β, γ, line|`fqM`, `fiberSetM`, `completedVector`, `adjugateQuad`, `alphaMatrix`, `betaMatrix`, `gammaMatrix`, `scaledLineU`|DefsMatrix.lean : 17–58|
|0|statement|`DichotomyM`, `fboundM`, `full_rank_projection_dichotomy_of_direction_property`|FullRankGeneric.lean : 27–34, 708–712|
|1|identity (1.1)|`general_rank_identity`|AdjugateIdentity.lean : 87–116|
|2|integrality $N·ℤ^{r} ⊆ G·ℤ^{r}$|`witnessGram_mulVec_adjugate`|AdjugateIdentity.lean : 45–48|
|2|lattice transport (2.2)|`general_scaled_line_preserves_lattice`|AdjugateIdentity.lean : 118–129|
|2|line value (2.3)|`general_scaled_line_identity`, `general_scaled_line_fq`|AdjugateIdentity.lean : 131–140; FullRankGeneric.lean : 158–170|
|2|line zero ⇒ fiber element|`general_scaled_line_solution`|AdjugateIdentity.lean : 142–151|
|3|c₀ ≤ |β| under α·Z₀ ≤ 0|`full_rank_dichotomy_of_direction`, bounded branch (h1–h3)|FullRankGeneric.lean : 268–285|
|3, 9||β|, |γ| size|`betaMatrix_abs_le`, `gammaMatrix_abs_le`, `fboundM_core_ge_lin`, `fboundM_core_ge_gamma`|FullRankGeneric.lean : 79–136|
|4 (i)–(ii)|disc positive non-square|`disc` computation + `not_isSquare_sq_mul`|FullRankGeneric.lean : 193–200; Directions.lean : 34|
|4 (iii)–(iv)|initial point, X₀ > 0|`fiberSetM_infinite_of_line`, hmem0/hX0|FullRankGeneric.lean : 201–218|
|4 (v)|Pell orbit infinite|`pell_infinite_of_X_pos`|PellStep.lean : 11|
|4 (vi)|transport, injectivity, residue|`fiberSetM_infinite_of_line`, hinj/hline/hmem|FullRankGeneric.lean : 219–246|
|5|per-point dichotomy, α ≠ 0|`full_rank_dichotomy_of_direction`|FullRankGeneric.lean : 248–289|
|6a|shift periodicity|`alpha_zero_beta_zero_periodic_M`, `periodic_infinite_or_empty`|FullRankGeneric.lean : 291–322; TwoWitness layer|
|6b|progression unboundedness|`full_rank_alpha_zero_dichotomy`, progression branch + `fiberSetM_infinite_of_unbounded`|FullRankGeneric.lean : 344–392, 138–153|
|6c|c ≤ |γ||`full_rank_alpha_zero_dichotomy`, bounded branch|FullRankGeneric.lean : 393–422|
|7|root bound|`full_rank_root_bound`|FullRankGeneric.lean : 424–478|
|8a|anisotropy|`eq_zero_of_adjugateQuad_eq_zero`|FullRankGeneric.lean : 511–558|
|8b|sign attained|`exists_adjugateQuad_sign`|FullRankGeneric.lean : 560–575|
|8c|indefinite direction|`indefinite_signed_nonsquare_direction_M`; leaves `split_signed_nonsquare_direction`, `anisotropic_signed_nonsquare_direction`|FullRankGeneric.lean : 490–509; Directions.lean : 199, 125|
|8d|definite direction|`definite_signed_nonsquare_direction_M`; leaf `definite_nonsquare_direction`|FullRankGeneric.lean : 578–638; Directions.lean : 69|
|8e|assembly grid|`full_rank_dichotomy_all`|FullRankGeneric.lean : 640–706|
|2, 8|plane restriction algebra|`adjugateQuad_smul_add_smul`, `adjugateQuad_add_smul`|FullRankGeneric.lean : 480–488; AdjugateIdentity.lean : 80–86|
