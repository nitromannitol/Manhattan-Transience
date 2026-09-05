import Manhattan.Paper.Constant.Witnesses

/-!
# The paper's constant: axiom audit

The part's own `#print axioms` surface, kept inside
`Manhattan/Paper/Constant/` so that `Manhattan/Meta/AxiomsAudit.lean` is not
touched.  Every declaration below must report exactly
`[propext, Classical.choice, Quot.sound]`.
-/

#print axioms Manhattan.Paper.Constant.rpow_le_Zdelta_tight
#print axioms Manhattan.Paper.Constant.move3_bound_tight
#print axioms Manhattan.Paper.Constant.v4FrequencyBound_tight
#print axioms Manhattan.Paper.Constant.v4FrequencyBound_tight_proved
#print axioms Manhattan.Paper.Constant.uniform_green_numeral
#print axioms Manhattan.Paper.Constant.uniform_green_numeral_v4
#print axioms Manhattan.Paper.Constant.annealed_green_le_numeral
#print axioms Manhattan.Paper.Constant.frequencyConstant_gt
#print axioms Manhattan.Paper.Constant.frequencyConstant_lt
#print axioms Manhattan.Paper.Constant.move3_rhs_strict
#print axioms Manhattan.Paper.Constant.green_constant_gt_paper
