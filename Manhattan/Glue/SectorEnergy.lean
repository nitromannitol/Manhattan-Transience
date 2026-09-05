import Manhattan.Glue.FinalDischarge
import Manhattan.Glue.SummandThreeMixedBound
import Manhattan.Glue.SummandFourAssembly

/-!
# Equation (23) for the concrete competitor, and Proposition 2.2

`Manhattan/Glue/Discharge.lean` reduces the whole formalization to the single
named statement `Manhattan.Glue.ConcreteSectorEnergyBound M`, the paper's
estimate `E_p(f_p,k_p) ≤ C √L` for the four-sector form
`manuscript.tex:769-772` (eq:E = (22)) at the concrete competitor of
`Glue/Correction.lean`; the estimate itself is the third display of
`eq:construction` at `manuscript.tex:785-790`.
`Manhattan/Glue/Summands.lean` splits that statement into the four summands of
the objective and composes them again (`concreteSectorEnergyBound_of_four`).

All four summand bounds are now proved:

* `Manhattan.Glue.summandOneBound_proved` (`Glue/Summands.lean`), `⟨f,H₁f⟩`;
* `Manhattan.Glue.summandTwoBound_proved` (`Glue/SummandsMixed.lean`),
  `⟨k,H₃k⟩`;
* `Manhattan.Glue.summandThreeBound_proved`
  (`Glue/SummandThreeMixedBound.lean`), `‖D₁f-D₂^*k‖²_{-1}`;
* `Manhattan.Glue.summandFourBound_proved`
  (`Glue/SummandFourAssembly.lean`), `‖D₃k‖²_{-1}`.

This file composes them, so equation (23) holds unconditionally
(`exists_concreteSectorEnergyBound`), and reads off Proposition 2.2
(`prop:frequency`, `manuscript.tex:644-661`) through the provider
`proposition_frequency_v2_of_exists` of `Glue/FinalDischarge.lean`.

The two headline conclusions, `Manhattan.AnnealedGreenBound` (Theorem 1.2) and
the quenched finiteness of the Green series (Theorem 1.1), are the frozen
anchors themselves; their bodies apply
`Manhattan.Glue.theorem_1_2_proved_of_exists` and
`Manhattan.Glue.theorem_1_1_proved_of_exists` to
`exists_concreteSectorEnergyBound` directly.
-/

noncomputable section

namespace Manhattan.Glue

/-- **Equation (23), unconditionally.** The four summands of the objective
`eq:E = (22)` at the concrete competitor, each bounded by its own module, add up
to `M √L`. This is the last hypothesis the discharge chain of
`Glue/Discharge.lean` was waiting for. -/
theorem exists_concreteSectorEnergyBound :
    ∃ M : ℝ, 0 ≤ M ∧ ConcreteSectorEnergyBound M := by
  obtain ⟨C₁, hC₁, h1⟩ := summandOneBound_proved
  obtain ⟨C₂, hC₂, h2⟩ := summandTwoBound_proved
  obtain ⟨C₃, hC₃, h3⟩ := summandThreeBound_proved
  obtain ⟨C₄, hC₄, h4⟩ := summandFourBound_proved
  exact ⟨C₁ + C₂ + C₃ + C₄, by linarith,
    concreteSectorEnergyBound_of_four hC₁ h1 h2 h3 h4⟩

/-- **Proposition 2.2** (`prop:frequency`, `manuscript.tex:644-661`), version
2, unconditionally. -/
theorem proposition_frequency_v2 : PropositionFrequencyClaim :=
  proposition_frequency_v2_of_exists exists_concreteSectorEnergyBound

end Manhattan.Glue
