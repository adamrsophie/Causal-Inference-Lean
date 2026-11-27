/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Designs.Randomized.Complete
public import CausalInference.Interference.TwoStage

/-!
# Randomized designs and allocation strategies

The design-based framework of `CausalInference.Randomized` describes an assignment law by a
`Design` (a finite summation set with weights), while the interference files describe it by an
`AllocationStrategy` (a weight on every assignment vector). This file converts between the two
and shows that the conversions preserve expectations and treatment probabilities, that complete
randomization is the same law on both sides, and that without interference the
assignment-indexed outcomes are the observed outcomes of classical potential outcomes. Source:
M. G. Hudgens and M. E. Halloran (2008), Toward causal inference with interference, Journal of
the American Statistical Association 103; Imbens and Rubin (2015), *Causal Inference for
Statistics, Social, and Biomedical Sciences*.

## Main definitions

All declarations live in the namespace `CausalInference.Interference`, except
`Randomized.Design.toAllocationStrategy`, which lives in `CausalInference.Randomized`.

* `AllocationStrategy.toDesign`: an allocation strategy as a design supported on every
  assignment.
* `Randomized.Design.toAllocationStrategy`: a design as an allocation strategy, by zero
  extension of its weights outside the support.
* `toPO`: the classical potential outcomes `(y1 Y, y0 Y)` of assignment-indexed outcomes.

## Main results

* `expect_eq_toDesign_expect`, `treatProb_true_eq_toDesign_inclusionProb`: the conversion to a
  design preserves expectations and treatment probabilities.
* `expect_toAllocationStrategy`, `toAllocationStrategy_treatProb_true`: the same for the
  converse conversion.
* `completeRandomization_prob_eq_mass`, `completeRandomization_toDesign_expect`: complete
  randomization assigns every assignment the same probability on both sides, so all
  expectations agree.
* `NoInterference.eq_toPO_observed`: without interference, `Y a i` is the observed outcome
  of unit `i` under `a` for the classical potential outcomes `toPO Y`.
-/

@[expose] public section

namespace CausalInference.Interference

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An allocation strategy as a randomized design: every assignment is in the summation set and
carries its strategy probability as weight. -/
def AllocationStrategy.toDesign (ψ : AllocationStrategy ι) : Randomized.Design ι where
  support := univ
  weight := ψ.prob
  weight_nonneg := fun a _ => ψ.nonneg a
  sum_weight := ψ.sum_eq_one

/-- The design of an allocation strategy gives every assignment its strategy probability. -/
theorem AllocationStrategy.toDesign_mass (ψ : AllocationStrategy ι) (a : ι → Bool) :
    ψ.toDesign.mass a = ψ.prob a := by
  simp [Randomized.Design.mass, AllocationStrategy.toDesign]

/-- Expectations under an allocation strategy and under its design agree. -/
theorem expect_eq_toDesign_expect (ψ : AllocationStrategy ι) (f : (ι → Bool) → ℝ) :
    expect ψ f = ψ.toDesign.expect f := rfl

/-- The probability that unit `i` is treated under an allocation strategy is its inclusion
probability under the corresponding design. -/
theorem treatProb_true_eq_toDesign_inclusionProb (ψ : AllocationStrategy ι) (i : ι) :
    ψ.treatProb i true = ψ.toDesign.inclusionProb i := by
  simp [AllocationStrategy.treatProb, Randomized.Design.inclusionProb,
    Randomized.Design.expect, AllocationStrategy.toDesign, Randomized.treatInd, sum_filter]

/-- A randomized design as an allocation strategy: the probability of an assignment is its
mass, that is, its weight on the support and `0` outside it. -/
noncomputable def _root_.CausalInference.Randomized.Design.toAllocationStrategy
    (d : Randomized.Design ι) : AllocationStrategy ι where
  prob := d.mass
  nonneg := d.mass_nonneg
  sum_eq_one := d.sum_mass

/-- Expectations under a design and under its allocation strategy agree. -/
theorem expect_toAllocationStrategy (d : Randomized.Design ι) (f : (ι → Bool) → ℝ) :
    expect d.toAllocationStrategy f = d.expect f :=
  (d.expect_eq_sum_mass f).symm

/-- The probability that unit `i` is treated under the allocation strategy of a design is its
inclusion probability under the design. -/
theorem toAllocationStrategy_treatProb_true (d : Randomized.Design ι) (i : ι) :
    d.toAllocationStrategy.treatProb i true = d.inclusionProb i := by
  rw [treatProb_true_eq_toDesign_inclusionProb, Randomized.Design.inclusionProb,
    Randomized.Design.inclusionProb, ← expect_eq_toDesign_expect, expect_toAllocationStrategy]

/-- **Complete randomization is the same law on both sides.** For `k ≤ N`, the allocation
strategy of complete randomization and the complete design give every assignment the same
probability. -/
theorem completeRandomization_prob_eq_mass {k : ℕ} (hk : k ≤ Fintype.card ι) (a : ι → Bool) :
    (completeRandomization ι k hk).prob a = (Randomized.completeDesign k hk).mass a := by
  have hcard : numVectors ι k = #(Randomized.completeSupport (ι := ι) k) := rfl
  simp only [completeRandomization, Randomized.completeDesign, Randomized.Design.mass,
    Randomized.Design.uniform, Randomized.mem_completeSupport, hcard]
  rfl

/-- Expectations under complete randomization agree on both sides. -/
theorem completeRandomization_toDesign_expect {k : ℕ} (hk : k ≤ Fintype.card ι)
    (f : (ι → Bool) → ℝ) :
    (completeRandomization ι k hk).toDesign.expect f =
      (Randomized.completeDesign k hk).expect f := by
  rw [Randomized.Design.expect_eq_sum_mass, Randomized.Design.expect_eq_sum_mass]
  simp only [AllocationStrategy.toDesign_mass, completeRandomization_prob_eq_mass]

/-- The classical potential outcomes of assignment-indexed outcomes `Y`: the outcome of each
unit when every unit is treated, and when no unit is treated. -/
def toPO (Y : (ι → Bool) → ι → ℝ) : Randomized.PotentialOutcomes ι := ⟨y1 Y, y0 Y⟩

omit [Fintype ι] [DecidableEq ι] in
/-- Without interference the outcome of unit `i` under the assignment vector `a` is the
observed outcome of `i` under `a` for the classical potential outcomes `toPO Y`. -/
theorem NoInterference.eq_toPO_observed {Y : (ι → Bool) → ι → ℝ} (h : NoInterference Y)
    (a : ι → Bool) (i : ι) : Y a i = (toPO Y).observed a i := by
  rw [h.eq_ite]
  rfl

end CausalInference.Interference
