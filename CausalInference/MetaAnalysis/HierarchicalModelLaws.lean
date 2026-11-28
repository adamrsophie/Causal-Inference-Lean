/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.Exchangeable

/-!
# The random effects model as a hierarchical law without a hyperparameter

The library's `hierarchicalLaw n hyper pop samp` is the law of the units `(θᵢ, yᵢ)` of a two
level hierarchical model. Without a hyperparameter (the one point space `Unit` with the point
mass as hyperprior) it is the **random effects model** of a meta-analysis: the unit parameters
are i.i.d. from the population law `pop`, and given them the data are independent from the
sampling kernel. Then:

* `hierarchicalLaw_unit`: the units are i.i.d. from `pop ⊗ samp`;
* `map_fst_hierarchicalLaw_unit`: the unit parameters are i.i.d. from `pop`;
* `map_snd_hierarchicalLaw_unit`: the data are i.i.d. from the predictive law `samp ∘ pop`, the
  mixture of the sampling laws over the population law.

The fixed effects law with unit parameters `θⱼ`, the product `Measure.pi fun j => samp (θ j)`,
needs no definition of its own.

## Main results

* `hierarchicalLaw_unit`, `map_fst_hierarchicalLaw_unit`, `map_snd_hierarchicalLaw_unit`.

## References

* A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari and D. B. Rubin, *Bayesian Data
  Analysis*, third edition (2013).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory

variable {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]

/-- **Without a hyperparameter the units are i.i.d.**: the hierarchical law with the point mass
on `Unit` as hyperprior is the product of `pop ⊗ samp`. -/
theorem hierarchicalLaw_unit (n : ℕ) (pop : Measure Θ) (samp : Kernel Θ Y) :
    hierarchicalLaw n (Measure.dirac ()) (fun _ => pop) samp =
      Measure.pi fun _ : Fin n => pop ⊗ₘ samp :=
  Measure.dirac_bind measurable_const _

/-- **The unit parameters of the random effects model are i.i.d. from the population law.** -/
theorem map_fst_hierarchicalLaw_unit (n : ℕ) (pop : Measure Θ) [IsProbabilityMeasure pop]
    (samp : Kernel Θ Y) [IsMarkovKernel samp] :
    (hierarchicalLaw n (Measure.dirac ()) (fun _ => pop) samp).map (fun u i => (u i).1) =
      Measure.pi fun _ : Fin n => pop := by
  rw [hierarchicalLaw_unit, Measure.pi_map_pi (fun _ => measurable_fst.aemeasurable)]
  congr 1
  funext i
  exact Measure.fst_compProd pop samp

/-- **The data of the random effects model are i.i.d. from the predictive law** `samp ∘ pop`. -/
theorem map_snd_hierarchicalLaw_unit (n : ℕ) (pop : Measure Θ) [IsProbabilityMeasure pop]
    (samp : Kernel Θ Y) [IsMarkovKernel samp] :
    (hierarchicalLaw n (Measure.dirac ()) (fun _ => pop) samp).map (fun u i => (u i).2) =
      Measure.pi fun _ : Fin n => samp ∘ₘ pop := by
  rw [hierarchicalLaw_unit, Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable)]
  congr 1
  funext i
  exact Measure.snd_compProd pop samp

end MetaAnalysis

end CausalInference
