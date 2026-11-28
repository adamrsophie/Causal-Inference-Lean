/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedBootstrapLimit
public import CausalInference.Estimation.DeltaMethod

/-!
# Order in conditional probability, in probability

A bootstrap statistic depends on the data `ω` and on the resample `y`. A family of properties
`p n ω y` of the resamples holds **with conditional probability tending to one, in probability**
when, for every `κ > 0`, eventually `P(P*_ω(not p) ≥ κ) ≤ κ`, where `P*_ω = resampleLaw O n ω` is
the resampling law given the data (`ResampleEventually`). The two small and bounded orders of
this mode are `ResampleTendstoZero` (`X = o_{P*}(1)` in probability) and `ResampleBounded`
(`X = O_{P*}(1)` in probability). The resampling probabilities of sets that need not be measurable
are outer probabilities, so no measurability is needed anywhere.

The calculus is the usual one: sums of small terms are small, a small term times a bounded term
is small, small terms are bounded, and a term dominated by a small (bounded) term is small
(bounded). Properties of the data alone (probability tending to one under `P`) are properties
of this kind. A bootstrap remainder that is small in this sense makes the statistic bootstrap
linear (`isBootstrapLinear_of_resampleTendstoZero`).

## Main definitions

* `ResampleLikely P O p κ`: eventually `P(P*_ω(not p) ≥ κ) ≤ κ`.
* `ResampleEventually P O p`: `ResampleLikely P O p κ` for every `κ > 0`.
* `ResampleTendstoZero P O X`: `|X| < ε` with conditional probability tending to one, for every
  `ε > 0`.
* `ResampleBounded P O X`: for every `κ > 0` there is `K` with `ResampleLikely P O (|X| ≤ K) κ`.

## Main results

* `ResampleTendstoZero.add`, `.mul_bounded`, `.of_le`, `.sum`, `ResampleBounded.add`, `.mul`.
* `ResampleTendstoZero.of_tendstoInMeasure`, `ResampleBounded.of_data`: properties of the data.
* `isBootstrapLinear_of_resampleTendstoZero`.

## References

* P. J. Bickel and D. A. Freedman (1981), *Some asymptotic theory for the bootstrap*, Annals of
  Statistics 9.
* A. W. van der Vaart (1998), *Asymptotic Statistics*, Cambridge University Press, chapter 23.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open Bootstrap

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪] {P : Measure Ω}
  {O : ℕ → Ω → 𝒪}

/-- **Resample properties at level `κ`**: eventually in `n`, the data `ω` at which the
resampling probability of `not p` is at least `κ` have probability at most `κ`. -/
def ResampleLikely (P : Measure Ω) (O : ℕ → Ω → 𝒪)
    (p : (n : ℕ) → Ω → (Fin n → 𝒪) → Prop) (κ : ℝ) : Prop :=
  ∀ᶠ n in atTop, P {ω | κ ≤ (resampleLaw O n ω).real {y | ¬ p n ω y}} ≤ ENNReal.ofReal κ

/-- **Resample properties with conditional probability tending to one, in probability**:
`ResampleLikely P O p κ` for every `κ > 0`. -/
def ResampleEventually (P : Measure Ω) (O : ℕ → Ω → 𝒪)
    (p : (n : ℕ) → Ω → (Fin n → 𝒪) → Prop) : Prop :=
  ∀ κ : ℝ, 0 < κ → ResampleLikely P O p κ

/-- **Small in conditional probability, in probability**: for every `ε > 0`, `|X| < ε` with
conditional probability tending to one, in probability. -/
def ResampleTendstoZero (P : Measure Ω) (O : ℕ → Ω → 𝒪)
    (X : (n : ℕ) → Ω → (Fin n → 𝒪) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ResampleEventually P O fun n ω y => |X n ω y| < ε

/-- **Bounded in conditional probability, in probability**: for every `κ > 0` there is a bound
`K` with `ResampleLikely P O (|X| ≤ K) κ`. -/
def ResampleBounded (P : Measure Ω) (O : ℕ → Ω → 𝒪)
    (X : (n : ℕ) → Ω → (Fin n → 𝒪) → ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ K : ℝ, ResampleLikely P O (fun n ω y => |X n ω y| ≤ K) κ

variable {p q : (n : ℕ) → Ω → (Fin n → 𝒪) → Prop} {κ κ' : ℝ}

/-! ### Levels -/

theorem ResampleLikely.mono (h : ResampleLikely P O p κ) (hpq : ∀ n ω y, p n ω y → q n ω y)
    (hκ : κ ≤ κ') : ResampleLikely P O q κ' := by
  filter_upwards [h] with n hn
  refine (measure_mono fun ω hω => ?_).trans (hn.trans (ENNReal.ofReal_le_ofReal hκ))
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have : (resampleLaw O n ω).real {y | ¬ q n ω y} ≤ (resampleLaw O n ω).real {y | ¬ p n ω y} :=
    measureReal_mono fun y hy hp => hy (hpq n ω y hp)
  linarith

theorem ResampleLikely.and (h₁ : ResampleLikely P O p κ) (h₂ : ResampleLikely P O q κ')
    (hκ : 0 ≤ κ) (hκ' : 0 ≤ κ') :
    ResampleLikely P O (fun n ω y => p n ω y ∧ q n ω y) (κ + κ') := by
  filter_upwards [h₁, h₂] with n hn₁ hn₂
  refine (measure_mono fun ω hω => ?_).trans ((measure_union_le _ _).trans
    ((add_le_add hn₁ hn₂).trans (ENNReal.ofReal_add hκ hκ').symm.le))
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
  by_contra hc
  push Not at hc
  have hsub : {y | ¬ (p n ω y ∧ q n ω y)} ⊆ {y | ¬ p n ω y} ∪ {y | ¬ q n ω y} := by
    intro y hy
    simp only [Set.mem_ofPred_eq, not_and_or, Set.mem_union] at hy ⊢
    exact hy
  have := (measureReal_mono (μ := resampleLaw O n ω) hsub).trans (measureReal_union_le _ _)
  linarith [hc.1, hc.2]

/-! ### Conditional probability tending to one -/

theorem ResampleEventually.mono (h : ResampleEventually P O p)
    (hpq : ∀ n ω y, p n ω y → q n ω y) : ResampleEventually P O q :=
  fun κ hκ => (h κ hκ).mono hpq le_rfl

theorem ResampleEventually.and (h₁ : ResampleEventually P O p) (h₂ : ResampleEventually P O q) :
    ResampleEventually P O fun n ω y => p n ω y ∧ q n ω y := fun κ hκ => by
  have := (h₁ (κ / 2) (by positivity)).and (h₂ (κ / 2) (by positivity)) (by positivity)
    (by positivity)
  rwa [add_halves] at this

/-- A property holding at every resample for all large `n` holds with conditional probability
tending to one. -/
theorem ResampleEventually.of_eventually (h : ∀ᶠ n in atTop, ∀ ω y, p n ω y) :
    ResampleEventually P O p := fun κ hκ => by
  filter_upwards [h] with n hn
  have : {ω | κ ≤ (resampleLaw O n ω).real {y | ¬ p n ω y}} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
    have : {y | ¬ p n ω y} = ∅ := by
      ext y; simp [hn ω y]
    rw [this, measureReal_empty]
    exact hκ
  rw [this, measure_empty]
  exact bot_le

/-- **Properties of the data**: events of probability tending to one under `P` hold with
conditional probability tending to one. -/
theorem ResampleEventually.of_withProbTendingToOne {A : ℕ → Set Ω}
    (h : WithProbTendingToOne P A) : ResampleEventually P O fun n ω _ => ω ∈ A n := fun κ hκ => by
  filter_upwards [h.eventually_le (ENNReal.ofReal_pos.2 hκ)] with n hn
  refine (measure_mono fun ω hω => ?_).trans hn
  intro hωA
  simp only [Set.mem_ofPred_eq] at hω
  have : {y : Fin n → 𝒪 | ¬ ω ∈ A n} = ∅ := by
    ext y; simp [hωA]
  rw [this, measureReal_empty] at hω
  linarith

/-- Finite conjunctions. -/
theorem ResampleEventually.finset_forall {ι : Type*} (s : Finset ι)
    {p : ι → (n : ℕ) → Ω → (Fin n → 𝒪) → Prop} (h : ∀ i ∈ s, ResampleEventually P O (p i)) :
    ResampleEventually P O fun n ω y => ∀ i ∈ s, p i n ω y := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ResampleEventually.of_eventually (Eventually.of_forall fun _ _ _ i hi =>
      absurd hi (Finset.notMem_empty i))
  | insert a s ha ih =>
    refine ((h a (Finset.mem_insert_self a s)).and
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).mono fun n ω y hy i hi => ?_
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hy.1
    · exact hy.2 i hi

theorem ResampleEventually.forall_finite {ι : Type*} [Finite ι]
    {p : ι → (n : ℕ) → Ω → (Fin n → 𝒪) → Prop} (h : ∀ i, ResampleEventually P O (p i)) :
    ResampleEventually P O fun n ω y => ∀ i, p i n ω y := by
  have := Fintype.ofFinite ι
  exact (ResampleEventually.finset_forall Finset.univ fun i _ => h i).mono fun _ _ _ hy i =>
    hy i (Finset.mem_univ i)

/-! ### Small and bounded terms -/

variable {X Y : (n : ℕ) → Ω → (Fin n → 𝒪) → ℝ}

theorem ResampleTendstoZero.of_le (hY : ResampleTendstoZero P O Y)
    (hle : ResampleEventually P O fun n ω y => |X n ω y| ≤ |Y n ω y|) :
    ResampleTendstoZero P O X := fun ε hε =>
  ((hY ε hε).and hle).mono fun _ _ _ h => lt_of_le_of_lt h.2 h.1

theorem ResampleBounded.of_le (hY : ResampleBounded P O Y)
    (hle : ResampleEventually P O fun n ω y => |X n ω y| ≤ |Y n ω y|) :
    ResampleBounded P O X := fun κ hκ => by
  obtain ⟨K, hK⟩ := hY (κ / 2) (by positivity)
  refine ⟨K, ?_⟩
  have := hK.and (hle (κ / 2) (by positivity)) (by positivity) (by positivity)
  rw [add_halves] at this
  exact this.mono (fun _ _ _ h => h.2.trans h.1) le_rfl

theorem ResampleTendstoZero.add (hX : ResampleTendstoZero P O X)
    (hY : ResampleTendstoZero P O Y) :
    ResampleTendstoZero P O fun n ω y => X n ω y + Y n ω y := fun ε hε =>
  ((hX (ε / 2) (by positivity)).and (hY (ε / 2) (by positivity))).mono fun _ _ _ h =>
    lt_of_le_of_lt (abs_add_le _ _) (by linarith [h.1, h.2])

theorem ResampleTendstoZero.neg (hX : ResampleTendstoZero P O X) :
    ResampleTendstoZero P O fun n ω y => -X n ω y := fun ε hε =>
  (hX ε hε).mono fun _ _ _ h => by rwa [abs_neg]

theorem ResampleTendstoZero.sub (hX : ResampleTendstoZero P O X)
    (hY : ResampleTendstoZero P O Y) :
    ResampleTendstoZero P O fun n ω y => X n ω y - Y n ω y := by
  simpa only [sub_eq_add_neg] using hX.add hY.neg

theorem ResampleTendstoZero.const_mul (hX : ResampleTendstoZero P O X) (c : ℝ) :
    ResampleTendstoZero P O fun n ω y => c * X n ω y := fun ε hε =>
  (hX (ε / (|c| + 1)) (by positivity)).mono fun n ω y h => by
    rw [abs_mul]
    have h1 : |c| * |X n ω y| ≤ (|c| + 1) * |X n ω y| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    have h2 : (|c| + 1) * |X n ω y| < ε := by
      rwa [lt_div_iff₀ (by positivity), mul_comm] at h
    linarith

theorem resampleTendstoZero_zero : ResampleTendstoZero P O fun _ _ _ => 0 := fun _ hε =>
  ResampleEventually.of_eventually (Eventually.of_forall fun _ _ _ => by simpa using hε)

theorem ResampleTendstoZero.sum {ι : Type*} (s : Finset ι)
    {X : ι → (n : ℕ) → Ω → (Fin n → 𝒪) → ℝ} (h : ∀ i ∈ s, ResampleTendstoZero P O (X i)) :
    ResampleTendstoZero P O fun n ω y => ∑ i ∈ s, X i n ω y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (resampleTendstoZero_zero (P := P) (O := O))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem ResampleTendstoZero.bounded (hX : ResampleTendstoZero P O X) :
    ResampleBounded P O X := fun κ hκ =>
  ⟨1, (hX 1 one_pos κ hκ).mono (fun _ _ _ h => h.le) le_rfl⟩

theorem resampleBounded_const (c : ℝ) : ResampleBounded P O fun _ _ _ => c := fun κ hκ =>
  ⟨|c|, ResampleEventually.of_eventually (Eventually.of_forall fun _ _ _ => le_rfl) κ hκ⟩

theorem ResampleBounded.add (hX : ResampleBounded P O X) (hY : ResampleBounded P O Y) :
    ResampleBounded P O fun n ω y => X n ω y + Y n ω y := fun κ hκ => by
  obtain ⟨K₁, h₁⟩ := hX (κ / 2) (by positivity)
  obtain ⟨K₂, h₂⟩ := hY (κ / 2) (by positivity)
  refine ⟨K₁ + K₂, ?_⟩
  have := h₁.and h₂ (by positivity) (by positivity)
  rw [add_halves] at this
  exact this.mono (fun _ _ _ h => (abs_add_le _ _).trans (add_le_add h.1 h.2)) le_rfl

theorem ResampleBounded.mul (hX : ResampleBounded P O X) (hY : ResampleBounded P O Y) :
    ResampleBounded P O fun n ω y => X n ω y * Y n ω y := fun κ hκ => by
  obtain ⟨K₁, h₁⟩ := hX (κ / 2) (by positivity)
  obtain ⟨K₂, h₂⟩ := hY (κ / 2) (by positivity)
  refine ⟨K₁ * K₂, ?_⟩
  have := h₁.and h₂ (by positivity) (by positivity)
  rw [add_halves] at this
  refine this.mono (fun _ _ _ h => ?_) le_rfl
  rw [abs_mul]
  exact mul_le_mul h.1 h.2 (abs_nonneg _) ((abs_nonneg _).trans h.1)

theorem ResampleBounded.const_mul (hX : ResampleBounded P O X) (c : ℝ) :
    ResampleBounded P O fun n ω y => c * X n ω y :=
  (resampleBounded_const c).mul hX

theorem ResampleBounded.neg (hX : ResampleBounded P O X) :
    ResampleBounded P O fun n ω y => -X n ω y :=
  hX.of_le (ResampleEventually.of_eventually (Eventually.of_forall fun _ _ _ => by
    rw [abs_neg]))

theorem ResampleBounded.sub (hX : ResampleBounded P O X) (hY : ResampleBounded P O Y) :
    ResampleBounded P O fun n ω y => X n ω y - Y n ω y := by
  simpa only [sub_eq_add_neg] using hX.add hY.neg

theorem ResampleBounded.sum {ι : Type*} (s : Finset ι)
    {X : ι → (n : ℕ) → Ω → (Fin n → 𝒪) → ℝ} (h : ∀ i ∈ s, ResampleBounded P O (X i)) :
    ResampleBounded P O fun n ω y => ∑ i ∈ s, X i n ω y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (resampleBounded_const (P := P) (O := O) 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **A small term times a bounded term is small.** -/
theorem ResampleTendstoZero.mul_bounded (hX : ResampleTendstoZero P O X)
    (hY : ResampleBounded P O Y) :
    ResampleTendstoZero P O fun n ω y => X n ω y * Y n ω y := fun ε hε κ hκ => by
  obtain ⟨K, hK⟩ := hY (κ / 2) (by positivity)
  have := (hX (ε / (|K| + 1)) (by positivity) (κ / 2) (by positivity)).and hK (by positivity)
    (by positivity)
  rw [add_halves] at this
  refine this.mono (fun n ω y h => ?_) le_rfl
  obtain ⟨h1, h2⟩ := h
  rw [abs_mul]
  have h3 : |Y n ω y| ≤ |K| + 1 := h2.trans ((le_abs_self K).trans (by linarith))
  have h4 : |X n ω y| * (|K| + 1) < ε := by rwa [lt_div_iff₀ (by positivity)] at h1
  calc |X n ω y| * |Y n ω y| ≤ |X n ω y| * (|K| + 1) :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    _ < ε := h4

theorem ResampleBounded.mul_tendstoZero (hX : ResampleBounded P O X)
    (hY : ResampleTendstoZero P O Y) :
    ResampleTendstoZero P O fun n ω y => X n ω y * Y n ω y := by
  simpa only [mul_comm] using hY.mul_bounded hX

/-! ### Properties of the data -/

/-- **Convergence in probability of the data** gives a small term. -/
theorem ResampleTendstoZero.of_tendstoInMeasure {f : ℕ → Ω → ℝ} {c : ℝ}
    (h : TendstoInMeasure P f atTop (fun _ => c)) :
    ResampleTendstoZero P O fun n ω _ => f n ω - c := fun ε hε =>
  (ResampleEventually.of_withProbTendingToOne (h.withProbTendingToOne_dist_lt hε)).mono
    fun _ _ _ hy => by simpa [Real.dist_eq] using hy

/-- **Boundedness in probability of the data** gives a bounded term. -/
theorem ResampleBounded.of_data {f : ℕ → Ω → ℝ}
    (h : ∀ η : ℝ≥0∞, 0 < η → ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop, P {ω | M ≤ |f n ω|} ≤ η) :
    ResampleBounded P O fun n ω _ => f n ω := fun κ hκ => by
  obtain ⟨M, -, hM⟩ := h (ENNReal.ofReal κ) (ENNReal.ofReal_pos.2 hκ)
  refine ⟨M, ?_⟩
  filter_upwards [hM] with n hn
  refine (measure_mono fun ω hω => ?_).trans hn
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra hc
  have : {y : Fin n → 𝒪 | ¬ |f n ω| ≤ M} = ∅ := by
    ext y; simp [(not_le.1 hc).le]
  rw [this, measureReal_empty] at hω
  linarith

/-! ### Bootstrap linearity -/

/-- **A small bootstrap remainder gives bootstrap linearity.** -/
theorem isBootstrapLinear_of_resampleTendstoZero {T : (n : ℕ) → (Fin n → 𝒪) → ℝ}
    {ψ : 𝒪 → ℝ} (h : ResampleTendstoZero P O fun n ω y => bootstrapRemainder T ψ O n ω y) :
    IsBootstrapLinear P O T ψ := by
  intro ρ hρ
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨κ, hκ, hκε, hκη⟩ : ∃ κ : ℝ, 0 < κ ∧ κ ≤ ε ∧ ENNReal.ofReal κ ≤ η := by
    rcases eq_or_ne η ⊤ with rfl | hηt
    · exact ⟨ε, hε, le_rfl, le_top⟩
    refine ⟨min ε η.toReal, lt_min hε (ENNReal.toReal_pos hη.ne' hηt), min_le_left _ _, ?_⟩
    exact (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans (ENNReal.ofReal_toReal_le)
  filter_upwards [h ρ hρ κ hκ] with n hn
  refine (measure_mono fun ω hω => ?_).trans (hn.trans hκη)
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, not_lt] at hω ⊢
  rw [abs_of_nonneg measureReal_nonneg] at hω
  linarith

end PopulationAdjustment

end CausalInference
