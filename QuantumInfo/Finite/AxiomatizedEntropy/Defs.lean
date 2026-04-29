/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Dennj Osele
-/
module

public import QuantumInfo.ClassicalInfo.Entropy
public import QuantumInfo.Finite.MState
public import QuantumInfo.Finite.CPTPMap
public import QuantumInfo.Finite.POVM
public import QuantumInfo.Finite.Entropy.Relative

@[expose] public section

/-! # Generalized quantum entropy and relative entropy

Here we define a broad notion of entropy axiomatically, `Entropy`, and the Prop
`Entropy f` means that the function `f : MState → ℝ` acts like a generalized kind of quantum
entropy. For instance, min-, max-, α-Renyi, and von Neumann entropies all fall
into this category. We prove various properties about the entropy for anything
supporting this type class. Any entropy automatically gets corresponding notions
of conditional entropy, mutual information, and so on.

Similarly, `RelEntropy f` means that `f : MState → HermitianMat → ENNReal` is a kind of
relative entropy. Every `RelEntropy` leads to a notion of entropy, as well, by
fixing one argument to the fully mixed state.

Of course relative entropies are "usually" used with a pair of (normalized) quantum
states, but it's still very common in literature to specifically let the second
argument be an arbitrary (PSD, Hermitian) matrix, so we do allow this. The behavior
when not a density matrix is left unspecified by the axioms.

In terms of the file structure, we start with `RelEntropy` as the more "general"
function, and then derive much of `Entropy` from it.

## References:

 - [Khinchin’s Fourth Axiom of Entropy Revisited](https://www.mdpi.com/2571-905X/6/3/49)
 - [α-z Relative Entropies](https://warwick.ac.uk/fac/sci/maths/research/events/2013-2014/statmech/su/Nilanjana-slides.pdf)
 - Watrous's notes, [Max-relative entropy and conditional min-entropy](https://cs.uwaterloo.ca/~watrous/QIT-notes/QIT-notes.02.pdf)
 - [Quantum Relative Entropy - An Axiomatic Approach](https://www.marcotom.info/files/entropy-masterclass2022.pdf)
by Marco Tomamichel
 - [StackExchange](https://quantumcomputing.stackexchange.com/a/12953/10115)

-/

noncomputable section
universe u

open ComplexOrder
open scoped NNReal
open scoped ENNReal
open scoped Kronecker
open scoped HermitianMat

variable (f : ∀ {d : Type u} [Fintype d] [DecidableEq d], MState d → HermitianMat d ℂ → ℝ≥0∞)

/-- The axioms to be a well-behaved quantum relative entropy, as given by
[Tomamichel](https://www.marcotom.info/files/entropy-masterclass2022.pdf).

This simpler class allows for _trivial_ relative entropies, such as `-log tr(ρ⁰σ)`.
Use the mixin `RelEntropy.Nontrivial` to only allow nontrivial relative entropies. -/
class RelEntropy : Prop where
  /-- The data processing inequality -/
  DPI {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (ρ σ : MState d₁) (Λ : CPTPMap d₁ d₂) : f (Λ ρ) (Λ σ) ≤ f ρ σ
  /-- Entropy is additive under tensor products -/
  of_kron {d₁ d₂ : Type u} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂] :
    ∀ (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂), f (ρ₁ ⊗ᴹ ρ₂) (σ₁ ⊗ᴹ σ₂) = f ρ₁ σ₁ + f ρ₂ σ₂
  /-- Normalization of entropy to be `ln N` for a pure state vs. uniform on `N` many states. -/
  normalized {d : Type u} [fin : Fintype d] [DecidableEq d] [Nonempty d] (i : d) :
    f (.ofClassical (.constant i)) MState.uniform.M =
      some ⟨Real.log fin.card, Real.log_nonneg (mod_cast Fintype.card_pos)⟩

/-- Mixin on top of `RelEntropy` that rules out trivial relative entropies (those that vanish
on every pair of full-support states). See [Tomamichel](https://www.marcotom.info/files/entropy-masterclass2022.pdf). -/
class RelEntropy.Nontrivial [RelEntropy f] where
  /-- Nontriviality condition for a relative entropy: some pair of full-support states has
  positive relative entropy. This is the negation of Tomamichel's definition of a trivial
  relative entropy, which vanishes on all full-support state pairs. -/
  nontrivial : ∃ (d : Type u) (_ : Fintype d) (_ : DecidableEq d) (ρ σ : MState d),
    ρ.M.support = ⊤ ∧ σ.M.support = ⊤ ∧ 0 < f ρ σ

namespace RelEntropy

variable {d : Type u} [Fintype d] [DecidableEq d]
variable {d₂ : Type u} [Fintype d₂] [DecidableEq d₂]

variable [RelEntropy f]

section possibly_trivial

/-
At some point we might want to offer a different constructor so that `normalized` only checks
it for domains of size 2, which is sufficient (see Tomamichel's proof). In that case, the
fact that it's still zero when `Unique d` has to be proven, and this (now used) chunk of a proof
can be used in part for that:

-- have h_uniq (ρ') := (Subsingleton.allEq ρ ρ').symm
-- have h_kron := of_kron (f := f) ρ ρ ρ ρ
-- let e : d ≃ (d × d) := (Equiv.prodUnique d d).symm
-- rw [← relabel_eq f e] at h_kron
-- rw [h_uniq ((ρ⊗ρ).relabel e)] at h_kron
-- rw [h_uniq σ]

At that point we need the fact that it's not `⊤`, and then it must be zero.

-/

/-- Relabelling a state with `CPTPMap.ofEquiv` leaves relative entropies unchanged. -/
@[simp]
theorem ofEquiv_eq (e : d ≃ d₂) (ρ σ : MState d) :
    f (CPTPMap.ofEquiv e ρ) (CPTPMap.ofEquiv e σ) = f ρ σ := by
  apply le_antisymm
  · apply DPI
  · convert DPI (f := f) ((CPTPMap.ofEquiv e) ρ) ((CPTPMap.ofEquiv e) σ) (CPTPMap.ofEquiv e.symm)
    all_goals
      symm
      exact congrFun (CPTPMap.equiv_inverse e.symm) _

/-- Relabelling a state with `MState.relabel` leaves relative entropies unchanged. -/
@[simp]
theorem relabel_eq (e : d₂ ≃ d) (ρ σ : MState d) :
    f (ρ.relabel e) (σ.relabel e) = f ρ σ := by
  exact ofEquiv_eq (f := f) e.symm ρ σ

--Tomamichel's "4. Positivity" theorem is implicit true in our description because we
--only allow ENNReals. The only part to prove is that "D(ρ‖σ) = 0 if ρ = σ".

/-- The relative entropy is zero between any two states on a 1-D Hilbert space. -/
private lemma wrt_self_eq_zero' [Unique d] (ρ σ : MState d) : f ρ σ = 0 := by
  convert normalized (f := f) (d := d) default
  · exact Subsingleton.allEq _ _
  · exact Subsingleton.allEq _ _
  · simp [Fintype.card_unique, Real.log_one]
    rfl

/-- The relative entropy `D(ρ‖ρ) = 0`. -/
@[simp]
theorem wrt_self_eq_zero (ρ : MState d) : f ρ ρ.M = 0 := by
  rw [← nonpos_iff_eq_zero, ← wrt_self_eq_zero' f (d := PUnit) default default]
  convert DPI (f := f) _ _ (CPTPMap.replacement ρ)
  all_goals rw [CPTPMap.replacement_apply]

end possibly_trivial

section bounds

open Prob in
/-- Quantum relative min-entropy. -/
def min (ρ : MState d) (σ : HermitianMat d ℂ) : ENNReal :=
  —log ⟨ρ.exp_val (HermitianMat.projLE 0 σ),
    ρ.exp_val_prob ⟨HermitianMat.projLE_nonneg 0 σ, HermitianMat.projLE_le_one 0 σ⟩⟩

@[aesop (rule_sets := [finiteness]) simp]
theorem min_eq_top_iff (ρ : MState d) (σ : HermitianMat d ℂ) :
    (min ρ σ) = ⊤ ↔ ρ.M.support ≤ (HermitianMat.projLE 0 σ).ker := by
  rw [min, Prob.negLog_eq_top_iff]
  constructor
  · intro h
    have h0 : ρ.exp_val (HermitianMat.projLE 0 σ) = 0 := by
      simpa using congrArg (fun p : Prob => (p : ℝ)) h
    exact (ρ.exp_val_eq_zero_iff (HermitianMat.projLE_nonneg 0 σ)).mp h0
  · intro h
    exact Subtype.ext ((ρ.exp_val_eq_zero_iff (HermitianMat.projLE_nonneg 0 σ)).mpr h)

protected theorem toReal_min (ρ : MState d) (σ : HermitianMat d ℂ) :
    (min ρ σ).toReal = -Real.log (ρ.exp_val (HermitianMat.projLE 0 σ)) := by
  simp [min,
    Prob.negLog_pos_Real (p := ⟨ρ.exp_val (HermitianMat.projLE 0 σ),
      ρ.exp_val_prob ⟨HermitianMat.projLE_nonneg 0 σ, HermitianMat.projLE_le_one 0 σ⟩⟩)]


/-- On state inputs, the current support-based `min` quantity is always zero. -/
@[simp]
theorem min_state_eq_zero (ρ σ : MState d) : min ρ σ.M = 0 := by
  have hproj : HermitianMat.projLE 0 σ.M = 1 := by
    rw [HermitianMat.projLE_zero_cfc]
    calc σ.M.cfc (fun x ↦ if 0 ≤ x then 1 else 0) = σ.M.cfc (fun _ ↦ (1 : ℝ)) :=
          HermitianMat.cfc_congr_of_nonneg σ.nonneg fun _ hx => by simpa using hx
      _ = 1 := by simp [HermitianMat.cfc_const (A := σ.M) (r := (1 : ℝ))]
  simp [min, show (⟨ρ.exp_val (HermitianMat.projLE 0 σ.M),
    ρ.exp_val_prob ⟨HermitianMat.projLE_nonneg 0 σ.M, HermitianMat.projLE_le_one 0 σ.M⟩⟩ : Prob) = 1
    from Subtype.ext (by change ρ.exp_val _ = 1; rw [hproj, MState.exp_val_one])]

/-- The current support-based `min` quantity does not satisfy the normalization axiom of `RelEntropy`. -/
theorem not_RelEntropy_min : ¬ RelEntropy min := by
  intro hmin
  have := congrArg ENNReal.toReal (hmin.normalized (d := ULift (Fin 2)) (i := ⟨0⟩))
  simp at this; linarith [Real.log_pos one_lt_two]

theorem not_Nontrivial_min [RelEntropy min] : ¬Nontrivial min := by
  rintro ⟨h⟩
  obtain ⟨d, _, _, ρ, σ, -, -, hpos⟩ := h
  simp at hpos

omit [RelEntropy f] in
/-- The relative min-entropy is a lower bound on all relative entropies. -/
theorem min_le (ρ σ : MState d) : min ρ σ.M ≤ f ρ σ.M := by
  simp

open Classical in
/-- Quantum relative max-entropy. -/
def max (ρ : MState d) (σ : HermitianMat d ℂ) : ENNReal :=
  if ∃ (x : ℝ), ρ.M ≤ Real.exp x • σ then
    some (sInf { x : NNReal | ρ.M ≤ Real.exp x • σ })
  else
    ⊤

@[aesop (rule_sets := [finiteness]) simp]
protected theorem max_not_top (ρ : MState d) (σ : HermitianMat d ℂ) (hσ : 0 ≤ σ) :
    (max ρ σ) ≠ ⊤ ↔ σ.ker ≤ ρ.M.ker := by
  open ComplexOrder in
  constructor
  · intro h v hv
    by_cases hx : ∃ x : ℝ, ρ.M ≤ Real.exp x • σ
    · obtain ⟨x, hx⟩ := hx
      apply HermitianMat.mem_ker_of_inner_mulVec_zero ρ.nonneg v
      have hle := (HermitianMat.le_iff_mulVec_le_mulVec ρ.M (Real.exp x • σ)).mp hx v
      exact le_antisymm
        (by simpa [(HermitianMat.mem_ker_iff_mulVec_zero (A := σ) v).1 hv,
          Matrix.smul_mulVec, dotProduct_zero] using hle)
        (HermitianMat.inner_mulVec_nonneg ρ.nonneg v)
    · exact (h (by simp [max, hx])).elim
  · intro hker
    let P := σ.supportProj
    have hright : ρ.M.mat * P.mat = ρ.M.mat := by
      dsimp [P]; simpa using HermitianMat.mul_supportProj_of_ker_le (A := ρ.M) (B := σ) hker
    have hleft : P.mat * ρ.M.mat = ρ.M.mat := by
      simpa only [Matrix.conjTranspose_mul, HermitianMat.conjTranspose_mat] using
        congrArg Matrix.conjTranspose hright
    have hP_idem : P.mat * P.mat = P.mat := by
      have : P ^ 2 = P := by
        dsimp [P]; rw [HermitianMat.supportProj_eq_cfc, ← HermitianMat.cfc_pow,
          ← HermitianMat.cfc_comp_apply]
        exact HermitianMat.cfc_congr_of_nonneg hσ fun x _ => by by_cases hx : x = 0 <;> simp [hx]
      simpa [pow_two] using congrArg (fun A : HermitianMat d ℂ => A.mat) this
    have hρ_le_P : ρ.M ≤ P := calc
      ρ.M = ρ.M.conj P.mat := by
        symm; apply HermitianMat.ext
        simp only [HermitianMat.conj_apply_mat, HermitianMat.conjTranspose_mat,
          hright, hleft]
      _ ≤ (1 : HermitianMat d ℂ).conj P.mat := HermitianMat.conj_mono ρ.le_one
      _ = P := by apply HermitianMat.ext; simp [HermitianMat.conj_apply_mat, hP_idem]
    let α : ℝ := ∑ i, if σ.H.eigenvalues i = 0 then 0 else (σ.H.eigenvalues i)⁻¹
    have hterm : ∀ j, 0 ≤ if σ.H.eigenvalues j = 0 then 0 else (σ.H.eigenvalues j)⁻¹ :=
      fun j => by by_cases hj : σ.H.eigenvalues j = 0 <;>
        simp [hj, inv_nonneg.mpr (HermitianMat.eigenvalues_nonneg hσ j)]
    have hα_nonneg : 0 ≤ α := Finset.sum_nonneg fun i _ => hterm i
    have hP_le : P ≤ α • σ := by
      dsimp [P, α]
      rw [← sub_nonneg, show (∑ i, if σ.H.eigenvalues i = 0 then 0 else (σ.H.eigenvalues i)⁻¹) • σ =
        σ.cfc (fun x => (∑ i, if σ.H.eigenvalues i = 0 then 0 else (σ.H.eigenvalues i)⁻¹) * x) from by
        simp,
        HermitianMat.supportProj_eq_cfc, ← HermitianMat.cfc_sub_apply, HermitianMat.cfc_nonneg_iff]
      intro i; set y := σ.H.eigenvalues i
      by_cases hy0 : y = 0
      · simp [hy0]
      · have hy_pos := lt_of_le_of_ne (HermitianMat.eigenvalues_nonneg hσ i) (Ne.symm hy0)
        have hsingle : y⁻¹ ≤ α := by
          dsimp [α]; simpa [y, hy0] using
            Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ i)
        have := mul_le_mul_of_nonneg_right hsingle hy_pos.le
        simp [hy0]; linarith [inv_mul_cancel₀ hy0]
    rw [max, if_pos]
    · simp
    · refine ⟨Real.log (α + 1), ?_⟩
      calc ρ.M ≤ P := hρ_le_P
        _ ≤ α • σ := hP_le
        _ ≤ (α + 1) • σ := smul_le_smul_of_nonneg_right (by linarith) hσ
        _ = Real.exp (Real.log (α + 1)) • σ := by
            rw [Real.exp_log (by positivity : (0 : ℝ) < α + 1)]

protected theorem toReal_max (ρ : MState d) (σ : HermitianMat d ℂ) :
    (max ρ σ).toReal = sInf ((↑) '' { x : ℝ≥0 | ρ.M ≤ Real.exp x • σ }) := by
  rw [max]
  split_ifs with h
  · have hs : ({ x : ℝ≥0 | ρ.M ≤ Real.exp x • σ } : Set ℝ≥0).Nonempty := by
      rcases h with ⟨x, hx⟩
      have hσ_nonneg : 0 ≤ σ :=
        (smul_le_smul_iff_of_pos_left (Real.exp_pos x)).mp (by simpa using le_trans ρ.nonneg hx)
      refine ⟨⟨Max.max x 0, le_max_right _ _⟩, ?_⟩
      exact hx.trans <|
        smul_le_smul_of_nonneg_right
          (Real.exp_le_exp.mpr (show x ≤ Max.max x 0 from le_max_left _ _)) hσ_nonneg
    simp [ENNReal.some_eq_coe, NNReal.coe_sInf]
  · push Not at h
    have hs : ({ x : ℝ≥0 | ρ.M ≤ Real.exp x • σ } : Set ℝ≥0) = ∅ := by
      ext x
      simp [h (x : ℝ)]
    simp [hs]

@[simp]
theorem max_self_eq_zero (ρ : MState d) : max ρ ρ.M = 0 := by
  rw [max, if_pos ⟨0, by simp⟩]
  simp [show sInf { x : ℝ≥0 | ρ.M ≤ Real.exp x • ρ.M } = 0 from
    le_antisymm (csInf_le ⟨0, fun x _ => x.2⟩ (by simp))
      (le_csInf ⟨0, by simp⟩ fun x _ => x.2)]

/-- A full-support state dominates every other state up to an integer scalar. -/
private theorem exists_le_nat_smul_of_fullSupport (ρ σ : MState d)
    (hσ : σ.M.support = ⊤) :
    ∃ N : ℕ, 0 < N ∧ ρ.M ≤ ((N + 1 : ℝ) • σ.M) := by
  have hσ_ns : σ.M.NonSingular := HermitianMat.nonSingular_iff_support_top.mpr hσ
  have hker : σ.M.ker ≤ ρ.M.ker := by
    letI : σ.M.NonSingular := hσ_ns
    simp [HermitianMat.nonSingular_ker_bot]
  have hexp : ∃ x : ℝ, ρ.M ≤ Real.exp x • σ.M := by
    by_contra h
    exact (RelEntropy.max_not_top ρ σ.M σ.nonneg).mpr hker (by simp [max, h])
  obtain ⟨x, hx⟩ := hexp
  refine ⟨Nat.ceil (Real.exp x), Nat.ceil_pos.mpr (Real.exp_pos x), ?_⟩
  refine hx.trans ?_
  refine smul_le_smul_of_nonneg_right ?_ σ.nonneg
  exact (Nat.le_ceil _).trans (by norm_num)

/-- The output of Tomamichel's preparation channel on the first binary point. -/
private def binaryPrepOne (γ ω : MState d) (s t : ℝ) (hden : 0 < 1 - s - t)
    (h : t • γ.M ≤ (1 - s) • ω.M) : MState d where
  M := (1 - s - t)⁻¹ • ((1 - s) • ω.M - t • γ.M)
  nonneg := smul_nonneg (inv_nonneg.mpr hden.le) (sub_nonneg.mpr h)
  tr := by
    rw [HermitianMat.trace_smul, HermitianMat.trace_sub,
      HermitianMat.trace_smul, HermitianMat.trace_smul, γ.tr, ω.tr]
    field_simp [hden.ne']

/-- The output of Tomamichel's preparation channel on the second binary point. -/
private def binaryPrepZero (γ ω : MState d) (s t : ℝ) (hden : 0 < 1 - s - t)
    (h : s • ω.M ≤ (1 - t) • γ.M) : MState d where
  M := (1 - s - t)⁻¹ • ((1 - t) • γ.M - s • ω.M)
  nonneg := smul_nonneg (inv_nonneg.mpr hden.le) (sub_nonneg.mpr h)
  tr := by
    rw [HermitianMat.trace_smul, HermitianMat.trace_sub,
      HermitianMat.trace_smul, HermitianMat.trace_smul, γ.tr, ω.tr]
    field_simp [hden.ne']
    ring

/-- A binary coin lifted to the working universe. -/
private def uliftCoin (p : Prob) : ProbDistribution (ULift.{u} (Fin 2)) :=
  (ProbDistribution.congr Equiv.ulift.symm) (.coin p)

@[simp]
private theorem uliftCoin_apply_zero (p : Prob) :
    uliftCoin p (ULift.up (0 : Fin 2)) = p := by
  simp [uliftCoin, ProbDistribution.congr_apply]

@[simp]
private theorem uliftCoin_apply_one (p : Prob) :
    uliftCoin p (ULift.up (1 : Fin 2)) = 1 - p := by
  simp [uliftCoin, ProbDistribution.congr_apply]

private def cqPrepareChoiH {κ : Type u} [Fintype κ] [DecidableEq κ] (τ : κ → MState d) :
    HermitianMat (d × κ) ℂ :=
  ∑ i, HermitianMat.kronecker (τ i).M (MState.ofClassical (.constant i)).M

private def cqPrepareChoi {κ : Type u} [Fintype κ] [DecidableEq κ] (τ : κ → MState d) :
    Matrix (d × κ) (d × κ) ℂ :=
  (cqPrepareChoiH (d := d) τ).mat

private def cqPrepareMap {κ : Type u} [Fintype κ] [DecidableEq κ] (τ : κ → MState d) :
    MatrixMap κ d ℂ where
  toFun X := fun b₁ b₂ => ∑ i, X i i * (τ i).m b₁ b₂
  map_add' X Y := by
    ext b₁ b₂
    simp [Matrix.add_apply, Finset.sum_add_distrib, add_mul]
  map_smul' c X := by
    ext b₁ b₂
    simp [Matrix.smul_apply, Finset.mul_sum, mul_assoc]

private theorem cqPrepareMap_choi {κ : Type u} [Fintype κ] [DecidableEq κ] (τ : κ → MState d) :
    (cqPrepareMap (d := d) τ).choi_matrix = cqPrepareChoi (d := d) τ := by
  ext ⟨b₁, a₁⟩ ⟨b₂, a₂⟩
  simp only [MatrixMap.choi_matrix, cqPrepareMap, Matrix.single,
    cqPrepareChoi, cqPrepareChoiH, HermitianMat.mat_finset_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  show (if a₁ = x ∧ a₂ = x then 1 else 0) * (τ x).m b₁ b₂ =
    (τ x).m b₁ b₂ * (HermitianMat.diagonal ℂ (fun x₁ => ((ProbDistribution.constant x) x₁ : ℝ))).mat a₁ a₂
  rw [HermitianMat.diagonal_mat]
  by_cases h1 : a₁ = x <;> by_cases h2 : a₂ = x
  all_goals simp_all (config := { decide := true }) [Matrix.diagonal, ProbDistribution.constant_eq,
    Ne.symm]

private theorem cqPrepareChoi_psd {κ : Type u} [Fintype κ] [DecidableEq κ] (τ : κ → MState d) :
    (cqPrepareChoi (d := d) τ).PosSemidef := by
  change ((cqPrepareChoiH (d := d) τ).mat).PosSemidef
  have hnonneg : (0 : HermitianMat (d × κ) ℂ) ≤ cqPrepareChoiH (d := d) τ := by
    unfold cqPrepareChoiH
    exact Finset.sum_nonneg fun i _ =>
      HermitianMat.kronecker_nonneg (τ i).nonneg (MState.ofClassical (.constant i)).nonneg
  exact HermitianMat.zero_le_iff.mp hnonneg

private theorem cqPrepareChoi_traceLeft {κ : Type u} [Fintype κ] [DecidableEq κ]
    (τ : κ → MState d) :
    (cqPrepareChoi (d := d) τ).traceLeft = 1 := by
  have hTP : (cqPrepareMap (d := d) τ).IsTracePreserving := by
    intro X
    change ∑ x, ∑ i, X i i * (τ i).m x x = X.trace
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [← Finset.mul_sum]
    have htr : ∑ i₁, (τ i).m i₁ i₁ = 1 := by
      simpa [Matrix.trace] using (MState.tr' (ρ := τ i))
    rw [htr]
    simp [Matrix.diag_apply]
  simpa [cqPrepareMap_choi (d := d) τ] using
    (MatrixMap.IsTracePreserving_iff_trace_choi (cqPrepareMap (d := d) τ)).1 hTP

private def cqPrepareCPTP {κ : Type u} [Fintype κ] [DecidableEq κ] (τ : κ → MState d) :
    CPTPMap κ d :=
  CPTPMap.CPTP_of_choi_PSD_Tr
    (M := cqPrepareChoi (d := d) τ)
    (cqPrepareChoi_psd (d := d) τ)
    (cqPrepareChoi_traceLeft (d := d) τ)

private theorem cqPrepare_apply_ofClassical {κ : Type u} [Fintype κ] [DecidableEq κ]
    (τ : κ → MState d) (dist : ProbDistribution κ) :
    MatrixMap.of_choi_matrix (cqPrepareChoi (d := d) τ) (MState.ofClassical dist).m
      = ∑ i, (dist i : ℝ) • (τ i).m := by
  have hmap : MatrixMap.of_choi_matrix (cqPrepareChoi (d := d) τ) = cqPrepareMap (d := d) τ := by
    simpa [cqPrepareMap_choi (d := d) τ] using
      (MatrixMap.choi_map_inv (cqPrepareMap (d := d) τ))
  rw [hmap]
  ext b₁ b₂
  change ∑ i, (Matrix.diagonal fun x => ((dist x : Prob) : ℂ)) i i * (τ i).m b₁ b₂ =
    (∑ i, (dist i : ℝ) • (τ i).m) b₁ b₂
  rw [Matrix.sum_apply]
  simp [Matrix.smul_apply]

private theorem cqPrepareCPTP_apply_constant {κ : Type u} [Fintype κ] [DecidableEq κ]
    (τ : κ → MState d) (x : κ) :
    cqPrepareCPTP (d := d) τ (MState.ofClassical (.constant x)) = τ x := by
  apply MState.ext_m
  have hc : MatrixMap.of_choi_matrix (cqPrepareChoi (d := d) τ)
      (MState.ofClassical (.constant x)).m = (τ x).m := by
    rw [cqPrepare_apply_ofClassical (d := d) τ (.constant x)]
    ext i j
    rw [Finset.sum_eq_single x]
    · simp [ProbDistribution.constant_eq]
    · intro y _ hyx
      by_cases hxy : x = y
      · exact False.elim (hyx hxy.symm)
      · simp [ProbDistribution.constant_eq, hxy]
    · intro hx
      exact (hx (by simp)).elim
  simpa [cqPrepareCPTP] using hc

private theorem cqPrepare_apply_uliftCoin (τ : ULift (Fin 2) → MState d) (p : Prob) :
    MatrixMap.of_choi_matrix (cqPrepareChoi (d := d) τ) (MState.ofClassical (uliftCoin p)).m =
      (p : ℝ) • (τ (ULift.up (0 : Fin 2))).m +
        ((1 - p : Prob) : ℝ) • (τ (ULift.up (1 : Fin 2))).m := by
  rw [cqPrepare_apply_ofClassical (d := d) τ (uliftCoin p)]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul]
  let up : Fin 2 → ULift (Fin 2) := fun y => ULift.up y
  have hsum :
      (∑ x : ULift (Fin 2), ↑↑((uliftCoin p) x) * (τ x).m i j) =
        ∑ y : Fin 2, ↑↑((uliftCoin p) (up y)) * (τ (up y)).m i j := by
    refine Fintype.sum_equiv Equiv.ulift
      (fun x : ULift (Fin 2) => ↑↑((uliftCoin p) x) * (τ x).m i j)
      (fun y : Fin 2 => ↑↑((uliftCoin p) (up y)) * (τ (up y)).m i j) ?_
    rintro ⟨x⟩
    rfl
  rw [hsum]
  simp [up, Fin.sum_univ_two]

private theorem prob_mix_coe (p a b : Prob) :
    ((Prob.mix p a b : Prob) : ℝ) =
      (p : ℝ) * (a : ℝ) + ((1 - p : Prob) : ℝ) * (b : ℝ) := by
  simp [Prob.mix, Mixable.mix, Mixable.mix_ab]

private def binaryClassicalPostprocess (a b : Prob) :
    CPTPMap (ULift (Fin 2)) (ULift (Fin 2)) :=
  let τ : ULift (Fin 2) → MState (ULift (Fin 2)) := fun i =>
    if i = ULift.up (0 : Fin 2) then MState.ofClassical (uliftCoin a)
    else MState.ofClassical (uliftCoin b)
  CPTPMap.CPTP_of_choi_PSD_Tr
    (M := cqPrepareChoi (d := ULift (Fin 2)) τ)
    (cqPrepareChoi_psd (d := ULift (Fin 2)) τ)
    (cqPrepareChoi_traceLeft (d := ULift (Fin 2)) τ)

private theorem binaryClassicalPostprocess_apply (a b p : Prob) :
    binaryClassicalPostprocess a b (MState.ofClassical (uliftCoin p)) =
      MState.ofClassical (uliftCoin (Prob.mix p a b)) := by
  apply MState.ext_m
  change MatrixMap.of_choi_matrix
      (cqPrepareChoi (d := ULift (Fin 2))
        (fun i : ULift (Fin 2) =>
          if i = ULift.up (0 : Fin 2) then MState.ofClassical (uliftCoin a)
          else MState.ofClassical (uliftCoin b)))
      (MState.ofClassical (uliftCoin p)).m =
    (MState.ofClassical (uliftCoin (Prob.mix p a b))).m
  rw [cqPrepare_apply_uliftCoin]
  ext i j
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  fin_cases i <;> fin_cases j
  all_goals
    simp [MState.m, MState.ofClassical, Matrix.add_apply, Prob.coe_one_minus, uliftCoin,
      ProbDistribution.congr_apply]
    try rw [← HermitianMat.mat_apply, HermitianMat.diagonal_mat]
    try simp [Matrix.diagonal, prob_mix_coe, Prob.coe_one_minus]
    try ring_nf

private theorem uliftCoin_support_top (p : Prob) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    (MState.ofClassical (uliftCoin p)).M.support = ⊤ := by
  have hpos : ∀ i : ULift (Fin 2), 0 < ((uliftCoin p) i : ℝ) := by
    intro i
    rcases i with ⟨i⟩
    fin_cases i
    · simpa using hp0
    · have h : 0 < 1 - (p : ℝ) := by linarith
      simpa [Prob.coe_one_minus] using h
  rw [← HermitianMat.nonSingular_iff_support_top]
  apply HermitianMat.nonSingular_of_posDef
  rw [MState.coe_ofClassical]
  apply Matrix.PosDef.diagonal
  intro i
  simpa [Complex.real_lt_real] using hpos i

private def classicalIndicatorEffect {κ : Type u} [DecidableEq κ] (A : Set κ) :
    HermitianMat κ ℂ := by classical exact HermitianMat.diagonal ℂ fun x => if x ∈ A then 1 else 0

private theorem ofClassical_exp_val_indicator
    {κ : Type u} [Fintype κ] [DecidableEq κ] (dist : ProbDistribution κ) (A : Set κ)
    [DecidablePred (fun x => x ∈ A)] :
    (MState.ofClassical dist).exp_val (classicalIndicatorEffect A) =
      ∑ x, if x ∈ A then (dist x : ℝ) else 0 := by
  rw [classicalIndicatorEffect, MState.exp_val, MState.coe_ofClassical,
    HermitianMat.inner_eq_re_trace]
  simp [Matrix.trace, HermitianMat.diagonal]
  exact Finset.sum_congr rfl fun x _ => by by_cases hx : x ∈ A <;> simp [hx]

private def hellingerOverlap {κ : Type u} [Fintype κ]
    (P Q : ProbDistribution κ) : ℝ :=
  ∑ x, Real.sqrt ((P x : ℝ) * (Q x : ℝ))

private theorem prob_le_sqrt_mul_of_le {p q : Prob} (hpq : (p : ℝ) ≤ q) :
    (p : ℝ) ≤ Real.sqrt ((p : ℝ) * (q : ℝ)) := by
  rw [Real.le_sqrt p.2.1 (mul_nonneg p.2.1 q.2.1)]
  simpa [pow_two] using mul_le_mul_of_nonneg_left hpq p.2.1

private theorem exists_effect_exp_val_ne_of_ne (ρ σ : MState d) (hne : ρ ≠ σ) :
    ∃ T : HermitianMat d ℂ, (0 ≤ T ∧ T ≤ 1) ∧ ρ.exp_val T ≠ σ.exp_val T := by
  let A : HermitianMat d ℂ := ρ.M - σ.M
  have hA_tr : A.trace = 0 := by
    simp [A, HermitianMat.trace_sub, ρ.tr, σ.tr]
  have hA_not_nonneg : ¬ 0 ≤ A := by
    intro hA_nonneg
    have hA_mat_tr : A.mat.trace = 0 :=
      (HermitianMat.trace_eq_zero_iff (A := A)).1 hA_tr
    have hA_mat_zero : A.mat = 0 :=
      (Matrix.PosSemidef.trace_eq_zero_iff (HermitianMat.zero_le_iff.mp hA_nonneg)).1 hA_mat_tr
    exact hne (MState.ext (eq_of_sub_eq_zero (HermitianMat.ext hA_mat_zero)))
  let B : HermitianMat d ℂ := A⁻
  have hB_nonneg : 0 ≤ B := by
    simpa [B] using HermitianMat.negPart_nonneg A
  have hinner_neg : inner ℝ A B < 0 := by
    simpa [B] using (HermitianMat.inner_negPart_neg_iff (A := A)).2 hA_not_nonneg
  have hB_ne : B ≠ 0 := by
    intro hB_zero
    rw [hB_zero] at hinner_neg
    simp at hinner_neg
  have hB_trace_pos : 0 < B.trace := by
    refine lt_of_le_of_ne (HermitianMat.trace_nonneg hB_nonneg) ?_
    intro htrace
    have hB_mat_tr : B.mat.trace = 0 :=
      (HermitianMat.trace_eq_zero_iff (A := B)).1 htrace.symm
    exact hB_ne (HermitianMat.ext
      ((Matrix.PosSemidef.trace_eq_zero_iff (HermitianMat.zero_le_iff.mp hB_nonneg)).1 hB_mat_tr))
  let T : HermitianMat d ℂ := B.trace⁻¹ • B
  have hT_nonneg : 0 ≤ T := by
    simpa [T] using smul_nonneg (inv_nonneg.mpr hB_trace_pos.le) hB_nonneg
  have hT_le_one : T ≤ 1 := by
    dsimp [T]
    calc
      B.trace⁻¹ • B ≤ B.trace⁻¹ • (B.trace • (1 : HermitianMat d ℂ)) :=
        smul_le_smul_of_nonneg_left (HermitianMat.le_trace_smul_one hB_nonneg)
          (inv_nonneg.mpr hB_trace_pos.le)
      _ = 1 := by
        rw [smul_smul, inv_mul_cancel₀ hB_trace_pos.ne']
        simp
  refine ⟨T, ⟨hT_nonneg, hT_le_one⟩, ?_⟩
  intro hsame
  have hsub : ρ.exp_val T - σ.exp_val T = 0 := sub_eq_zero.mpr hsame
  have hcalc : ρ.exp_val T - σ.exp_val T = inner ℝ A T := by
    simp [A, MState.exp_val, inner_sub_left]
  rw [hcalc] at hsub
  have hscaled : inner ℝ A T = B.trace⁻¹ * inner ℝ A B := by
    simp [T, inner_smul_right]
  have hneg : inner ℝ A T < 0 := by
    simpa [hscaled] using mul_neg_of_pos_of_neg (inv_pos.mpr hB_trace_pos) hinner_neg
  linarith

private def tauOfLE (N : ℕ) (hN : 0 < N) (ρ σ : MState d)
    (h : ρ.M ≤ ((N + 1 : ℝ) • σ.M)) : MState d where
  M := ((N : ℝ)⁻¹) • (((N + 1 : ℝ) • σ.M) - ρ.M)
  nonneg := smul_nonneg (by positivity) (sub_nonneg.mpr h)
  tr := by
    have hN' : (N : ℝ) ≠ 0 := by positivity
    simp [HermitianMat.trace_sub, σ.tr, ρ.tr, hN']

private theorem mstate_eq_of_le (ρ σ : MState d) (h : ρ.M ≤ σ.M) : ρ = σ := by
  have hsub : 0 ≤ σ.M - ρ.M := by simpa using sub_nonneg.mpr h
  exact MState.ext <| (eq_of_sub_eq_zero (HermitianMat.ext <|
    (Matrix.PosSemidef.trace_eq_zero_iff (HermitianMat.zero_le_iff.mp hsub)).1 <|
      (HermitianMat.trace_eq_zero_iff (A := σ.M - ρ.M)).1 (by simp [σ.tr, ρ.tr]))).symm

private theorem cqPrepareCPTP_uniform_tauOfLE
    (M : ℕ) (hM_pos : 0 < M) (ρ σ : MState d)
    (h : ρ.M ≤ ((M + 1 : ℝ) • σ.M)) :
    cqPrepareCPTP (d := d) (fun i : ULift (Fin (M + 1)) =>
      if i = ⟨0⟩ then ρ else tauOfLE (d := d) M hM_pos ρ σ h)
      (MState.uniform : MState (ULift (Fin (M + 1)))) = σ := by
  apply MState.ext_m
  have hsu : MatrixMap.of_choi_matrix (cqPrepareChoi (d := d)
      (fun i : ULift (Fin (M + 1)) =>
        if i = ⟨0⟩ then ρ else tauOfLE (d := d) M hM_pos ρ σ h))
      (MState.uniform : MState (ULift (Fin (M + 1)))).m = σ.m := by
    change MatrixMap.of_choi_matrix
        (cqPrepareChoi (d := d) (fun i : ULift (Fin (M + 1)) =>
          if i = ⟨0⟩ then ρ else tauOfLE (d := d) M hM_pos ρ σ h))
        (MState.ofClassical ProbDistribution.uniform).m = σ.m
    rw [cqPrepare_apply_ofClassical (d := d)
      (fun i : ULift (Fin (M + 1)) =>
        if i = ⟨0⟩ then ρ else tauOfLE (d := d) M hM_pos ρ σ h)
      ProbDistribution.uniform]
    let x0 : ULift (Fin (M + 1)) := ⟨0⟩
    let τr := tauOfLE (d := d) M hM_pos ρ σ h
    ext i j
    simp only [ProbDistribution.uniform_def, Matrix.sum_apply, Matrix.smul_apply,
      Complex.real_smul, Finset.card_univ, Fintype.card_ulift, Fintype.card_fin, one_div,
      Nat.cast_add, Nat.cast_one, Complex.ofReal_inv, Complex.ofReal_add,
      Complex.ofReal_natCast, Complex.ofReal_one]
    have hsplit :
        Finset.sum Finset.univ
          (fun x : ULift (Fin (M + 1)) =>
            (↑M + 1 : ℂ)⁻¹ * (if x = x0 then ρ else τr).m i j)
          =
        Finset.sum (Finset.erase Finset.univ x0)
          (fun x : ULift (Fin (M + 1)) =>
            (↑M + 1 : ℂ)⁻¹ * (if x = x0 then ρ else τr).m i j)
          + (↑M + 1 : ℂ)⁻¹ * ρ.m i j := by
      exact (Finset.sum_erase_add (s := Finset.univ) (a := x0)
        (f := fun x : ULift (Fin (M + 1)) =>
          (↑M + 1 : ℂ)⁻¹ * (if x = x0 then ρ else τr).m i j) (by simp)).symm
    have hrest :
        Finset.sum (Finset.erase Finset.univ x0)
          (fun x : ULift (Fin (M + 1)) =>
            (↑M + 1 : ℂ)⁻¹ * (if x = x0 then ρ else τr).m i j)
          =
        M * ((↑M + 1 : ℂ)⁻¹ * τr.m i j) := by
      calc
        Finset.sum (Finset.erase Finset.univ x0)
            (fun x : ULift (Fin (M + 1)) =>
              (↑M + 1 : ℂ)⁻¹ * (if x = x0 then ρ else τr).m i j)
          =
            Finset.sum (Finset.erase Finset.univ x0)
              (fun _ : ULift (Fin (M + 1)) => (↑M + 1 : ℂ)⁻¹ * τr.m i j) := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                simp [(Finset.mem_erase.mp hx).1]
        _ = M * ((↑M + 1 : ℂ)⁻¹ * τr.m i j) := by
            simp [x0]
    rw [hsplit, hrest]
    have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM_pos
    have hM1 : (M + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero M
    dsimp [τr]
    simp [tauOfLE, MState.m]
    field_simp [hM0, hM1]
    have hcancel :
        ((((M + 1 : ℝ) • (σ : HermitianMat d ℂ)) - (ρ : HermitianMat d ℂ)) +
            (ρ : HermitianMat d ℂ) : HermitianMat d ℂ) =
          (((M + 1 : ℝ) • (σ : HermitianMat d ℂ)) : HermitianMat d ℂ) := by
      abel
    have hcancel_ij := congrArg (fun A : HermitianMat d ℂ => A i j) hcancel
    convert hcancel_ij using 1
    simp [HermitianMat.smul_apply]
  simpa [cqPrepareCPTP] using hsu

private theorem integer_bound_aux (N : ℕ) (ρ σ : MState d)
    (h : ρ.M ≤ ((N + 1 : ℝ) • σ.M)) :
    f ρ σ.M ≤ ENNReal.ofReal (Real.log (N + 1)) := by
  cases N with
  | zero =>
      have hEq : ρ = σ := mstate_eq_of_le ρ σ (by simpa using h)
      subst hEq
      simp
  | succ N =>
      let κ := ULift (Fin (N + 2))
      let τrest := tauOfLE (d := d) (N + 1) (Nat.succ_pos _) ρ σ h
      let τ : κ → MState d := fun i => if i = ⟨0⟩ then ρ else τrest
      let Λ : CPTPMap κ d := cqPrepareCPTP (d := d) τ
      have hconst : Λ (MState.ofClassical (.constant (⟨0⟩ : κ))) = ρ := by
        simpa [Λ, τ] using cqPrepareCPTP_apply_constant (d := d) τ (⟨0⟩ : κ)
      have huniform : Λ (MState.uniform : MState κ) = σ := by
        simpa [Λ, κ, τ, τrest] using
          cqPrepareCPTP_uniform_tauOfLE (d := d) (N + 1) (Nat.succ_pos _) ρ σ h
      calc
        f ρ σ.M =
            f (Λ (MState.ofClassical (.constant (⟨0⟩ : κ))))
              ((Λ (MState.uniform : MState κ)).M) := by
          rw [hconst, huniform]
        _ ≤ f (MState.ofClassical (.constant (⟨0⟩ : κ))) (MState.uniform : MState κ).M := DPI _ _ Λ
        _ = ENNReal.ofReal (Real.log (N + 2)) := by
          have hlog_nonneg : 0 ≤ Real.log (N + 2 : ℝ) :=
            Real.log_nonneg (by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith)
          simpa [κ, ENNReal.some_eq_coe, ENNReal.ofReal_eq_coe_nnreal hlog_nonneg] using
            (RelEntropy.normalized (f := f) (d := κ) (⟨0⟩ : κ))
        _ = ENNReal.ofReal (Real.log (↑(N + 1) + 1)) := by
          congr 2
          norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]

private theorem smul_kronecker {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (a b : ℝ) (A : HermitianMat m ℂ) (B : HermitianMat n ℂ) :
    (a • A) ⊗ₖ (b • B) = (a * b) • (A ⊗ₖ B) := by
  ext1
  simp [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, mul_comm]

private def DyadicPow (d : Type u) : ℕ → Type u
  | 0 => d
  | n + 1 => DyadicPow d n × DyadicPow d n

private instance dyadicPowFintype (n : ℕ) : Fintype (DyadicPow d n) := by
  induction n with
  | zero => simpa [DyadicPow] using (inferInstance : Fintype d)
  | succ n ih => simpa [DyadicPow] using (inferInstance : Fintype (DyadicPow d n × DyadicPow d n))

private instance dyadicPowDecidableEq (n : ℕ) : DecidableEq (DyadicPow d n) := by
  induction n with
  | zero => simpa [DyadicPow] using (inferInstance : DecidableEq d)
  | succ n ih =>
      simpa [DyadicPow] using (inferInstance : DecidableEq (DyadicPow d n × DyadicPow d n))

private def dyadicStatePow (ρ : MState d) : ∀ n, MState (DyadicPow d n)
  | 0 => ρ
  | n + 1 => dyadicStatePow ρ n ⊗ᴹ dyadicStatePow ρ n

private def dyadicProbPow (dist : ProbDistribution d) : ∀ n, ProbDistribution (DyadicPow d n)
  | 0 => dist
  | n + 1 => ProbDistribution.prod (dyadicProbPow dist n) (dyadicProbPow dist n)

private theorem dyadicStatePow_ofClassical (dist : ProbDistribution d) :
    ∀ n, dyadicStatePow (MState.ofClassical dist) n =
      MState.ofClassical (dyadicProbPow dist n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change dyadicStatePow (MState.ofClassical dist) n ⊗ᴹ
          dyadicStatePow (MState.ofClassical dist) n =
        MState.ofClassical
          (ProbDistribution.prod (dyadicProbPow dist n) (dyadicProbPow dist n))
      rw [ih]
      apply MState.ext_m
      ext i j
      simp [MState.m, MState.prod, MState.ofClassical, ProbDistribution.prod,
        HermitianMat.kronecker_diagonal]

private theorem hellingerOverlap_uliftCoin (p q : Prob) :
    hellingerOverlap (uliftCoin p) (uliftCoin q) =
      Real.sqrt ((p : ℝ) * (q : ℝ)) +
        Real.sqrt ((1 - (p : ℝ)) * (1 - (q : ℝ))) := by
  rw [hellingerOverlap]
  have hsum :
      (∑ x : ULift (Fin 2),
          Real.sqrt (((uliftCoin p) x : ℝ) * ((uliftCoin q) x : ℝ))) =
        ∑ y : Fin 2,
          Real.sqrt (((ProbDistribution.coin p) y : ℝ) *
            ((ProbDistribution.coin q) y : ℝ)) := by
    simpa [uliftCoin, ProbDistribution.congr_apply] using
      (Equiv.sum_comp (Equiv.ulift : ULift (Fin 2) ≃ Fin 2)
        (fun y : Fin 2 => Real.sqrt (((ProbDistribution.coin p) y : ℝ) *
          ((ProbDistribution.coin q) y : ℝ))))
  rw [hsum]
  simp [Fin.sum_univ_two]

private theorem hellingerOverlap_uliftCoin_lt_one (p q : Prob) (hpq : (p : ℝ) < q) :
    hellingerOverlap (uliftCoin p) (uliftCoin q) < 1 := by
  rw [hellingerOverlap_uliftCoin]
  have hp0 : 0 ≤ (p : ℝ) := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  have hq0 : 0 ≤ (q : ℝ) := q.2.1
  have hq1 : (q : ℝ) ≤ 1 := q.2.2
  have hpq_nonneg : 0 ≤ (p : ℝ) * q := mul_nonneg hp0 hq0
  have hcomp_nonneg : 0 ≤ (1 - (p : ℝ)) * (1 - q) :=
    mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hq1)
  have hmid_pos : 0 < ((p : ℝ) + q - 2 * p * q) / 2 := by
    have hp_nonneg : 0 ≤ (p : ℝ) * (1 - q) := mul_nonneg hp0 (sub_nonneg.mpr hq1)
    have hq_pos : 0 < (q : ℝ) * (1 - p) := by
      refine mul_pos (lt_of_le_of_lt hp0 hpq) ?_
      linarith
    nlinarith
  have hsqrt_lt :
      Real.sqrt (((p : ℝ) * q) * ((1 - p) * (1 - q))) <
        ((p : ℝ) + q - 2 * p * q) / 2 := by
    rw [Real.sqrt_lt' hmid_pos]
    nlinarith [sq_pos_of_pos (sub_pos.mpr hpq)]
  have hsquare :
      (Real.sqrt ((p : ℝ) * q) + Real.sqrt ((1 - (p : ℝ)) * (1 - q))) ^ 2 < 1 ^ 2 := by
    have hsqrt_mul :
        Real.sqrt ((p : ℝ) * q) * Real.sqrt ((1 - p) * (1 - q)) =
          Real.sqrt (((p : ℝ) * q) * ((1 - p) * (1 - q))) := by
      rw [← Real.sqrt_mul hpq_nonneg]
    rw [add_sq, Real.sq_sqrt hpq_nonneg, Real.sq_sqrt hcomp_nonneg]
    nlinarith [hsqrt_mul]
  exact (sq_lt_sq₀ (by positivity) (by norm_num : (0 : ℝ) ≤ 1)).mp (by simpa using hsquare)

private theorem hellingerOverlap_prod {κ η : Type u} [Fintype κ] [Fintype η]
    (P₁ Q₁ : ProbDistribution κ) (P₂ Q₂ : ProbDistribution η) :
    hellingerOverlap (ProbDistribution.prod P₁ P₂) (ProbDistribution.prod Q₁ Q₂) =
      hellingerOverlap P₁ Q₁ * hellingerOverlap P₂ Q₂ := by
  rw [hellingerOverlap, hellingerOverlap, hellingerOverlap]
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : κ, ∑ y : η,
        Real.sqrt ((((P₁ x) * (P₂ y) : Prob) : ℝ) *
          (((Q₁ x) * (Q₂ y) : Prob) : ℝ))) =
        ∑ x : κ, ∑ y : η,
          Real.sqrt (((P₁ x : ℝ) * (Q₁ x : ℝ)) *
            ((P₂ y : ℝ) * (Q₂ y : ℝ))) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          refine Finset.sum_congr rfl ?_
          intro y _
          congr 1
          simp [mul_assoc, mul_left_comm, mul_comm]
    _ = ∑ x : κ, ∑ y : η,
          Real.sqrt ((P₁ x : ℝ) * (Q₁ x : ℝ)) *
            Real.sqrt ((P₂ y : ℝ) * (Q₂ y : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          refine Finset.sum_congr rfl ?_
          intro y _
          rw [Real.sqrt_mul]
          exact mul_nonneg (P₁ x).2.1 (Q₁ x).2.1
    _ = (∑ x : κ, Real.sqrt ((P₁ x : ℝ) * (Q₁ x : ℝ))) *
          ∑ y : η, Real.sqrt ((P₂ y : ℝ) * (Q₂ y : ℝ)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [Finset.mul_sum]

omit [DecidableEq d] in
private theorem hellingerOverlap_dyadicProbPow (P Q : ProbDistribution d) :
    ∀ m, hellingerOverlap (dyadicProbPow P m) (dyadicProbPow Q m) =
      (hellingerOverlap P Q) ^ (2 ^ m : ℕ) := by
  intro m
  induction m with
  | zero =>
      change hellingerOverlap P Q = (hellingerOverlap P Q) ^ (1 : ℕ)
      rw [pow_one]
  | succ m ih =>
      set_option maxRecDepth 1000 in
      change hellingerOverlap
          (ProbDistribution.prod (dyadicProbPow P m) (dyadicProbPow P m))
          (ProbDistribution.prod (dyadicProbPow Q m) (dyadicProbPow Q m)) =
        (hellingerOverlap P Q) ^ (2 ^ (m + 1) : ℕ)
      rw [hellingerOverlap_prod, ih]
      have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by omega
      rw [hpow, pow_add]

private theorem exists_likelihood_indicator_effect
    {κ : Type u} [Fintype κ] [DecidableEq κ] (P Q : ProbDistribution κ) (s r : Prob)
    (hoverlap_s : hellingerOverlap P Q ≤ (s : ℝ))
    (hoverlap_r : hellingerOverlap P Q ≤ 1 - (r : ℝ)) :
    ∃ T : HermitianMat κ ℂ, (0 ≤ T ∧ T ≤ 1) ∧
      ∃ α β : Prob,
        (MState.ofClassical P).exp_val T = α ∧
        (MState.ofClassical Q).exp_val T = β ∧
        (α : ℝ) ≤ s ∧ (r : ℝ) ≤ β := by
  classical
  let A : Set κ := {x | (P x : ℝ) ≤ Q x}
  let T : HermitianMat κ ℂ := classicalIndicatorEffect A
  have hT : 0 ≤ T ∧ T ≤ 1 := by
    classical
    refine ⟨?_, ?_⟩
    · rw [HermitianMat.zero_le_iff]
      rw [show T = HermitianMat.diagonal ℂ fun x => if x ∈ A then (1 : ℝ) else 0 from rfl,
        HermitianMat.diagonal_mat, Matrix.posSemidef_diagonal_iff]
      intro i
      by_cases hi : i ∈ A <;> simp [hi]
    · rw [← sub_nonneg]
      rw [show T = HermitianMat.diagonal ℂ fun x => if x ∈ A then (1 : ℝ) else 0 from rfl,
        ← HermitianMat.diagonal_one (𝕜 := ℂ),
        ← HermitianMat.diagonal_sub, HermitianMat.zero_le_iff, HermitianMat.diagonal_mat,
        Matrix.posSemidef_diagonal_iff]
      intro i
      by_cases hi : i ∈ A <;> simp [hi]
  let α : Prob := ⟨(MState.ofClassical P).exp_val T, (MState.ofClassical P).exp_val_prob hT⟩
  let β : Prob := ⟨(MState.ofClassical Q).exp_val T, (MState.ofClassical Q).exp_val_prob hT⟩
  refine ⟨T, hT, α, β, rfl, rfl, ?_, ?_⟩
  · change (MState.ofClassical P).exp_val T ≤ (s : ℝ)
    rw [ofClassical_exp_val_indicator]
    have hp_mass : ∑ x, (if (P x : ℝ) ≤ Q x then (P x : ℝ) else 0) ≤
        hellingerOverlap P Q := by
      rw [hellingerOverlap]
      refine Finset.sum_le_sum ?_
      intro x _
      by_cases hx : (P x : ℝ) ≤ Q x
      · simpa [hx] using prob_le_sqrt_mul_of_le (p := P x) (q := Q x) hx
      · simpa [hx] using Real.sqrt_nonneg ((P x : ℝ) * (Q x : ℝ))
    exact hp_mass.trans hoverlap_s
  · change (r : ℝ) ≤ (MState.ofClassical Q).exp_val T
    rw [ofClassical_exp_val_indicator]
    change (r : ℝ) ≤ ∑ x, (if (P x : ℝ) ≤ Q x then (Q x : ℝ) else 0)
    have hcompl : ∑ x, (if (P x : ℝ) ≤ Q x then 0 else (Q x : ℝ)) ≤
        hellingerOverlap P Q := by
      rw [hellingerOverlap]
      refine Finset.sum_le_sum ?_
      intro x _
      by_cases hx : (P x : ℝ) ≤ Q x
      · simpa [hx] using Real.sqrt_nonneg ((P x : ℝ) * (Q x : ℝ))
      · have hqp : (Q x : ℝ) ≤ P x := le_of_not_ge hx
        rw [mul_comm]
        simpa [hx] using prob_le_sqrt_mul_of_le hqp
    have htotal' :
        (∑ x, (if (P x : ℝ) ≤ Q x then 0 else (Q x : ℝ))) +
          (∑ x, (if (P x : ℝ) ≤ Q x then (Q x : ℝ) else 0)) =
        1 := by
      rw [← Finset.sum_add_distrib]
      trans ∑ x, (Q x : ℝ)
      · refine Finset.sum_congr rfl ?_
        intro x _
        by_cases hx : (P x : ℝ) ≤ Q x <;> simp [hx]
      · exact Q.normalized
    linarith

private theorem exists_dyadic_binary_effect_le_ge
    (p q s r : Prob) (hpq : (p : ℝ) < q)
    (hs_pos : 0 < (s : ℝ)) (hr_lt_one : (r : ℝ) < 1) :
    ∃ (n : ℕ) (T : HermitianMat (DyadicPow (ULift.{u} (Fin 2)) n) ℂ),
      (0 ≤ T ∧ T ≤ 1) ∧ ∃ α β : Prob,
        (dyadicStatePow (MState.ofClassical (uliftCoin p)) n).exp_val T = α ∧
        (dyadicStatePow (MState.ofClassical (uliftCoin q)) n).exp_val T = β ∧
        (α : ℝ) ≤ s ∧ (r : ℝ) ≤ β := by
  let ε : ℝ := (s : ℝ) ⊓ (1 - (r : ℝ))
  have hε : 0 < ε := by
    simpa [ε] using lt_inf_iff.mpr ⟨hs_pos, sub_pos.mpr hr_lt_one⟩
  have ha0 : 0 ≤ hellingerOverlap (uliftCoin p) (uliftCoin q) := by
    rw [hellingerOverlap_uliftCoin]
    positivity
  have ha1 : hellingerOverlap (uliftCoin p) (uliftCoin q) < 1 :=
    hellingerOverlap_uliftCoin_lt_one p q hpq
  obtain ⟨n, hn'⟩ := exists_pow_lt_of_lt_one hε ha1
  have hn : (hellingerOverlap (uliftCoin p) (uliftCoin q)) ^ (2 ^ n : ℕ) < ε := lt_of_le_of_lt
    (pow_le_pow_of_le_one ha0 ha1.le (Nat.lt_two_pow_self (n := n)).le) hn'
  have hoverlap_lt :
      hellingerOverlap (dyadicProbPow (uliftCoin p) n) (dyadicProbPow (uliftCoin q) n) < ε := by
    rw [hellingerOverlap_dyadicProbPow]
    exact hn
  have hoverlap_s :
      hellingerOverlap (dyadicProbPow (uliftCoin p) n) (dyadicProbPow (uliftCoin q) n) ≤
        (s : ℝ) :=
    hoverlap_lt.le.trans inf_le_left
  have hoverlap_r :
      hellingerOverlap (dyadicProbPow (uliftCoin p) n) (dyadicProbPow (uliftCoin q) n) ≤
        1 - (r : ℝ) :=
    hoverlap_lt.le.trans inf_le_right
  obtain ⟨T, hT, α, β, hpT, hqT, hαs, hrβ⟩ :
      ∃ T : HermitianMat (DyadicPow (ULift.{u} (Fin 2)) n) ℂ, (0 ≤ T ∧ T ≤ 1) ∧
        ∃ α β : Prob,
        (MState.ofClassical (dyadicProbPow (uliftCoin p) n)).exp_val T = α ∧
        (MState.ofClassical (dyadicProbPow (uliftCoin q) n)).exp_val T = β ∧
        (α : ℝ) ≤ s ∧ (r : ℝ) ≤ β := by
    exact exists_likelihood_indicator_effect
      (dyadicProbPow (uliftCoin p) n) (dyadicProbPow (uliftCoin q) n) s r hoverlap_s hoverlap_r
  refine ⟨n, T, hT, α, β, ?_, ?_, hαs, hrβ⟩
  · simpa [dyadicStatePow_ofClassical] using hpT
  · simpa [dyadicStatePow_ofClassical] using hqT

private def dyadicCPTPMapPow {e : Type u} [Fintype e] [DecidableEq e]
    (Λ : CPTPMap d e) : ∀ n, CPTPMap (DyadicPow d n) (DyadicPow e n)
  | 0 => Λ
  | n + 1 => dyadicCPTPMapPow Λ n ⊗ᶜᵖ dyadicCPTPMapPow Λ n

/-- Universe-lifted two-outcome POVM associated to an effect `0 ≤ T ≤ 1`. -/
private def binaryPOVMOfEffectULift (T : HermitianMat d ℂ) (hT : 0 ≤ T ∧ T ≤ 1) :
    POVM (ULift (Fin 2)) d where
  mats i := if i = ULift.up (0 : Fin 2) then T else 1 - T
  nonneg i := by
    split
    · exact hT.1
    · exact HermitianMat.zero_le_iff.mpr hT.2
  normalized := by
    have hsum :
        (∑ i : ULift (Fin 2), if i = ULift.up (0 : Fin 2) then T else 1 - T) =
          ∑ i : Fin 2, if ULift.up i = ULift.up (0 : Fin 2) then T else 1 - T := by
      refine Fintype.sum_equiv Equiv.ulift
        (fun i : ULift (Fin 2) => if i = ULift.up (0 : Fin 2) then T else 1 - T)
        (fun i : Fin 2 => if ULift.up i = ULift.up (0 : Fin 2) then T else 1 - T) ?_
      rintro ⟨x⟩
      rfl
    rw [hsum]
    simp [Fin.sum_univ_two]

/-- Measuring a lifted binary effect and discarding the post-measurement state gives a lifted coin. -/
private theorem binaryPOVMOfEffectULift_measureDiscard_apply
    (T : HermitianMat d ℂ) (hT : 0 ≤ T ∧ T ≤ 1) (ρ : MState d) :
    (binaryPOVMOfEffectULift T hT).measureDiscard ρ =
      MState.ofClassical (uliftCoin ⟨ρ.exp_val T, ρ.exp_val_prob hT⟩) := by
  rw [POVM.measureDiscard_apply]
  congr 1
  let p : Prob := ⟨ρ.exp_val T, ρ.exp_val_prob hT⟩
  ext i
  rcases i with ⟨i⟩
  fin_cases i
  · let z : ULift (Fin 2) := ULift.up (0 : Fin 2)
    change (((binaryPOVMOfEffectULift T hT).measure ρ) z : ℝ) = ((uliftCoin p) z : ℝ)
    change inner ℝ T ρ.M = ((uliftCoin p) z : ℝ)
    have hz : ((uliftCoin p) z : ℝ) = ρ.exp_val T := by
      simp [z, p]
    rw [hz, HermitianMat.inner_comm]
    rfl
  · let o : ULift (Fin 2) := ULift.up (1 : Fin 2)
    change (((binaryPOVMOfEffectULift T hT).measure ρ) o : ℝ) = ((uliftCoin p) o : ℝ)
    change inner ℝ (1 - T) ρ.M = ((uliftCoin p) o : ℝ)
    have ho : ((uliftCoin p) o : ℝ) = 1 - ρ.exp_val T := by
      simp [o, p, Prob.coe_one_minus]
    rw [ho, HermitianMat.inner_comm, inner_sub_right, HermitianMat.inner_one, ρ.tr]
    rfl

/-- Named-probability version of `binaryPOVMOfEffectULift_measureDiscard_apply`. -/
private theorem binaryPOVMOfEffectULift_measureDiscard_apply_eq_uliftCoin
    (T : HermitianMat d ℂ) (hT : 0 ≤ T ∧ T ≤ 1) (ρ : MState d) (p : Prob)
    (hρT : ρ.exp_val T = p) :
    (binaryPOVMOfEffectULift T hT).measureDiscard ρ =
      MState.ofClassical (uliftCoin p) := by
  rw [binaryPOVMOfEffectULift_measureDiscard_apply]
  congr 2
  exact Subtype.ext hρT

private theorem dyadicStatePow_relEntropy (ρ σ : MState d) :
    ∀ n, f (dyadicStatePow ρ n) (dyadicStatePow σ n).M = ((2 ^ n : ℕ) : ENNReal) * f ρ σ := by
  intro n
  induction n with
  | zero =>
      simp [dyadicStatePow]
      rfl
  | succ n ih =>
      have hkron :=
        RelEntropy.of_kron (f := f)
          (dyadicStatePow ρ n) (dyadicStatePow σ n)
          (dyadicStatePow ρ n) (dyadicStatePow σ n)
      show f (dyadicStatePow ρ n ⊗ᴹ dyadicStatePow ρ n)
            ↑(dyadicStatePow σ n ⊗ᴹ dyadicStatePow σ n) = _
      rw [hkron, ih]
      rw [← two_mul, ← mul_assoc,
        mul_comm (2 : ENNReal) (((2 ^ n : ℕ) : ENNReal)), mul_assoc]
      simp [pow_succ, Nat.cast_mul, mul_assoc]

private theorem exists_binary_measurement_of_ne (ρ σ : MState d) (hne : ρ ≠ σ) :
    ∃ p q : Prob, (p : ℝ) < (q : ℝ) ∧
      ∃ Λ : CPTPMap d (ULift.{u} (Fin 2)),
        Λ ρ = MState.ofClassical (uliftCoin p) ∧
        Λ σ = MState.ofClassical (uliftCoin q) := by
  obtain ⟨T, hT, hT_ne⟩ := exists_effect_exp_val_ne_of_ne ρ σ hne
  let p : Prob := ⟨ρ.exp_val T, ρ.exp_val_prob hT⟩
  let q : Prob := ⟨σ.exp_val T, σ.exp_val_prob hT⟩
  by_cases hpq : (p : ℝ) < q
  · let Λ : CPTPMap d (ULift.{u} (Fin 2)) := (binaryPOVMOfEffectULift T hT).measureDiscard
    exact ⟨p, q, hpq, Λ,
      binaryPOVMOfEffectULift_measureDiscard_apply_eq_uliftCoin T hT ρ p rfl,
      binaryPOVMOfEffectULift_measureDiscard_apply_eq_uliftCoin T hT σ q rfl⟩
  · let T' : HermitianMat d ℂ := 1 - T
    have hT' : 0 ≤ T' ∧ T' ≤ 1 := by
      constructor <;> dsimp [T']
      · exact HermitianMat.zero_le_iff.mpr hT.2
      · rw [sub_le_iff_le_add]
        simpa using hT.1
    let p' : Prob := 1 - p
    let q' : Prob := 1 - q
    have hpq' : (p' : ℝ) < q' := by
      dsimp [p', q']
      rw [Prob.coe_one_minus, Prob.coe_one_minus]
      have hqp : (q : ℝ) < p :=
        lt_of_le_of_ne (le_of_not_gt hpq) (fun heq => hT_ne heq.symm)
      linarith
    let Λ : CPTPMap d (ULift.{u} (Fin 2)) := (binaryPOVMOfEffectULift T' hT').measureDiscard
    refine ⟨p', q', hpq', Λ, ?_, ?_⟩
    · apply binaryPOVMOfEffectULift_measureDiscard_apply_eq_uliftCoin
      dsimp [T', p', p]
      rw [MState.exp_val_sub, MState.exp_val_one, Prob.coe_one_minus]
    · apply binaryPOVMOfEffectULift_measureDiscard_apply_eq_uliftCoin
      dsimp [T', q', q]
      rw [MState.exp_val_sub, MState.exp_val_one, Prob.coe_one_minus]

private theorem dyadicCPTPMapPow_apply_dyadicStatePow
    (Λ : CPTPMap d d₂) (μ : MState d) :
    ∀ m, dyadicCPTPMapPow Λ m (dyadicStatePow μ m) = dyadicStatePow (Λ μ) m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      set_option maxRecDepth 1000 in
      change (dyadicCPTPMapPow Λ m ⊗ᶜᵖ dyadicCPTPMapPow Λ m)
          (dyadicStatePow μ m ⊗ᴹ dyadicStatePow μ m) =
        dyadicStatePow (Λ μ) m ⊗ᴹ dyadicStatePow (Λ μ) m
      have hprod : (dyadicCPTPMapPow Λ m ⊗ᶜᵖ dyadicCPTPMapPow Λ m)
            (dyadicStatePow μ m ⊗ᴹ dyadicStatePow μ m) =
          (dyadicCPTPMapPow Λ m (dyadicStatePow μ m)) ⊗ᴹ
            (dyadicCPTPMapPow Λ m (dyadicStatePow μ m)) := by
        apply MState.ext_m
        change ((dyadicCPTPMapPow Λ m).map.kron (dyadicCPTPMapPow Λ m).map)
            ((dyadicStatePow μ m).m ⊗ₖ (dyadicStatePow μ m).m) =
          ((dyadicCPTPMapPow Λ m).map (dyadicStatePow μ m).m) ⊗ₖ
            ((dyadicCPTPMapPow Λ m).map (dyadicStatePow μ m).m)
        exact MatrixMap.kron_map_of_kron_state (dyadicCPTPMapPow Λ m).map
          (dyadicCPTPMapPow Λ m).map (dyadicStatePow μ m).m (dyadicStatePow μ m).m
      rw [hprod, ih]

private theorem dyadic_binary_zero_of_zero
    (ρ σ : MState d) (p q : Prob) (Λ : CPTPMap d (ULift.{u} (Fin 2)))
    (hzero : f ρ σ = 0)
    (hρ : Λ ρ = MState.ofClassical (uliftCoin p))
    (hσ : Λ σ = MState.ofClassical (uliftCoin q)) :
    ∀ n,
      f (dyadicStatePow (MState.ofClassical (uliftCoin p)) n)
        (dyadicStatePow (MState.ofClassical (uliftCoin q)) n).M = 0 := by
  intro n
  have hle : f (dyadicStatePow (Λ ρ) n) (dyadicStatePow (Λ σ) n).M ≤
      ((2 ^ n : ℕ) : ENNReal) * f ρ σ := calc
    f (dyadicStatePow (Λ ρ) n) (dyadicStatePow (Λ σ) n).M =
        f (dyadicCPTPMapPow Λ n (dyadicStatePow ρ n))
          (dyadicCPTPMapPow Λ n (dyadicStatePow σ n)).M := by
      rw [dyadicCPTPMapPow_apply_dyadicStatePow Λ ρ n,
        dyadicCPTPMapPow_apply_dyadicStatePow Λ σ n]
    _ ≤ f (dyadicStatePow ρ n) (dyadicStatePow σ n).M :=
      DPI _ _ (dyadicCPTPMapPow Λ n)
    _ = ((2 ^ n : ℕ) : ENNReal) * f ρ σ := dyadicStatePow_relEntropy (f := f) ρ σ n
  rw [hzero, mul_zero] at hle
  simpa [hρ, hσ] using le_antisymm hle bot_le

private theorem exists_binary_postprocess {α β s r : Prob}
    (hαs : (α : ℝ) ≤ s) (hsr : (s : ℝ) < r) (hrβ : (r : ℝ) ≤ β) :
    ∃ a b : Prob, Prob.mix α a b = s ∧ Prob.mix β a b = r := by
  let A : ℝ := α
  let B : ℝ := β
  let S : ℝ := s
  let R : ℝ := r
  have hAB : A < B := by dsimp [A, B, S, R] at *; linarith
  let k : ℝ := (R - S) / (B - A)
  have hk_nonneg : 0 ≤ k := by
    dsimp [k]
    exact div_nonneg (sub_nonneg.mpr (by dsimp [S, R]; exact hsr.le))
      (sub_nonneg.mpr hAB.le)
  have hk_le_one : k ≤ 1 := by
    dsimp [k]
    rw [div_le_one (sub_pos.mpr hAB)]
    dsimp [A, B, S, R] at *
    linarith
  let bR : ℝ := S - A * k
  let aR : ℝ := bR + k
  have hbR_nonneg : 0 ≤ bR := by
    dsimp [bR]
    have hAk_le_A : A * k ≤ A * 1 := by
      exact mul_le_mul_of_nonneg_left hk_le_one α.2.1
    dsimp [A, S] at hAk_le_A hαs
    linarith
  have hbR_le_one : bR ≤ 1 := by
    dsimp [bR]
    dsimp [S]
    nlinarith [s.2.2, α.2.1, hk_nonneg]
  have haR_nonneg : 0 ≤ aR := by dsimp [aR]; positivity
  have haR_le_one : aR ≤ 1 := by
    have hden_pos : 0 < B - A := sub_pos.mpr hAB
    have hmain :
        S * (B - A) + (1 - A) * (R - S) ≤ 1 * (B - A) := by
      have hR : R * (1 - A) ≤ B * (1 - A) := by
        refine mul_le_mul_of_nonneg_right ?_ ?_
        · dsimp [R, B] at hrβ ⊢
          exact hrβ
        · dsimp [A]
          linarith [α.2.2]
      have hS : S * (B - 1) ≤ A * (B - 1) := by
        refine mul_le_mul_of_nonpos_right ?_ ?_
        · dsimp [A, S] at hαs ⊢
          exact hαs
        · dsimp [B]
          linarith [β.2.2]
      nlinarith
    have haR_eq :
        aR = (S * (B - A) + (1 - A) * (R - S)) / (B - A) := by
      dsimp [aR, bR, k]
      field_simp [hden_pos.ne']
      ring
    rw [haR_eq, div_le_one hden_pos]
    simpa using hmain
  let a : Prob := ⟨aR, haR_nonneg, haR_le_one⟩
  let b : Prob := ⟨bR, hbR_nonneg, hbR_le_one⟩
  refine ⟨a, b, ?_, ?_⟩
  · apply Subtype.ext
    rw [prob_mix_coe, Prob.coe_one_minus]
    dsimp [a, b, aR, bR, k, A, S]
    ring
  · apply Subtype.ext
    rw [prob_mix_coe, Prob.coe_one_minus]
    dsimp [a, b, aR, bR, k, A, B, S, R]
    field_simp [show (↑β : ℝ) - ↑α ≠ 0 by dsimp [A, B] at hAB; linarith]
    ring

section nontrivial
variable [RelEntropy.Nontrivial f]

private theorem exists_positive_binary_pair :
    ∃ p q : Prob, 0 < (p : ℝ) ∧ (p : ℝ) < q ∧ (q : ℝ) < 1 ∧
      (MState.ofClassical (uliftCoin.{u} p)).M.support = ⊤ ∧
      (MState.ofClassical (uliftCoin.{u} q)).M.support = ⊤ ∧
      0 < f (MState.ofClassical (uliftCoin.{u} p))
        (MState.ofClassical (uliftCoin.{u} q)).M := by
  obtain ⟨s, t, hs0, -, ht0, -, hs_order, hsSupport, htSupport, hpos⟩ :
      ∃ s t : Prob,
        0 < (s : ℝ) ∧ (s : ℝ) < 1 / 2 ∧
        0 < (t : ℝ) ∧ (t : ℝ) < 1 / 2 ∧
        (s : ℝ) < ((1 - t : Prob) : ℝ) ∧
        (MState.ofClassical (uliftCoin s)).M.support = ⊤ ∧
        (MState.ofClassical (uliftCoin (1 - t))).M.support = ⊤ ∧
        0 < f (MState.ofClassical (uliftCoin s))
          (MState.ofClassical (uliftCoin (1 - t))).M := by
    obtain ⟨d, instFintype, instDecidableEq, γ, ω, hγ, hω, hpos⟩ :=
      RelEntropy.Nontrivial.nontrivial (f := f)
    letI : Fintype d := instFintype
    letI : DecidableEq d := instDecidableEq
    obtain ⟨s, t, hs0, hslt, ht0, htlt, hleft, hright⟩ :
        ∃ s t : Prob, 0 < (s : ℝ) ∧ (s : ℝ) < 1 / 2 ∧
          0 < (t : ℝ) ∧ (t : ℝ) < 1 / 2 ∧
          (t : ℝ) • γ.M ≤ (1 - (s : ℝ)) • ω.M ∧
          (s : ℝ) • ω.M ≤ (1 - (t : ℝ)) • γ.M := by
      obtain ⟨s, t, hs0, hs_half, ht0, ht_half, hleft, hright⟩ :
          ∃ s t : ℝ, 0 < s ∧ s < 1 / 2 ∧ 0 < t ∧ t < 1 / 2 ∧
            t • γ.M ≤ (1 - s) • ω.M ∧ s • ω.M ≤ (1 - t) • γ.M := by
        obtain ⟨Nγω, hNγω_pos, hγω⟩ := exists_le_nat_smul_of_fullSupport γ ω hω
        obtain ⟨Nωγ, hNωγ_pos, hωγ⟩ := exists_le_nat_smul_of_fullSupport ω γ hγ
        let K : ℕ := Nat.max Nγω Nωγ
        let a : ℝ := 1 / (K + 2 : ℝ)
        have hden_pos : (0 : ℝ) < K + 2 := by positivity
        have ha_pos : 0 < a := by dsimp [a]; positivity
        have ha_lt_half : a < 1 / 2 := by
          dsimp [a]
          rw [div_lt_iff₀ hden_pos]
          have hK_ge_one : (1 : ℝ) ≤ K := by
            exact_mod_cast le_trans hNγω_pos (le_max_left Nγω Nωγ)
          nlinarith
        have hscaleγω : a * (Nγω + 1 : ℝ) ≤ 1 - a := by
          dsimp [a]
          rw [div_mul_eq_mul_div, one_sub_div hden_pos.ne',
            div_le_div_iff_of_pos_right hden_pos]
          nlinarith [show (Nγω + 1 : ℝ) ≤ K + 1 by
            exact_mod_cast Nat.succ_le_succ (le_max_left Nγω Nωγ)]
        have hscaleωγ : a * (Nωγ + 1 : ℝ) ≤ 1 - a := by
          dsimp [a]
          rw [div_mul_eq_mul_div, one_sub_div hden_pos.ne',
            div_le_div_iff_of_pos_right hden_pos]
          nlinarith [show (Nωγ + 1 : ℝ) ≤ K + 1 by
            exact_mod_cast Nat.succ_le_succ (le_max_right Nγω Nωγ)]
        refine ⟨a, a, ha_pos, ha_lt_half, ha_pos, ha_lt_half, ?_, ?_⟩
        · calc
            a • γ.M ≤ a • ((Nγω + 1 : ℝ) • ω.M) :=
              smul_le_smul_of_nonneg_left hγω ha_pos.le
            _ = (a * (Nγω + 1 : ℝ)) • ω.M := by rw [smul_smul]
            _ ≤ (1 - a) • ω.M := smul_le_smul_of_nonneg_right hscaleγω ω.nonneg
        · calc
            a • ω.M ≤ a • ((Nωγ + 1 : ℝ) • γ.M) :=
              smul_le_smul_of_nonneg_left hωγ ha_pos.le
            _ = (a * (Nωγ + 1 : ℝ)) • γ.M := by rw [smul_smul]
            _ ≤ (1 - a) • γ.M := smul_le_smul_of_nonneg_right hscaleωγ γ.nonneg
      refine ⟨⟨s, hs0.le, (by linarith : s ≤ 1)⟩, ⟨t, ht0.le, (by linarith : t ≤ 1)⟩,
        hs0, hs_half, ht0, ht_half, ?_, ?_⟩
      · simpa using hleft
      · simpa using hright
    have hden : 0 < 1 - (s : ℝ) - (t : ℝ) := by linarith
    let τ : ULift.{u} (Fin 2) → MState d := fun i =>
      if i = ULift.up (0 : Fin 2) then
        binaryPrepOne γ ω (s : ℝ) (t : ℝ) hden hleft
      else
        binaryPrepZero γ ω (s : ℝ) (t : ℝ) hden hright
    let Λ : CPTPMap (ULift.{u} (Fin 2)) d :=
      CPTPMap.CPTP_of_choi_PSD_Tr
        (M := cqPrepareChoi (d := d) τ)
        (cqPrepareChoi_psd (d := d) τ)
        (cqPrepareChoi_traceLeft (d := d) τ)
    have hdenC : (1 - ((s : ℝ) : ℂ) - ((t : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hden.ne'
    have hγprep : Λ (MState.ofClassical (uliftCoin s)) = γ := by
      apply MState.ext_m
      have hγinner : MatrixMap.of_choi_matrix (cqPrepareChoi (d := d) τ)
          (MState.ofClassical (uliftCoin s)).m = γ.m := by
        rw [cqPrepare_apply_uliftCoin, Prob.coe_one_minus]
        ext i j
        simp [τ, binaryPrepOne, binaryPrepZero, MState.m, Matrix.add_apply, Matrix.sub_apply,
          Matrix.smul_apply, -MState.mat_M]
        field_simp [hdenC]
        ring
      simpa [Λ, τ] using hγinner
    have hωprep : Λ (MState.ofClassical (uliftCoin (1 - t))) = ω := by
      apply MState.ext_m
      have hωinner : MatrixMap.of_choi_matrix (cqPrepareChoi (d := d) τ)
          (MState.ofClassical (uliftCoin (1 - t))).m = ω.m := by
        rw [cqPrepare_apply_uliftCoin, Prob.coe_one_minus, Prob.coe_one_minus]
        ext i j
        simp [τ, binaryPrepOne, binaryPrepZero, MState.m, Matrix.add_apply, Matrix.sub_apply,
          Matrix.smul_apply, -MState.mat_M]
        field_simp [hdenC]
        ring
      simpa [Λ, τ] using hωinner
    have hsSupport : (MState.ofClassical (uliftCoin s)).M.support = ⊤ :=
      uliftCoin_support_top s hs0 (by linarith)
    have htSupport : (MState.ofClassical (uliftCoin (1 - t))).M.support = ⊤ :=
      uliftCoin_support_top (1 - t) (by rw [Prob.coe_one_minus]; linarith)
        (by rw [Prob.coe_one_minus]; linarith)
    refine ⟨s, t, hs0, hslt, ht0, htlt, ?_, hsSupport, htSupport, ?_⟩
    · rw [Prob.coe_one_minus]
      linarith
    refine lt_of_lt_of_le hpos ?_
    calc
      f γ ω.M =
          f (Λ (MState.ofClassical (uliftCoin s)))
            (Λ (MState.ofClassical (uliftCoin (1 - t)))).M := by
        rw [hγprep, hωprep]
      _ ≤ f (MState.ofClassical (uliftCoin s))
          (MState.ofClassical (uliftCoin (1 - t))).M := DPI _ _ Λ
  refine ⟨s, 1 - t, hs0, hs_order, ?_, hsSupport, htSupport, hpos⟩
  rw [Prob.coe_one_minus]
  linarith

/-- A nontrivial relative entropy is **faithful**: it can distinguish when two states are equal.

The proof (Tomamichel §5) goes by building a binary measurement that separates `ρ` from `σ`,
using DPI to reduce to a classical `Fin 2` distribution, then amplifying with `of_kron` until the
`Nontrivial` axiom forces a strictly positive value. The tensor-power separation step is formalized
via the finite classical likelihood test in `exists_dyadic_binary_effect_le_ge`. -/
theorem faithful (ρ σ : MState d) : f ρ σ = 0 ↔ ρ = σ := by
  constructor
  · intro hzero
    by_contra hne
    obtain ⟨p, q, hpq, Λ, hρ, hσ⟩ := exists_binary_measurement_of_ne ρ σ hne
    have hzero_binary := dyadic_binary_zero_of_zero (f := f) ρ σ p q Λ hzero hρ hσ
    obtain ⟨s, r, hs_pos, hsr, hr_lt_one, hsSupport, hrSupport, hpos⟩ :=
      exists_positive_binary_pair (f := f)
    obtain ⟨n, T, hT, α, β, hpT, hqT, hαs, hrβ⟩ :=
      exists_dyadic_binary_effect_le_ge p q s r hpq hs_pos hr_lt_one
    have hpos_source : 0 < f (dyadicStatePow (MState.ofClassical (uliftCoin p)) n)
        (dyadicStatePow (MState.ofClassical (uliftCoin q)) n).M := by
      obtain ⟨a, b, hsmix, hrmix⟩ := exists_binary_postprocess hαs hsr hrβ
      let Μ : CPTPMap (DyadicPow (ULift.{u} (Fin 2)) n) (ULift (Fin 2)) :=
        (binaryPOVMOfEffectULift T hT).measureDiscard
      let Λ' : CPTPMap (DyadicPow (ULift.{u} (Fin 2)) n) (ULift (Fin 2)) :=
        (binaryClassicalPostprocess a b) ∘ₘ Μ
      have hρout : Λ' (dyadicStatePow (MState.ofClassical (uliftCoin p)) n) =
          MState.ofClassical (uliftCoin s) := by
        rw [CPTPMap.compose_eq, show Μ (dyadicStatePow (MState.ofClassical (uliftCoin p)) n) =
            MState.ofClassical (uliftCoin α) from
          binaryPOVMOfEffectULift_measureDiscard_apply_eq_uliftCoin
            T hT (dyadicStatePow (MState.ofClassical (uliftCoin p)) n) α hpT,
          binaryClassicalPostprocess_apply, hsmix]
      have hσout : Λ' (dyadicStatePow (MState.ofClassical (uliftCoin q)) n) =
          MState.ofClassical (uliftCoin r) := by
        rw [CPTPMap.compose_eq, show Μ (dyadicStatePow (MState.ofClassical (uliftCoin q)) n) =
            MState.ofClassical (uliftCoin β) from
          binaryPOVMOfEffectULift_measureDiscard_apply_eq_uliftCoin
            T hT (dyadicStatePow (MState.ofClassical (uliftCoin q)) n) β hqT,
          binaryClassicalPostprocess_apply, hrmix]
      refine lt_of_lt_of_le hpos ?_
      calc
        f (MState.ofClassical (uliftCoin s)) (MState.ofClassical (uliftCoin r)).M =
            f (Λ' (dyadicStatePow (MState.ofClassical (uliftCoin p)) n))
              (Λ' (dyadicStatePow (MState.ofClassical (uliftCoin q)) n)).M := by
          rw [hρout, hσout]
        _ ≤ f (dyadicStatePow (MState.ofClassical (uliftCoin p)) n)
              (dyadicStatePow (MState.ofClassical (uliftCoin q)) n).M := DPI _ _ Λ'
    simp [hzero_binary n] at hpos_source
  · rintro rfl
    simp

/-- Positive form of faithfulness: distinct states have strictly positive relative entropy.

This is equivalent to `faithful` because relative entropies are `ENNReal`-valued. -/
theorem faithful_pos_iff_ne (ρ σ : MState d) : 0 < f ρ σ ↔ ρ ≠ σ := by
  rw [ne_eq, ← (faithful (f := f) ρ σ)]
  exact bot_lt_iff_ne_bot

/-- A paper-literal nontrivial relative entropy is nontrivial in every non-one-dimensional
system, once faithfulness is available. This is the full-strength witness previously used as
the `RelEntropy.Nontrivial` axiom. -/
theorem nontrivial_of_two_le_card
    (d : Type u) [Fintype d] [DecidableEq d] (hd : 2 ≤ Fintype.card d) :
    ∃ (ρ σ : MState d), ρ.M.support = ⊤ ∧ σ.M.support = ⊤ ∧ 0 < f ρ σ := by
  obtain ⟨ρ, σ, hρ, hσ, hne⟩ : ∃ (ρ σ : MState d),
      ρ.M.support = ⊤ ∧ σ.M.support = ⊤ ∧ ρ ≠ σ := by
    haveI : Nonempty d := Fintype.card_pos_iff.mp (lt_of_lt_of_le (by norm_num) hd)
    let i : d := Classical.arbitrary d
    let p : Prob := ⟨1 / 2, by norm_num⟩
    let ρ : MState d := p [MState.ofClassical (.constant i) ↔ MState.uniform]
    refine ⟨ρ, MState.uniform, ?_, ?_, ?_⟩
    · haveI : ρ.M.NonSingular := HermitianMat.nonSingular_of_posDef <| by
        dsimp [ρ]
        exact MState.PosDef_mix_of_ne_one (hσ₂ := MState.uniform_posDef) p
          (by dsimp [p]; norm_num [Prob.ext_iff])
      exact HermitianMat.nonSingular_support_top
    · haveI : (MState.uniform : MState d).M.NonSingular :=
        HermitianMat.nonSingular_of_posDef MState.uniform_posDef
      exact HermitianMat.nonSingular_support_top
    · intro hρσ
      have hmat := congrArg (fun τ : MState d => τ.M.mat) hρσ
      simp [ρ, p, Mixable.mix, Mixable.mix_ab, MState.instMixable,
        MState.uniform, MState.ofClassical, ProbDistribution.constant_eq,
        ProbDistribution.uniform_def, HermitianMat.diagonal, Mixable.to_U] at hmat
      have hdiag_re := congrArg Complex.re (congrFun (congrFun hmat i) i)
      simp [Matrix.add_apply] at hdiag_re
      norm_num at hdiag_re
      have hinv_lt_one : ((Fintype.card d : ℝ))⁻¹ < 1 :=
        inv_lt_one_of_one_lt₀
          (by exact_mod_cast (lt_of_lt_of_le one_lt_two hd) : (1 : ℝ) < Fintype.card d)
      nlinarith
  exact ⟨ρ, σ, hρ, hσ, (faithful_pos_iff_ne (f := f) ρ σ).mpr hne⟩

end nontrivial


private theorem le_of_le_exp (ρ σ : MState d) {x : ℝ}
    (hx : 0 ≤ x) (h : ρ.M ≤ Real.exp x • σ.M) :
    f ρ σ.M ≤ ENNReal.ofReal x := by
  have hfin : f ρ σ.M ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top <|
      integer_bound_aux (f := f) (N := Nat.ceil (Real.exp x)) ρ σ <| by
      refine h.trans ?_
      refine smul_le_smul_of_nonneg_right ?_ σ.nonneg
      exact (Nat.le_ceil _).trans (by norm_num)
  by_contra hfx
  have hfx' : ENNReal.ofReal x < f ρ σ.M := lt_of_not_ge hfx
  let δ : ℝ := (f ρ σ.M).toReal - x
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith [(ENNReal.ofReal_lt_iff_lt_toReal hx hfin).1 hfx']
  let n : ℕ := Nat.ceil (Real.log 3 / δ) + 1
  have hgap : Real.log 3 < (((2 ^ n : ℕ) : ℝ)) * δ := by
    apply (div_lt_iff₀ hδ).mp
    exact lt_of_lt_of_le
      (show Real.log 3 / δ < (n : ℝ) by
        dsimp [n]
        exact lt_of_le_of_lt (Nat.le_ceil (Real.log 3 / δ))
          (by exact_mod_cast Nat.lt_succ_self (Nat.ceil (Real.log 3 / δ))))
      (by exact_mod_cast ((Nat.lt_two_pow_self : n < 2 ^ n).le) : (n : ℝ) ≤ (2 ^ n : ℕ))
  let y : ℝ := (((2 ^ n : ℕ) : ℝ)) * x
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]; positivity
  have hpow_le : ∀ m, (dyadicStatePow ρ m).M ≤
      Real.exp ((((2 ^ m : ℕ) : ℝ)) * x) • (dyadicStatePow σ m).M := by
    intro m
    induction m with
    | zero =>
        simpa [dyadicStatePow] using h
    | succ m ih =>
        have hσ_nonneg :
            0 ≤ Real.exp ((((2 ^ m : ℕ) : ℝ)) * x) • (dyadicStatePow σ m).M :=
          smul_nonneg (by positivity) (dyadicStatePow σ m).nonneg
        have hpow :
            ((((2 ^ (m + 1) : ℕ) : ℝ)) * x) =
              ((((2 ^ m : ℕ) : ℝ)) * x) + ((((2 ^ m : ℕ) : ℝ)) * x) := by
          rw [pow_succ, Nat.cast_mul]
          ring
        have hunfold : (dyadicStatePow ρ (m + 1)).M
            = (dyadicStatePow ρ m).M ⊗ₖ (dyadicStatePow ρ m).M := rfl
        have hrhs : Real.exp (((((2 ^ m : ℕ) : ℝ)) * x) + ((((2 ^ m : ℕ) : ℝ)) * x)) •
              (dyadicStatePow σ (m + 1)).M
            = (Real.exp ((((2 ^ m : ℕ) : ℝ)) * x) • (dyadicStatePow σ m).M) ⊗ₖ
              (Real.exp ((((2 ^ m : ℕ) : ℝ)) * x) • (dyadicStatePow σ m).M) := by
          simpa [dyadicStatePow, MState.prod, Real.exp_add] using
            (smul_kronecker (Real.exp ((((2 ^ m : ℕ) : ℝ)) * x))
                (Real.exp ((((2 ^ m : ℕ) : ℝ)) * x))
                (dyadicStatePow σ m).M (dyadicStatePow σ m).M).symm
        rw [hunfold, hpow, hrhs]
        rw [← sub_nonneg]
        let A : HermitianMat (DyadicPow d m) ℂ := (dyadicStatePow ρ m).M
        let B : HermitianMat (DyadicPow d m) ℂ :=
          Real.exp ((((2 ^ m : ℕ) : ℝ)) * x) • (dyadicStatePow σ m).M
        have hAB : A ≤ B := ih
        have hA : 0 ≤ A := (dyadicStatePow ρ m).nonneg
        have hB : 0 ≤ B := hσ_nonneg
        change 0 ≤ B ⊗ₖ B - A ⊗ₖ A
        have hAB_add : A + (B - A) = B := by abel
        have hnegC : A ⊗ₖ (-A) = -(A ⊗ₖ A) := by
          ext1
          simpa using (Matrix.kronecker_smul (-1 : ℂ) A.mat A.mat)
        have hAC : A ⊗ₖ B + -(A ⊗ₖ A) = A ⊗ₖ (B - A) := by
          calc
            A ⊗ₖ B + -(A ⊗ₖ A) = A ⊗ₖ B + A ⊗ₖ (-A) := by rw [hnegC]
            _ = A ⊗ₖ (B + -A) := by
                  simpa using (HermitianMat.kronecker_add (A := A) (B := B) (C := -A)).symm
            _ = A ⊗ₖ (B - A) := by rw [sub_eq_add_neg]
        have hEq : B ⊗ₖ B - A ⊗ₖ A = A ⊗ₖ (B - A) + (B - A) ⊗ₖ B := by
          calc
            B ⊗ₖ B - A ⊗ₖ A = (A + (B - A)) ⊗ₖ B - A ⊗ₖ A := by rw [hAB_add]
            _ = (A ⊗ₖ B + (B - A) ⊗ₖ B) - A ⊗ₖ A := by rw [HermitianMat.add_kronecker]
            _ = (A ⊗ₖ B + -(A ⊗ₖ A)) + (B - A) ⊗ₖ B := by abel
            _ = A ⊗ₖ (B - A) + (B - A) ⊗ₖ B := by rw [hAC]
        rw [hEq]
        exact add_nonneg
          (HermitianMat.kronecker_nonneg hA (sub_nonneg.mpr hAB))
          (HermitianMat.kronecker_nonneg (sub_nonneg.mpr hAB) hB)
  have hpow_bound' :
      (((2 ^ n : ℕ) : ENNReal) * f ρ σ.M) ≤
        ENNReal.ofReal (Real.log (Nat.ceil (Real.exp y) + 1)) := by
    simpa [dyadicStatePow_relEntropy (f := f) ρ σ n] using
      integer_bound_aux (f := f) (N := Nat.ceil (Real.exp y))
        (dyadicStatePow ρ n) (dyadicStatePow σ n) (by
          refine (hpow_le n).trans ?_
          refine smul_le_smul_of_nonneg_right ?_ (dyadicStatePow σ n).nonneg
          dsimp [y]
          exact (Nat.le_ceil _).trans (by norm_num))
  have hpow_bound_real :
      (((2 ^ n : ℕ) : ℝ)) * (f ρ σ.M).toReal ≤
        Real.log (Nat.ceil (Real.exp y) + 1 : ℝ) := by
    calc
      (((2 ^ n : ℕ) : ℝ)) * (f ρ σ.M).toReal
          = ((((2 ^ n : ℕ) : ENNReal) * f ρ σ.M)).toReal := by
              rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
      _ ≤ (ENNReal.ofReal (Real.log (Nat.ceil (Real.exp y) + 1 : ℝ))).toReal :=
        (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (by simp) hfin) ENNReal.ofReal_ne_top).2 hpow_bound'
      _ = Real.log (Nat.ceil (Real.exp y) + 1 : ℝ) := by
              rw [ENNReal.toReal_ofReal (Real.log_nonneg (by norm_num))]
  have hlog_upper : Real.log (Nat.ceil (Real.exp y) + 1 : ℝ) ≤ y + Real.log 3 := by
    have hceille : (Nat.ceil (Real.exp y) + 1 : ℝ) ≤ 3 * Real.exp y := by
      nlinarith [(Nat.ceil_lt_add_one (Real.exp_nonneg y)).le,
        (show (1 : ℝ) ≤ Real.exp y by simpa [Real.one_le_exp_iff] using hy_nonneg)]
    linarith [Real.log_le_log (by positivity) hceille,
      show Real.log (3 * Real.exp y) = Real.log 3 + y by
        rw [Real.log_mul (by positivity : (3 : ℝ) ≠ 0) (Real.exp_pos y).ne', Real.log_exp]]
  have hlower :
      y + Real.log 3 < (((2 ^ n : ℕ) : ℝ)) * (f ρ σ.M).toReal := by
    dsimp [y, δ] at hgap
    nlinarith
  linarith

/-- The relative max-entropy is a lower bound on all relative entropies. -/
theorem le_max (ρ σ : MState d) : f ρ σ.M ≤ max ρ σ.M := by
  by_cases hx : ∃ x : ℝ, ρ.M ≤ Real.exp x • σ.M
  · have hmax_fin : max ρ σ.M ≠ ∞ := by
      simp [max, hx]
    obtain ⟨x, hx⟩ := hx
    let y : ℝ := Max.max x 0
    have hy0 : 0 ≤ y := by simp [y]
    have hy : ρ.M ≤ Real.exp y • σ.M := by
      exact hx.trans (smul_le_smul_of_nonneg_right
        (Real.exp_le_exp.mpr (show x ≤ y by dsimp [y]; exact le_max_left _ _)) σ.nonneg)
    have hfin : f ρ σ.M ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_of_le_exp (f := f) ρ σ hy0 hy)
    have htoReal :
        (f ρ σ.M).toReal ≤ (max ρ σ.M).toReal := by
      rw [RelEntropy.toReal_max (ρ := ρ) (σ := σ.M)]
      let S : Set ℝ := ((↑) '' {x : ℝ≥0 | ρ.M ≤ Real.exp x • σ.M})
      have hS_nonempty : S.Nonempty := by
        refine ⟨(⟨y, hy0⟩ : ℝ≥0), ?_⟩
        exact ⟨⟨y, hy0⟩, hy, rfl⟩
      refine le_csInf hS_nonempty ?_
      intro a ha
      rcases ha with ⟨z, hz, rfl⟩
      have hbound := le_of_le_exp (f := f) ρ σ z.2 hz
      simpa [ENNReal.toReal_ofReal z.2] using
        (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).2 hbound
    exact (ENNReal.toReal_le_toReal hfin hmax_fin).1 htoReal
  · simp [max, hx]

end bounds

end RelEntropy

/-- The axioms for a well-behaved quantum entropy: it vanishes on pure states and is additive
under tensor products. Captures the common features of the von Neumann, min-, max-, and α-Renyi
entropies. -/
class Entropy (f : ∀ {d : Type u} [Fintype d] [DecidableEq d], MState d → ℝ≥0) where
  /-- The entropy of a pure state is zero -/
  of_const {d : Type u} [Fintype d] [DecidableEq d] (ψ : Ket d) : f (.pure ψ) = 0
  /-- Entropy is additive under tensor products -/
  of_kron {d₁ d₂ : Type u} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂] :
    ∀ (ρ : MState d₁) (σ : MState d₂), f (ρ ⊗ᴹ σ) = f ρ + f σ
  -- /-- Entropy is convex. TODO def? Or do we even need this? -/
  -- convex : True := by trivial
