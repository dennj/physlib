/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Finite.Entropy.Relative
public import QuantumInfo.Finite.CPTPMap.Dual
public import QuantumInfo.ForMathlib.Matrix
public import QuantumInfo.ForMathlib.HermitianMat.Sqrt
public import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

@[expose] public section

noncomputable section

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]
variable {dA dB dC dA₁ dA₂ : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α : ℝ} {ρ σ : MState d}

open scoped InnerProductSpace RealInnerProductSpace HermitianMat

/-!
# DPI (Data Processing Inequality)

The Data Processing Inequality (DPI) for the sandwiched Rényi relative entropy, and
as a consequence, the quantum relative entropy.
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra
open BigOperators

/-- The weighted norm \|X\|_{p, σ} defined in the paper. -/
noncomputable def weighted_norm (p : ℝ) (σ : MState d) (X : Matrix d d ℂ) : ℝ :=
  let σ_pow : HermitianMat d ℂ := σ.M.cfc (fun x => x ^ (1 / (2 * p)))
  schattenNorm (σ_pow.mat * X * σ_pow.mat) p

/-- The weighted norm for p = \infty. -/
noncomputable def weighted_norm_infty (_ : MState d) (X : Matrix d d ℂ) : ℝ :=
  ‖X‖

/-- The map Γ_σ(X) = σ^{1/2} X σ^{1/2}. -/
noncomputable def Gamma (σ : MState d) (X : Matrix d d ℂ) : Matrix d d ℂ :=
  let σ_half : HermitianMat d ℂ := σ.M.cfc (fun x => x ^ (1/2 : ℝ))
  σ_half.mat * X * σ_half.mat

/-- The inverse map Γ_σ^{-1}(X) = σ^{-1/2} X σ^{-1/2}. -/
noncomputable def Gamma_inv (σ : MState d) (X : Matrix d d ℂ) : Matrix d d ℂ :=
  let σ_inv_half : HermitianMat d ℂ := σ.M.cfc (fun x => x ^ (-1/2 : ℝ))
  σ_inv_half.mat * X * σ_inv_half.mat

/-- The operator T = Γ_{Φ(σ)}^{-1} ∘ Φ ∘ Γ_σ. -/
noncomputable def T_op (Φ : CPTPMap d d₂) (σ : MState d) (X : Matrix d d ℂ) : Matrix d₂ d₂ ℂ :=
  Gamma_inv (Φ σ) (Φ.map (Gamma σ X))

/-- The induced norm of a map Ψ: M_d -> M_d2 with respect to weighted norms. -/
noncomputable def induced_norm (p : ℝ) (σ : MState d) (Φ : CPTPMap d d₂) (Ψ : Matrix d d ℂ → Matrix d₂ d₂ ℂ) : ℝ :=
  sSup { weighted_norm p (Φ σ) (Ψ X) / weighted_norm p σ X | (X : Matrix d d ℂ) (_ : weighted_norm p σ X ≠ 0) }

/-
The operator T = Γ_{Φ(σ)}^{-1} ∘ Φ ∘ Γ_σ as a linear map.
-/
noncomputable def T_map (σ : MState d) (Φ : CPTPMap d d₂) : MatrixMap d d₂ ℂ :=
  { toFun := fun X => T_op Φ σ X,
    map_add' := fun X Y => by
      unfold T_op Gamma Gamma_inv
      simp [Matrix.mul_add, Matrix.add_mul]
    map_smul' := fun c X => by
      unfold T_op
      simp
      unfold Gamma Gamma_inv
      simp [mul_assoc]
  }

/-
Gamma_map is the conjugation by the square root of sigma.
-/
noncomputable def Gamma_map (σ : MState d) : MatrixMap d d ℂ :=
  MatrixMap.conj (σ.M.cfc (fun x => x ^ (1/2 : ℝ))).mat

lemma Gamma_map_eq (σ : MState d) (X : Matrix d d ℂ) :
    Gamma_map σ X = Gamma σ X := by
  ext; simp [ Gamma_map, Gamma ]
  apply_rules [ IsSelfAdjoint.cfc ]

/-
Gamma_map is completely positive.
-/
lemma Gamma_map_CP (σ : MState d) : (Gamma_map σ).IsCompletelyPositive :=
  MatrixMap.conj_isCompletelyPositive _

/-
Gamma_inv_map is the conjugation by the inverse square root of sigma.
-/
noncomputable def Gamma_inv_map (σ : MState d) : MatrixMap d d ℂ :=
  MatrixMap.conj (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat

lemma Gamma_inv_map_eq (σ : MState d) (X : Matrix d d ℂ) :
    Gamma_inv_map σ X = Gamma_inv σ X := by
  simp [Gamma_inv_map, Gamma_inv]
  congr
  apply IsSelfAdjoint.cfc

/-
The inverse square root of sigma.
-/
noncomputable def sigma_inv_sqrt (σ : MState d) : Matrix d d ℂ :=
  (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat

/-
Gamma_inv_map is completely positive.
-/
lemma Gamma_inv_map_CP (σ : MState d) : (Gamma_inv_map σ).IsCompletelyPositive :=
  MatrixMap.conj_isCompletelyPositive _

/-
T_map is the composition of Gamma_inv_map, Phi, and Gamma_map.
-/
lemma T_map_eq_comp (σ : MState d) (Φ : CPTPMap d d₂) :
    T_map σ Φ = (Gamma_inv_map (Φ σ)).comp (Φ.map.comp (Gamma_map σ)) := by
  ext
  unfold T_map
  simp [T_op]
  congr! 1
  · exact funext fun x => Gamma_inv_map_eq ( Φ σ ) x ▸ rfl
  · rw [ Gamma_map_eq ]

/-
T_map is completely positive.
-/
lemma T_is_CP (σ : MState d) (Φ : CPTPMap d d₂) :
    (T_map σ Φ).IsCompletelyPositive := by
  rw [T_map_eq_comp]
  exact (Gamma_map_CP σ |>.comp Φ.cp).comp (Gamma_inv_map_CP (Φ σ))

/-
The weighted 1-norm of X is the trace norm of Gamma(X).
-/
lemma weighted_norm_one_eq_trace_norm_Gamma (σ : MState d) (X : Matrix d d ℂ) :
    weighted_norm 1 σ X = schattenNorm (Gamma σ X) 1 := by
  unfold weighted_norm Gamma
  norm_num

/-
Multiplication property for HermitianMat functional calculus.
-/
lemma HermitianMat.cfc_mul {d : Type*} [Fintype d] [DecidableEq d]
    (A : HermitianMat d ℂ) (f g : ℝ → ℝ) :
    (A.cfc f).mat * (A.cfc g).mat = (A.cfc (fun x => f x * g x)).mat :=
  (mat_cfc_mul A f g).symm

/-
Gamma of identity is sigma.
-/
lemma Gamma_one (σ : MState d) : Gamma σ 1 = σ.M.mat := by
  have h_gamma_one : (σ.M.cfc (fun x => x^(1/2 : ℝ))).mat * (σ.M.cfc (fun x => x^(1/2 : ℝ))).mat = σ.M.cfc (fun x => x^(1/2 : ℝ) * x^(1/2 : ℝ)) := by
    symm
    exact HermitianMat.mat_cfc_mul σ.M ( fun x => x ^ ( 1 / 2 : ℝ ) ) ( fun x => x ^ ( 1 / 2 : ℝ ) )
  convert h_gamma_one using 1
  · unfold Gamma; aesop
  · norm_num [ ← Real.sqrt_eq_rpow, Real.sqrt_mul_self ( show 0 ≤ _ from _ ) ]
    have h_gamma_one : ∀ x ∈ spectrum ℝ σ.m, Real.sqrt x * Real.sqrt x = x := by
      intro x hx; rw [ Real.mul_self_sqrt ] ; exact (by
      rw [ spectrum.mem_iff ] at hx
      exact Matrix.PosSemidef.pos_of_mem_spectrum σ.psd x hx)
    rw [ cfc ]
    split_ifs <;> simp_all
    · convert rfl
      convert cfcHom_id _
      ext x; aesop
    · exact False.elim ( ‹IsSelfAdjoint σ.m → ¬ContinuousOn ( fun x => Real.sqrt x * Real.sqrt x ) ( spectrum ℝ σ.m ) › σ.M.prop <| ContinuousOn.mul ( Real.continuous_sqrt.continuousOn ) ( Real.continuous_sqrt.continuousOn ) )

/-
Gamma inverse of sigma is identity.
-/
lemma Gamma_inv_self (σ : MState d) (hσ : σ.m.PosDef) :
    Gamma_inv σ σ.M.mat = 1 := by
  -- We use `HermitianMat.cfc_mul` and the fact that $x^{-1/2} * x * x^{-1/2} = 1$ for $x > 0$.
  have h_gamma_inv_sigma : (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat * (σ.M.mat) * (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat = (σ.M.cfc (fun x => x ^ (-1/2 : ℝ) * x * x ^ (-1/2 : ℝ))).mat := by
    have h_gamma_inv_sigma : (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat * (σ.M.cfc id).mat * (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat = (σ.M.cfc (fun x => x ^ (-1/2 : ℝ) * x * x ^ (-1/2 : ℝ))).mat := by
      have h_gamma_inv_sigma : ∀ (f g h : ℝ → ℝ), ContinuousOn f (spectrum ℝ σ.M.mat) → ContinuousOn g (spectrum ℝ σ.M.mat) → ContinuousOn h (spectrum ℝ σ.M.mat) → (σ.M.cfc f).mat * (σ.M.cfc g).mat * (σ.M.cfc h).mat = (σ.M.cfc (fun x => f x * g x * h x)).mat := by
        intro f g h hf hg hh
        have h_gamma_inv_sigma : (σ.M.cfc f).mat * (σ.M.cfc g).mat = (σ.M.cfc (fun x => f x * g x)).mat := by
          symm
          convert HermitianMat.mat_cfc_mul σ.M f g using 1
        rw [ h_gamma_inv_sigma, ← HermitianMat.mat_cfc_mul ]
        congr! 2
      have h : ∀ x ∈ spectrum ℝ σ.M.mat, x ≠ 0 := by
        norm_num
        intro x hx h_zero
        have h_eigenvalue : ∃ v : d → ℂ, v ≠ 0 ∧ σ.m.mulVec v = x • v := by
          simp_all [ spectrum.mem_iff]
          contrapose! hx
          exact Matrix.PosDef.isUnit hσ
        obtain ⟨ v, hv_ne_zero, hv_eigenvalue ⟩ := h_eigenvalue
        rw [Matrix.posDef_iff_dotProduct_mulVec] at hσ
        have := hσ.2 hv_ne_zero
        simp [hv_eigenvalue, h_zero] at this
      apply h_gamma_inv_sigma
      · fun_prop
      · fun_prop
      · fun_prop
    convert h_gamma_inv_sigma using 1
    ext i j ; simp [ Matrix.mul_apply]
  -- Since $x^{-1/2} * x * x^{-1/2} = 1$ for $x > 0$, we have $(σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat * (σ.M.mat) * (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat = (σ.M.cfc (fun x => 1)).mat$.
  have h_gamma_inv_sigma_simplified : (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat * (σ.M.mat) * (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat = (σ.M.cfc (fun x => 1)).mat := by
    convert h_gamma_inv_sigma using 1
    congr! 1
    -- Since $x^{-1/2} * x * x^{-1/2} = 1$ for all $x > 0$, the functions are equal.
    have h_eq : ∀ x : ℝ, 0 < x → x ^ (-1 / 2 : ℝ) * x * x ^ (-1 / 2 : ℝ) = 1 := by
      intro x hx
      ring_nf
      norm_num [ hx.ne' ]
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul hx.le ] ; norm_num [ hx.ne' ]
      rw [ Real.rpow_neg_one, inv_mul_cancel₀ hx.ne' ]
    exact Eq.symm (HermitianMat.cfc_congr_of_posDef hσ h_eq)
  convert h_gamma_inv_sigma_simplified using 1
  ext i j
  simp

lemma Gamma_inv_self_supportProj (σ : MState d) :
    Gamma_inv σ σ.M.mat = σ.M.supportProj.mat := by
  change ((σ.M.cfc (fun x => x ^ (-1 / 2 : ℝ))).mat * σ.M.mat *
      (σ.M.cfc (fun x => x ^ (-1 / 2 : ℝ))).mat) = σ.M.supportProj.mat
  rw [show σ.M.mat = (σ.M.cfc id).mat by simp]
  rw [← HermitianMat.mat_cfc_mul σ.M (fun x => x ^ (-1 / 2 : ℝ)) id]
  have hmul :
      (σ.M.cfc ((fun x => x ^ (-1 / 2 : ℝ)) * id)).mat =
        (σ.M.cfc (fun x => x ^ (-1 / 2 : ℝ) * x)).mat := by
    rfl
  rw [hmul]
  rw [← HermitianMat.mat_cfc_mul σ.M (fun x => x ^ (-1 / 2 : ℝ) * x)
    (fun x => x ^ (-1 / 2 : ℝ))]
  rw [HermitianMat.supportProj_eq_cfc]
  congr 1
  apply HermitianMat.cfc_congr_of_nonneg σ.nonneg
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  · simp [hx0]
    have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    nth_rw 2 [← Real.rpow_one x]
    rw [← Real.rpow_add hxpos (-1 / 2 : ℝ) 1]
    norm_num
    rw [← Real.rpow_add hxpos (1 / 2 : ℝ) (-(1 / 2 : ℝ))]
    norm_num

/-
The matrix of the output state is the map applied to the input matrix.
-/
lemma CPTPMap_apply_MState_M (Φ : CPTPMap d d₂) (σ : MState d) :
    (Φ σ).M.mat = Φ.map σ.M.mat := rfl

theorem T_map_supportProj (σ : MState d) (Φ : CPTPMap d d₂) :
    (T_map σ Φ) 1 = (Φ σ).M.supportProj.mat := by
  dsimp [T_map, T_op]; rw [Gamma_one, ← CPTPMap_apply_MState_M, Gamma_inv_self_supportProj]

/-
Gamma composed with Gamma inverse is identity.
-/
lemma Gamma_Gamma_inv (σ : MState d) (hσ : σ.m.PosDef) (X : Matrix d d ℂ) :
    Gamma σ (Gamma_inv σ X) = X := by
  -- By definition of Gamma and Gamma_inv, we can simplify the expression.
  have h_simp : (σ.M.cfc (fun x => x ^ (1 / 2 : ℝ))).mat * (σ.M.cfc (fun x => x ^ (-1 / 2 : ℝ))).mat = 1 := by
    symm
    convert HermitianMat.mat_cfc_mul _ _ _ using 1
    · have h_gamma_gamma_inv : ∀ x ∈ spectrum ℝ σ.M.mat, x ^ (1 / 2 : ℝ) * x ^ (-1 / 2 : ℝ) = 1 := by
        intro x hx
        have hx_pos : 0 < x := by
          have := (Matrix.posDef_iff_dotProduct_mulVec.mp hσ).2
          obtain ⟨v, hv⟩ : ∃ v : d → ℂ, v ≠ 0 ∧ σ.m.mulVec v = x • v := by
            rw [ spectrum.mem_iff ] at hx
            simp_all [ Matrix.isUnit_iff_isUnit_det ]
            obtain ⟨ v, hv ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hx
            simp_all [ sub_eq_iff_eq_add, Matrix.sub_mulVec ]
            exact ⟨ v, hv.1, hv.2.symm.trans ( by ext i; erw [ Matrix.mulVec_diagonal ] ; aesop ) ⟩
          specialize this hv.1
          simp_all [ dotProduct]
          simp_all [ mul_assoc, mul_comm]
          simp_all [ mul_left_comm ( v _ ), Complex.mul_conj, Complex.normSq_eq_norm_sq ]
          norm_cast at this
          exact lt_of_not_ge fun hx' => this.not_ge <| Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg hx' <| sq_nonneg _
        rw [ ← Real.rpow_add hx_pos ] ; norm_num
      rw [HermitianMat.cfc_congr (g := fun x ↦ 1)]
      · rw [ HermitianMat.cfc_const ]
        norm_num
      · exact fun x hx => h_gamma_gamma_inv x hx
  unfold Gamma Gamma_inv; simp_all [ ← mul_assoc ]
  simp_all [ mul_assoc, mul_eq_one_comm.mp h_simp ]

lemma Gamma_Gamma_inv_supportProj (σ : MState d) (X : Matrix d d ℂ) :
    Gamma σ (Gamma_inv σ X) = σ.M.supportProj.mat * X * σ.M.supportProj.mat := by
  have hleft :
      (σ.M.cfc (fun x => x ^ (1 / 2 : ℝ))).mat *
          (σ.M.cfc (fun x => x ^ (-(1 / 2 : ℝ)))).mat = σ.M.supportProj.mat := by
    simpa [HermitianMat.rpow_eq_cfc] using
      (HermitianMat.rpow_neg_mul_rpow_eq_supportProj
        (A := σ.M) σ.nonneg (p := (- (1 / 2 : ℝ))) (by norm_num))
  have hright :
      (σ.M.cfc (fun x => x ^ (-(1 / 2 : ℝ)))).mat *
          (σ.M.cfc (fun x => x ^ (1 / 2 : ℝ))).mat = σ.M.supportProj.mat := by
    simpa [HermitianMat.rpow_eq_cfc] using
      (HermitianMat.rpow_neg_mul_rpow_eq_supportProj
        (A := σ.M) σ.nonneg (p := (1 / 2 : ℝ)) (by norm_num))
  have hneg_half :
      (σ.M.cfc (fun x => x ^ (-1 / 2 : ℝ))).mat =
        (σ.M.cfc (fun x => x ^ (-(1 / 2 : ℝ)))).mat := by congr 1; ext x; norm_num
  unfold Gamma Gamma_inv
  calc _ = ((σ.M.cfc (fun x => x ^ (1 / 2 : ℝ))).mat *
            (σ.M.cfc (fun x => x ^ (-1 / 2 : ℝ))).mat) *
          X *
          ((σ.M.cfc (fun x => x ^ (-1 / 2 : ℝ))).mat *
            (σ.M.cfc (fun x => x ^ (1 / 2 : ℝ))).mat) := by simp [Matrix.mul_assoc]
    _ = _ := by rw [hneg_half, hleft, hright]

private lemma Gamma_T_map_eq_compression (σ : MState d) (Φ : CPTPMap d d₂)
    (X : Matrix d d ℂ) :
    Gamma (Φ σ) ((T_map σ Φ) X) =
      (Φ σ).M.supportProj.mat * Φ.map (Gamma σ X) * (Φ σ).M.supportProj.mat := by
  unfold T_map T_op
  simpa using Gamma_Gamma_inv_supportProj (σ := Φ σ) (X := Φ.map (Gamma σ X))

private def spectralProj (A : HermitianMat d ℂ) (i : d) : Matrix d d ℂ :=
  A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose

private def supportCpow (A : HermitianMat d ℂ) (z : ℂ) : Matrix d d ℂ :=
  ∑ i, (if A.H.eigenvalues i = 0 then 0 else ((A.H.eigenvalues i : ℂ) ^ z)) • spectralProj A i

private lemma spectralProj_mul (A : HermitianMat d ℂ) (i j : d) :
    spectralProj A i * spectralProj A j = if i = j then spectralProj A i else 0 := by
  classical
  unfold spectralProj
  have hU :
      A.H.eigenvectorUnitary.val.conjTranspose * A.H.eigenvectorUnitary.val =
        (1 : Matrix d d ℂ) := by
    simp [Matrix.IsHermitian.eigenvectorUnitary]
  by_cases hij : i = j
  · subst j
    calc
      A.H.eigenvectorUnitary.val * Matrix.single i i 1 * A.H.eigenvectorUnitary.val.conjTranspose *
          (A.H.eigenvectorUnitary.val * Matrix.single i i 1 * A.H.eigenvectorUnitary.val.conjTranspose)
        = A.H.eigenvectorUnitary.val *
            (Matrix.single i i 1 * (A.H.eigenvectorUnitary.val.conjTranspose *
              A.H.eigenvectorUnitary.val) * Matrix.single i i 1) *
            A.H.eigenvectorUnitary.val.conjTranspose := by
              simp [Matrix.mul_assoc]
      _ = A.H.eigenvectorUnitary.val *
            (Matrix.single i i 1 * Matrix.single i i 1) *
            A.H.eigenvectorUnitary.val.conjTranspose := by
              simp [hU, Matrix.mul_assoc]
      _ = spectralProj A i := by
            simp [spectralProj, Matrix.mul_assoc]
      _ = if i = i then spectralProj A i else 0 := by simp
  · calc
      A.H.eigenvectorUnitary.val * Matrix.single i i 1 * A.H.eigenvectorUnitary.val.conjTranspose *
          (A.H.eigenvectorUnitary.val * Matrix.single j j 1 * A.H.eigenvectorUnitary.val.conjTranspose)
        = A.H.eigenvectorUnitary.val *
            (Matrix.single i i 1 * (A.H.eigenvectorUnitary.val.conjTranspose *
              A.H.eigenvectorUnitary.val) * Matrix.single j j 1) *
            A.H.eigenvectorUnitary.val.conjTranspose := by
              simp [Matrix.mul_assoc]
      _ = A.H.eigenvectorUnitary.val *
            (Matrix.single i i 1 * Matrix.single j j 1) *
            A.H.eigenvectorUnitary.val.conjTranspose := by
              simp [hU, Matrix.mul_assoc]
      _ = A.H.eigenvectorUnitary.val * 0 * A.H.eigenvectorUnitary.val.conjTranspose := by
            ext a b
            simp [Matrix.mul_apply, hij]
      _ = 0 := by simp
      _ = if i = j then spectralProj A i else 0 := by simp [hij]

private lemma supportCpow_zero (A : HermitianMat d ℂ) :
    supportCpow A 0 = A.supportProj.mat := by
  classical
  unfold supportCpow spectralProj
  rw [A.supportProj_eq_cfc]
  rw [HermitianMat.cfc_toMat_eq_sum_smul_proj]
  congr! 1 with i
  by_cases h : A.H.eigenvalues i = 0 <;> simp [h]

private lemma supportCpow_ofReal
    (A : HermitianMat d ℂ) (hA : 0 ≤ A) {r : ℝ} (hr : 0 < r) :
    supportCpow A (r : ℂ) = (A ^ r).mat := by
  classical
  unfold supportCpow
  rw [HermitianMat.rpow_eq_cfc, HermitianMat.cfc_toMat_eq_sum_smul_proj]
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases h0 : A.H.eigenvalues i = 0
  · simp [h0, spectralProj, hr.ne']
  · have hnn : 0 ≤ A.H.eigenvalues i :=
      (HermitianMat.zero_le_iff.mp hA).eigenvalues_nonneg i
    simp [h0, spectralProj]
    rw [← Complex.ofReal_cpow hnn r]
    rfl

private lemma supportCpow_ofReal_ne_zero (A : HermitianMat d ℂ) (hA : 0 ≤ A) {r : ℝ}
    (hr : r ≠ 0) :
    supportCpow A (r : ℂ) = (A ^ r).mat := by
  classical
  unfold supportCpow
  rw [HermitianMat.rpow_eq_cfc, HermitianMat.cfc_toMat_eq_sum_smul_proj]
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases h0 : A.H.eigenvalues i = 0
  · simp [h0, spectralProj, Real.zero_rpow hr]
  · have hnn : 0 ≤ A.H.eigenvalues i :=
      (HermitianMat.zero_le_iff.mp hA).eigenvalues_nonneg i
    simp [h0, spectralProj]
    rw [← Complex.ofReal_cpow hnn r]
    rfl

private lemma supportCpow_one (A : HermitianMat d ℂ) (hA : 0 ≤ A) :
    supportCpow A (1 : ℂ) = A.mat := by
  simpa using supportCpow_ofReal A hA (r := 1) zero_lt_one

private lemma Gamma_eq_supportCpow_half (σ : MState d) (X : Matrix d d ℂ) :
    Gamma σ X =
      supportCpow σ.M ((1 / 2 : ℝ) : ℂ) * X * supportCpow σ.M ((1 / 2 : ℝ) : ℂ) := by
  rw [supportCpow_ofReal σ.M σ.nonneg (r := 1 / 2) (by positivity)]
  simp [Gamma, HermitianMat.rpow_eq_cfc]

private lemma supportCpow_mul (A : HermitianMat d ℂ) (z w : ℂ) :
    supportCpow A z * supportCpow A w = supportCpow A (z + w) := by
  classical
  unfold supportCpow
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Finset.sum_eq_single i]
  · by_cases h0 : A.H.eigenvalues i = 0
    · simp [h0]
    · have h0' : ((A.H.eigenvalues i : ℂ)) ≠ 0 := by
        exact_mod_cast h0
      have hPP : spectralProj A i * spectralProj A i = spectralProj A i := by
        simpa using spectralProj_mul A i i
      calc
        (if A.H.eigenvalues i = 0 then 0 else ((A.H.eigenvalues i : ℂ) ^ z)) • spectralProj A i *
            ((if A.H.eigenvalues i = 0 then 0 else ((A.H.eigenvalues i : ℂ) ^ w)) • spectralProj A i)
            =
          (((A.H.eigenvalues i : ℂ) ^ z) * ((A.H.eigenvalues i : ℂ) ^ w)) •
            (spectralProj A i * spectralProj A i) := by
              rw [smul_mul_assoc, mul_smul_comm, smul_smul]
              simp [h0]
        _ = (((A.H.eigenvalues i : ℂ) ^ z) * ((A.H.eigenvalues i : ℂ) ^ w)) • spectralProj A i := by
              rw [hPP]
        _ = ((A.H.eigenvalues i : ℂ) ^ (z + w)) • spectralProj A i := by
              rw [← Complex.cpow_add _ _ h0']
        _ = (if A.H.eigenvalues i = 0 then 0 else ((A.H.eigenvalues i : ℂ) ^ (z + w))) •
              spectralProj A i := by simp [h0]
  · intro j hj hij
    simp [spectralProj_mul, hij]
  · intro hi
    simp at hi

private lemma Gamma_supportCpow_shift
    (σ : MState d) (a : ℂ) (X : Matrix d d ℂ) :
    Gamma σ (supportCpow σ.M a * X * supportCpow σ.M a) =
      supportCpow σ.M (((1 / 2 : ℝ) : ℂ) + a) * X *
        supportCpow σ.M (((1 / 2 : ℝ) : ℂ) + a) := by
  calc
    Gamma σ (supportCpow σ.M a * X * supportCpow σ.M a)
      = supportCpow σ.M (((1 / 2 : ℝ) : ℂ)) *
          (supportCpow σ.M a * X * supportCpow σ.M a) *
          supportCpow σ.M (((1 / 2 : ℝ) : ℂ)) := by
            rw [Gamma_eq_supportCpow_half]
    _ = (supportCpow σ.M (((1 / 2 : ℝ) : ℂ)) * supportCpow σ.M a) * X *
          (supportCpow σ.M a * supportCpow σ.M (((1 / 2 : ℝ) : ℂ))) := by
            simp [Matrix.mul_assoc]
    _ = supportCpow σ.M ((((1 / 2 : ℝ) : ℂ) + a)) * X *
          supportCpow σ.M (a + (((1 / 2 : ℝ) : ℂ))) := by
            rw [supportCpow_mul, supportCpow_mul]
    _ = supportCpow σ.M ((((1 / 2 : ℝ) : ℂ) + a)) * X *
          supportCpow σ.M ((((1 / 2 : ℝ) : ℂ) + a)) := by
            rw [add_comm a (((1 / 2 : ℝ) : ℂ))]

private lemma Gamma_supportCpow_sub_one_div
    (σ : MState d) (z : ℂ) (X : Matrix d d ℂ) :
    Gamma σ
      (supportCpow σ.M ((z - 1) / 2) * X * supportCpow σ.M ((z - 1) / 2)) =
        supportCpow σ.M (z / 2) * X * supportCpow σ.M (z / 2) := by
  have hz : (((2 : ℂ)⁻¹) + (z - 1) / 2) = z / 2 := by
    apply Complex.ext <;> simp; ring
  simpa [hz] using
    (Gamma_supportCpow_shift (σ := σ) (a := (z - 1) / 2) (X := X))

private lemma Gamma_supportCpow_neg_div
    (σ : MState d) (z : ℂ) (X : Matrix d d ℂ) :
    Gamma σ
      (supportCpow σ.M (-z / 2) * X * supportCpow σ.M (-z / 2)) =
        supportCpow σ.M (((1 : ℂ) - z) / 2) * X * supportCpow σ.M (((1 : ℂ) - z) / 2) := by
  have hz : (((2 : ℂ)⁻¹) + (-z / 2)) = (((1 : ℂ) - z) / 2) := by
    apply Complex.ext <;> simp; ring
  simpa [hz] using
    (Gamma_supportCpow_shift (σ := σ) (a := (-z / 2)) (X := X))


private lemma supportCpow_conjTranspose (A : HermitianMat d ℂ) (hA : 0 ≤ A) (z : ℂ) :
    (supportCpow A z)ᴴ = supportCpow A (star z) := by
  classical
  unfold supportCpow
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases h0 : A.H.eigenvalues i = 0
  · simp [h0]
  · have hpos : 0 < A.H.eigenvalues i := by
      exact lt_of_le_of_ne (HermitianMat.eigenvalues_nonneg hA i) (Ne.symm h0)
    have hcpow :
        star (((A.H.eigenvalues i : ℂ) ^ z)) = ((A.H.eigenvalues i : ℂ) ^ (star z)) := by
      simpa [Complex.conj_ofReal] using
        (Complex.cpow_conj (x := (A.H.eigenvalues i : ℂ)) (n := z)
          (by
            simpa [Complex.arg_ofReal_of_nonneg hpos.le] using
              (show (0 : ℝ) ≠ Real.pi by positivity))).symm
    rw [Matrix.conjTranspose_smul, show (spectralProj A i)ᴴ = spectralProj A i from by
      unfold spectralProj; simp [Matrix.mul_assoc]]
    simp [h0, hcpow]

private lemma supportCpow_im_mul_conj (A : HermitianMat d ℂ) (hA : 0 ≤ A) (t : ℝ) :
    (supportCpow A (Complex.I * t))ᴴ * supportCpow A (Complex.I * t) = A.supportProj.mat := by
  calc
    (supportCpow A (Complex.I * t))ᴴ * supportCpow A (Complex.I * t)
      = supportCpow A (star (Complex.I * t)) * supportCpow A (Complex.I * t) := by
          rw [supportCpow_conjTranspose _ hA]
    _ = supportCpow A (star (Complex.I * t) + Complex.I * t) := by
          rw [supportCpow_mul]
    _ = A.supportProj.mat := by
          simp [supportCpow_zero]

private lemma supportCpow_entry_diffContOnCl (A : HermitianMat d ℂ) (i j : d) :
    DiffContOnCl ℂ (fun z : ℂ => (supportCpow A z) i j)
      (Complex.HadamardThreeLines.verticalStrip 0 1) := by
  classical
  unfold supportCpow
  simp only [Matrix.sum_apply]
  refine Finset.induction_on Finset.univ ?_ ?_
  · simpa using (diffContOnCl_const : DiffContOnCl ℂ (fun _ : ℂ => (0 : ℂ))
      (Complex.HadamardThreeLines.verticalStrip 0 1))
  · intro a s ha hs
    simp [Finset.sum_insert, ha]
    by_cases h0 : A.H.eigenvalues a = 0
    · simpa [h0] using hs
    · have hterm :
          DiffContOnCl ℂ
            (fun z : ℂ =>
              ((A.H.eigenvalues a : ℂ) ^ z) • spectralProj A a i j)
            (Complex.HadamardThreeLines.verticalStrip 0 1) := by
          simpa [h0] using
            (((differentiable_id.const_cpow (Or.inl (by exact_mod_cast h0))).diffContOnCl).smul_const
              (spectralProj A a i j))
      simpa [h0, add_comm, add_left_comm, add_assoc] using hterm.add hs

private lemma supportCpow_diffContOnCl (A : HermitianMat d ℂ) :
    DiffContOnCl ℂ (fun z : ℂ => supportCpow A z)
      (Complex.HadamardThreeLines.verticalStrip 0 1) := by
  classical
  unfold supportCpow
  refine Finset.induction_on Finset.univ ?_ ?_
  · simpa using (diffContOnCl_const : DiffContOnCl ℂ (fun _ : ℂ => (0 : Matrix d d ℂ))
      (Complex.HadamardThreeLines.verticalStrip 0 1))
  · intro a s ha hs
    simp only [Finset.sum_insert ha]
    by_cases h0 : A.H.eigenvalues a = 0
    · simpa [h0] using hs
    · have hterm :
          DiffContOnCl ℂ
            (fun z : ℂ =>
              ((A.H.eigenvalues a : ℂ) ^ z) • spectralProj A a)
            (Complex.HadamardThreeLines.verticalStrip 0 1) := by
          simpa [h0] using
            (((differentiable_id.const_cpow (Or.inl (by exact_mod_cast h0))).diffContOnCl).smul_const
              (spectralProj A a))
      simpa [h0] using hterm.add hs

private lemma supportCpow_entry_diffContOnCl_strip (A : HermitianMat d ℂ) (l u : ℝ) (i j : d) :
    DiffContOnCl ℂ (fun z : ℂ => (supportCpow A z) i j)
      (Complex.HadamardThreeLines.verticalStrip l u) := by
  classical
  unfold supportCpow
  simp only [Matrix.sum_apply]
  refine Finset.induction_on Finset.univ ?_ ?_
  · simpa using (diffContOnCl_const : DiffContOnCl ℂ (fun _ : ℂ => (0 : ℂ))
      (Complex.HadamardThreeLines.verticalStrip l u))
  · intro a s ha hs
    simp [Finset.sum_insert, ha]
    by_cases h0 : A.H.eigenvalues a = 0
    · simpa [h0] using hs
    · have hterm :
          DiffContOnCl ℂ
            (fun z : ℂ =>
              ((A.H.eigenvalues a : ℂ) ^ z) • spectralProj A a i j)
            (Complex.HadamardThreeLines.verticalStrip l u) := by
          simpa [h0] using
            (((differentiable_id.const_cpow (Or.inl (by exact_mod_cast h0))).diffContOnCl).smul_const
              (spectralProj A a i j))
      simpa [h0, add_comm, add_left_comm, add_assoc] using hterm.add hs

private lemma supportCpow_diffContOnCl_strip (A : HermitianMat d ℂ) (l u : ℝ) :
    DiffContOnCl ℂ (fun z : ℂ => supportCpow A z)
      (Complex.HadamardThreeLines.verticalStrip l u) := by
  classical
  unfold supportCpow
  refine Finset.induction_on Finset.univ ?_ ?_
  · simpa using (diffContOnCl_const : DiffContOnCl ℂ (fun _ : ℂ => (0 : Matrix d d ℂ))
      (Complex.HadamardThreeLines.verticalStrip l u))
  · intro a s ha hs
    simp only [Finset.sum_insert ha]
    by_cases h0 : A.H.eigenvalues a = 0
    · simpa [h0] using hs
    · have hterm :
          DiffContOnCl ℂ
            (fun z : ℂ =>
              ((A.H.eigenvalues a : ℂ) ^ z) • spectralProj A a)
            (Complex.HadamardThreeLines.verticalStrip l u) := by
          simpa [h0] using
            (((differentiable_id.const_cpow (Or.inl (by exact_mod_cast h0))).diffContOnCl).smul_const
              (spectralProj A a))
      simpa [h0] using hterm.add hs

/-
If a Hermitian matrix is bounded by M*I, then all its eigenvalues are at most M.
-/
theorem HermitianMat.le_smul_one_imp_eigenvalues_le (A : HermitianMat d ℂ) (M : ℝ)
    (h : A ≤ M • (1 : HermitianMat d ℂ)) (i : d) :
    A.H.eigenvalues i ≤ M := by
  -- By definition of eigenvalues, for any unit vector $v$, we have $\langle v, A v \rangle \leq M$.
  have h_eigenvalue_le_M_step : ∀ (v : EuclideanSpace ℂ d), ‖v‖ = 1 → ⟪v, .toLp 2 <| A.mat.mulVec v⟫_ℂ ≤ M := by
    intro v hv
    have h_inner : ⟪v, .toLp 2 <| A.mat.mulVec v⟫_ℂ ≤ ⟪v, .toLp 2 <| (M • 1 : Matrix d d ℂ).mulVec v⟫_ℂ := by
      have h_inner : ⟪v, .toLp 2 <| ((M • 1 : Matrix d d ℂ) - A.mat).mulVec v⟫_ℂ ≥ 0 := by
        have h_inner_le_M : ∀ (X : HermitianMat d ℂ), X ≥ 0 → ∀ (v : EuclideanSpace ℂ d), ⟪v, .toLp 2 <| X.mat.mulVec v⟫_ℂ ≥ 0 := by
          intro X hX v
          simpa [EuclideanSpace.inner_eq_star_dotProduct, Matrix.dotProduct_mulVec, dotProduct, mul_comm] using
            (HermitianMat.inner_mulVec_nonneg hX v : 0 ≤ star v ⬝ᵥ X.mat *ᵥ v)
        convert h_inner_le_M ⟨ _, _ ⟩ _ v
        all_goals norm_num [ HermitianMat.le_iff ] at *
        · convert h.1
        · exact h
      simp_all [ Matrix.sub_mulVec]
    simp_all [ EuclideanSpace.norm_eq ]
    convert h_inner using 1
    simp [ Matrix.mulVec, dotProduct, inner ]
    simp [ Matrix.one_apply,mul_assoc]
    simp [ ← Finset.mul_sum]
    simp [ Complex.mul_conj, Complex.normSq_eq_norm_sq ]
    norm_cast
    aesop
  have := A.H.eigenvectorBasis.orthonormal
  have := this.1 i
  have := h_eigenvalue_le_M_step ( A.H.eigenvectorBasis i ) this
  rw [ show A.mat.mulVec _ = ( Matrix.IsHermitian.eigenvalues A.H i : ℂ ) • ( Matrix.IsHermitian.eigenvectorBasis A.H i ) from ?_ ] at this
  · have hnorm : ‖A.H.eigenvectorBasis i‖ = 1 := A.H.eigenvectorBasis.orthonormal.1 i
    have hself : ⟪A.H.eigenvectorBasis i, A.H.eigenvectorBasis i⟫_ℂ = 1 := by
      simp [inner_self_eq_norm_sq_to_K, hnorm]
    have hWithLp : WithLp.toLp 2 ((A.H.eigenvalues i : ℂ) • (A.H.eigenvectorBasis i).ofLp) =
        (A.H.eigenvalues i : ℂ) • A.H.eigenvectorBasis i :=
      (WithLp.toLp_smul (p := 2) (A.H.eigenvalues i : ℂ) (A.H.eigenvectorBasis i).ofLp).trans
        (by rw [WithLp.toLp_ofLp])
    rw [hWithLp, inner_smul_right, hself, mul_one] at this
    exact_mod_cast this
  · convert A.H.mulVec_eigenvectorBasis i using 1

set_option maxHeartbeats 400000 in
open MatrixOrder in
/-
If all eigenvalues of a Hermitian matrix are at most M, then the matrix is bounded by M*I.
-/
theorem HermitianMat.eigenvalues_le_imp_le_smul_one (A : HermitianMat d ℂ) (M : ℝ)
    (h : ∀ i, A.H.eigenvalues i ≤ M) :
    A ≤ M • (1 : HermitianMat d ℂ) := by
  have hD_le : HermitianMat.diagonal ℂ A.H.eigenvalues ≤ M • (1 : HermitianMat d ℂ) := by
    rw [← HermitianMat.diagonal_one (𝕜 := ℂ)]
    rw [← HermitianMat.diagonal_mul (𝕜 := ℂ) (f := (1 : d → ℝ)) M]
    rw [← sub_nonneg, ← HermitianMat.diagonal_sub, HermitianMat.zero_le_iff]
    simp [HermitianMat.diagonal_mat, Matrix.posSemidef_diagonal_iff, sub_nonneg, h]
  have h_one_conj :
      (1 : HermitianMat d ℂ).conj (A.H.eigenvectorUnitary : Matrix d d ℂ) = 1 := by
    simp [HermitianMat.conj_one_unitary]
  have h_conj_smul_one :
      (M • (1 : HermitianMat d ℂ)).conj (A.H.eigenvectorUnitary : Matrix d d ℂ) = M • (1 : HermitianMat d ℂ) := by
    calc
      (M • (1 : HermitianMat d ℂ)).conj (A.H.eigenvectorUnitary : Matrix d d ℂ)
          = HermitianMat.conjLinear ℝ (A.H.eigenvectorUnitary : Matrix d d ℂ) (M • (1 : HermitianMat d ℂ)) := by
              exact (HermitianMat.conjLinear_apply (R := ℝ) (B := (A.H.eigenvectorUnitary : Matrix d d ℂ))
                (A := M • (1 : HermitianMat d ℂ))).symm
      _ = M • HermitianMat.conjLinear ℝ (A.H.eigenvectorUnitary : Matrix d d ℂ) (1 : HermitianMat d ℂ) := by
            simp
      _ = M • ((1 : HermitianMat d ℂ).conj (A.H.eigenvectorUnitary : Matrix d d ℂ)) := by
            rw [HermitianMat.conjLinear_apply]
      _ = M • (1 : HermitianMat d ℂ) := by
            rw [h_one_conj]
  have h_conj := HermitianMat.conj_mono (M := (A.H.eigenvectorUnitary : Matrix d d ℂ)) hD_le
  rw [← HermitianMat.eq_conj_diagonal (A := A)] at h_conj
  rw [h_conj_smul_one] at h_conj
  exact h_conj

/-- The block matrix [[1, X], [X†, X†X]] is positive semidefinite. -/
theorem block_matrix_posSemidef {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    (X : Matrix k n ℂ) (Y : Matrix k m ℂ):
    (Matrix.fromBlocks (Yᴴ * Y) (Yᴴ * X) (Xᴴ * Y) (Xᴴ * X)).PosSemidef := by
  set B : Matrix (k ⊕ k) (m ⊕ n) ℂ := Matrix.fromBlocks Y X 0 0
  have hZ :
      Matrix.fromBlocks (Yᴴ * Y) (Yᴴ * X) (Xᴴ * Y) (Xᴴ * X) = Bᴴ * B := by
    have h := Matrix.fromBlocks_multiply (α := ℂ)
      (Yᴴ : Matrix m k ℂ) (0 : Matrix m k ℂ) (Xᴴ : Matrix n k ℂ) (0 : Matrix n k ℂ)
      (Y : Matrix k m ℂ) (X : Matrix k n ℂ) (0 : Matrix k m ℂ) (0 : Matrix k n ℂ)
    have hBT : Bᴴ = Matrix.fromBlocks Yᴴ 0 Xᴴ 0 := by
      simp [B, Matrix.fromBlocks_conjTranspose]
    show Matrix.fromBlocks _ _ _ _ = Bᴴ * B
    rw [hBT, h]
    simp
  rw [hZ]
  exact Matrix.posSemidef_conjTranspose_mul_self _

private lemma supportProj_le_one (A : HermitianMat d ℂ) :
    A.supportProj ≤ (1 : HermitianMat d ℂ) := by
  have hker : 0 ≤ A.kerProj := by
    simpa [HermitianMat.kerProj] using HermitianMat.projector_nonneg A.ker
  rw [show (1 : HermitianMat d ℂ) = A.supportProj + A.kerProj by
    simp [add_comm]]
  exact le_add_of_nonneg_right hker

private lemma supportProj_idem (A : HermitianMat d ℂ) :
    A.supportProj.mat * A.supportProj.mat = A.supportProj.mat := by
  have hpow : A.supportProj ^ 2 = A.supportProj := by
    rw [HermitianMat.supportProj_eq_cfc, ← HermitianMat.cfc_pow, ← HermitianMat.cfc_comp]
    apply HermitianMat.cfc_congr
    intro x hx
    by_cases hx0 : x = 0 <;> simp [hx0]
  simpa [pow_two, HermitianMat.mat_pow] using congrArg HermitianMat.mat hpow


private lemma Gamma_posSemidef (σ : MState d) {X : Matrix d d ℂ} (hX : X.PosSemidef) :
    (Gamma σ X).PosSemidef := by
  let S : HermitianMat d ℂ := σ.M.cfc (fun x => x ^ (1 / 2 : ℝ))
  have hS : S.matᴴ = S.mat := by
    simpa [S] using HermitianMat.conjTranspose_mat S
  change (S.mat * X * S.mat).PosSemidef
  simpa [hS] using (Matrix.PosSemidef.mul_mul_conjTranspose_same hX S.mat)

private lemma trace_compression_supportProj_le_trace
    {A : Matrix d₂ d₂ ℂ} (hA : A.PosSemidef) (B : HermitianMat d₂ ℂ) :
    (B.supportProj.mat * A * B.supportProj.mat).trace ≤ A.trace := by
  let S : Matrix d₂ d₂ ℂ := CFC.sqrt A
  have hS : Sᴴ = S := by
    simpa [S] using (CFC.sqrt_nonneg A).1
  have hmono :
      B.supportProj.conj S ≤ (1 : HermitianMat d₂ ℂ).conj S :=
    HermitianMat.conj_mono (M := S) (supportProj_le_one B)
  have htrace_mono :
      ((B.supportProj.conj S).mat).trace ≤ (((1 : HermitianMat d₂ ℂ).conj S).mat).trace :=
    Matrix.PosSemidef.trace_mono (show (B.supportProj.conj S).mat ≤ ((1 : HermitianMat d₂ ℂ).conj S).mat from hmono)
  have hleft :
      ((B.supportProj.conj S).mat).trace = (B.supportProj.mat * A * B.supportProj.mat).trace := by
    have hSS : S * S = A := by
      simpa [S] using CFC.sqrt_mul_sqrt_self A (Matrix.nonneg_iff_posSemidef.mpr hA)
    calc
      ((B.supportProj.conj S).mat).trace = (S * B.supportProj.mat * Sᴴ).trace := by
        simp [HermitianMat.conj_apply_mat]
      (S * B.supportProj.mat * Sᴴ).trace = (S * B.supportProj.mat * S).trace := by rw [hS]
      _ = (S * S * B.supportProj.mat).trace := by
            rw [show S * B.supportProj.mat * S = (S * B.supportProj.mat) * S by
              simp [Matrix.mul_assoc]]
            rw [Matrix.trace_mul_comm]
            simp [Matrix.mul_assoc]
      _ = (B.supportProj.mat * S * S).trace := by
            rw [Matrix.trace_mul_comm]
            simp [Matrix.mul_assoc]
      _ = (B.supportProj.mat * A).trace := by
            rw [show B.supportProj.mat * S * S = B.supportProj.mat * (S * S) by
              simp [Matrix.mul_assoc]]
            rw [hSS]
      _ = (A * B.supportProj.mat).trace := by rw [Matrix.trace_mul_comm]
      _ = (B.supportProj.mat * A * B.supportProj.mat).trace := by
            symm
            rw [show B.supportProj.mat * A * B.supportProj.mat = B.supportProj.mat * (A * B.supportProj.mat) by
              simp [Matrix.mul_assoc]]
            rw [Matrix.trace_mul_comm]
            rw [show (A * B.supportProj.mat) * B.supportProj.mat = A * (B.supportProj.mat * B.supportProj.mat) by
              simp [Matrix.mul_assoc]]
            simp [supportProj_idem B]
  have hright : (((1 : HermitianMat d₂ ℂ).conj S).mat).trace = A.trace := by
    calc
      (((1 : HermitianMat d₂ ℂ).conj S).mat).trace = (S * (1 : Matrix d₂ d₂ ℂ) * Sᴴ).trace := by
        simp [HermitianMat.conj_apply_mat]
      (S * (1 : Matrix d₂ d₂ ℂ) * Sᴴ).trace = (S * S).trace := by simp [hS]
      _ = A.trace := by
            rw [show S * S = A by
              simpa [S] using CFC.sqrt_mul_sqrt_self A (Matrix.nonneg_iff_posSemidef.mpr hA)]
  calc
    (B.supportProj.mat * A * B.supportProj.mat).trace = ((B.supportProj.conj S).mat).trace := by
      rw [hleft]
    _ ≤ (((1 : HermitianMat d₂ ℂ).conj S).mat).trace := htrace_mono
    _ = A.trace := hright

private lemma weighted_norm_one_T_map_le_of_nonneg
    (σ : MState d) (Φ : CPTPMap d d₂) {X : Matrix d d ℂ} (hX : X.PosSemidef) :
    weighted_norm 1 (Φ σ) ((T_map σ Φ) X) ≤ weighted_norm 1 σ X := by
  have hGX : (Gamma σ X).PosSemidef := Gamma_posSemidef σ hX
  have hΦGX : (Φ.map (Gamma σ X)).PosSemidef := Φ.cp.IsPositive hGX
  have hP :
      ((Φ σ).M.supportProj.mat)ᴴ = (Φ σ).M.supportProj.mat := by
    simp
  have hout : (Gamma (Φ σ) ((T_map σ Φ) X)).PosSemidef := by
    rw [Gamma_T_map_eq_compression]
    simpa [hP] using
      (Matrix.PosSemidef.mul_mul_conjTranspose_same hΦGX (Φ σ).M.supportProj.mat)
  let GinH : HermitianMat d ℂ := ⟨Gamma σ X, hGX.1⟩
  let GoutH : HermitianMat d₂ ℂ := ⟨Gamma (Φ σ) ((T_map σ Φ) X), hout.1⟩
  have hnorm_in : weighted_norm 1 σ X = GinH.trace := by
    rw [weighted_norm_one_eq_trace_norm_Gamma]
    simpa [GinH] using
      (schattenNorm_hermitian_pow (A := GinH) (HermitianMat.zero_le_iff.mpr hGX) (p := 1) (by norm_num))
  have hnorm_out : weighted_norm 1 (Φ σ) ((T_map σ Φ) X) = GoutH.trace := by
    rw [weighted_norm_one_eq_trace_norm_Gamma]
    simpa [GoutH] using
      (schattenNorm_hermitian_pow (A := GoutH) (HermitianMat.zero_le_iff.mpr hout) (p := 1) (by norm_num))
  have hmainC :
      Complex.ofReal GoutH.trace ≤ Complex.ofReal GinH.trace := by
    calc
      Complex.ofReal GoutH.trace =
          (Gamma (Φ σ) ((T_map σ Φ) X)).trace :=
        by
          change ↑GoutH.trace = GoutH.mat.trace
          exact HermitianMat.trace_eq_trace_rc GoutH
      _ = (((Φ σ).M.supportProj.mat) * Φ.map (Gamma σ X) * ((Φ σ).M.supportProj.mat)).trace := by
        rw [Gamma_T_map_eq_compression]
      _ ≤ (Φ.map (Gamma σ X)).trace := trace_compression_supportProj_le_trace hΦGX (Φ σ).M
      _ = (Gamma σ X).trace := by simp
      _ = Complex.ofReal GinH.trace := by
        change GinH.mat.trace = ↑GinH.trace
        exact (HermitianMat.trace_eq_trace_rc GinH).symm
  have hmain : GoutH.trace ≤ GinH.trace := by
    exact_mod_cast hmainC
  rw [hnorm_out, hnorm_in]
  exact hmain

private lemma dual_comp (M : MatrixMap d d₂ ℂ) (N : MatrixMap d₂ d₃ ℂ) :
    MatrixMap.dual (N ∘ₗ M) = M.dual ∘ₗ N.dual := by
  apply MatrixMap.dual_unique
  intro A B
  change (N (M A) * B).trace = (A * M.dual (N.dual B)).trace
  rw [MatrixMap.Dual.trace_eq N (M A) B, MatrixMap.Dual.trace_eq M A (N.dual B)]

private lemma dual_conj (P : Matrix d d ℂ) (hP : Pᴴ = P) :
    (MatrixMap.conj P).dual = MatrixMap.conj P := by
  apply MatrixMap.dual_unique
  intro A B
  calc
    ((MatrixMap.conj P) A * B).trace = (P * (A * Pᴴ * B)).trace := by
      simp [MatrixMap.conj, Matrix.mul_assoc]
    _ = ((A * Pᴴ * B) * P).trace := by
      rw [Matrix.trace_mul_comm]
    _ = (A * (Pᴴ * B * P)).trace := by
      simp [Matrix.mul_assoc]
    _ = (A * ((MatrixMap.conj P) B)).trace := by
      simp [MatrixMap.conj, hP, Matrix.mul_assoc]

private lemma traceNorm_le_of_dual_opNorm_le
    {M : MatrixMap d d₂ ℂ}
    (hdual : ∀ Z : Matrix d₂ d₂ ℂ, ‖M.dual Z‖ ≤ ‖Z‖)
    (Y : Matrix d d ℂ) :
    (M Y).traceNorm ≤ Y.traceNorm := by
  obtain ⟨U, hU⟩ := (Matrix.traceNorm_eq_max_re_tr_U (M Y)).left
  calc
    (M Y).traceNorm = Complex.re ((U.val * M Y).trace) := by
      simpa using hU.symm
    _ = Complex.re ((M.dual U.val * Y).trace) := by
      rw [Matrix.trace_mul_comm, MatrixMap.Dual.trace_eq, Matrix.trace_mul_comm]
    _ ≤ ‖(M.dual U.val * Y).trace‖ := Complex.re_le_norm _
    _ ≤ (M.dual U.val * Y).traceNorm := Matrix.abs_trace_le_traceNorm _
    _ ≤ ‖M.dual U.val‖ * Y.traceNorm := Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    _ ≤ ‖U.val‖ * Y.traceNorm := by
      exact mul_le_mul_of_nonneg_right (hdual U.val) (Matrix.traceNorm_nonneg Y)
    _ ≤ 1 * Y.traceNorm := by
      refine mul_le_mul_of_nonneg_right ?_ (Matrix.traceNorm_nonneg Y)
      by_cases h : IsEmpty d₂
      · have hU0 : U.val = 0 := Subsingleton.elim _ _
        simp [hU0]
      · letI : Nonempty d₂ := not_isEmpty_iff.mp h
        have hU : U.valᴴ * U.val = (1 : Matrix d₂ d₂ ℂ) := by
          ext i j
          by_cases hij : i = j
          · simpa [Matrix.one_apply, Matrix.star_eq_conjTranspose, hij] using
              congrFun (congrFun U.prop.1 i) j
          · simpa [Matrix.one_apply, Matrix.star_eq_conjTranspose, hij] using
              congrFun (congrFun U.prop.1 i) j
        have hU_sq : ‖U.val‖ * ‖U.val‖ = 1 := by
          calc
            ‖U.val‖ * ‖U.val‖ = ‖U.valᴴ * U.val‖ := by
              simpa using (CStarRing.norm_star_mul_self (x := U.val)).symm
            _ = 1 := by
              rw [hU]
              simp
        nlinarith [norm_nonneg U.val]
    _ = Y.traceNorm := by simp

private lemma fromBlocks_topleft_posSemidef {A : Matrix d₂ d₂ ℂ} (hA : A.PosSemidef) :
    (Matrix.fromBlocks A 0 0 (0 : Matrix d₂ d₂ ℂ)).PosSemidef := by
  have hsadj : (CFC.sqrt A).IsHermitian := by
    simpa using (CFC.sqrt_nonneg A).1
  have hsqrt :
      (CFC.sqrt A)ᴴ * CFC.sqrt A = A := by
    rw [hsadj.eq]
    simpa using CFC.sqrt_mul_sqrt_self A (Matrix.nonneg_iff_posSemidef.mpr hA)
  simpa [hsqrt] using
    (block_matrix_posSemidef (0 : Matrix d₂ d₂ ℂ) (CFC.sqrt A))


omit [DecidableEq d₂] in
private lemma cp_block_posSemidef {M : MatrixMap d d₂ ℂ}
    (hM : M.IsCompletelyPositive) (X : Matrix d d ℂ) :
    (Matrix.fromBlocks (M 1) (M X) ((M X)ᴴ) (M (Xᴴ * X))).PosSemidef := by
  classical
  obtain ⟨K, rfl⟩ := MatrixMap.IsCompletelyPositive.exists_kraus _ hM
  rw [MatrixMap.of_kraus_eq_sum_conj]
  have hEq :
      Matrix.fromBlocks
          ((∑ k, MatrixMap.conj (K k)) 1)
          ((∑ k, MatrixMap.conj (K k)) X)
          (((∑ k, MatrixMap.conj (K k)) X)ᴴ)
          ((∑ k, MatrixMap.conj (K k)) (Xᴴ * X))
        =
      ∑ k, Matrix.fromBlocks
        ((MatrixMap.conj (K k)) 1)
        ((MatrixMap.conj (K k)) X)
        (((MatrixMap.conj (K k)) X)ᴴ)
        ((MatrixMap.conj (K k)) (Xᴴ * X)) := by
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.sum_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.conjTranspose_sum]
  rw [hEq]
  exact Matrix.posSemidef_sum _ fun k _ => by
    simpa [MatrixMap.conj, Matrix.mul_assoc] using block_matrix_posSemidef (X * (K k)ᴴ) (K k)ᴴ

private lemma matrix_norm_le_of_nonneg_of_le {A B : Matrix d₂ d₂ ℂ}
    (hA : (0 : Matrix d₂ d₂ ℂ) ≤ A) (hAB : A ≤ B) :
    ‖A‖ ≤ ‖B‖ := by
  classical
  by_cases h : IsEmpty d₂
  · have hA0 : A = 0 := Subsingleton.elim _ _
    have hB0 : B = 0 := Subsingleton.elim _ _
    simp [hA0, hB0]
  · letI : Nonempty d₂ := not_isEmpty_iff.mp h
    letI : Nontrivial (EuclideanSpace ℂ d₂ →L[ℂ] EuclideanSpace ℂ d₂) := inferInstance
    let e := Matrix.toEuclideanCLM (n := d₂) (𝕜 := ℂ)
    have hA' : 0 ≤ e A := map_nonneg e hA
    have hAB' : e A ≤ e B := by simpa using hAB
    have h :=
      CStarAlgebra.norm_le_norm_of_nonneg_of_le
        (A := EuclideanSpace ℂ d₂ →L[ℂ] EuclideanSpace ℂ d₂) hA' hAB'
    simpa [e, Matrix.l2_opNorm_toEuclideanCLM] using h

private lemma norm_supportCpow_im_le_one (A : HermitianMat d₂ ℂ) (hA : 0 ≤ A) (t : ℝ) :
    ‖supportCpow A (Complex.I * t)‖ ≤ 1 := by
  let C := supportCpow A (Complex.I * t)
  have hsq : ‖C‖ * ‖C‖ = ‖A.supportProj.mat‖ := by
    calc
      ‖C‖ * ‖C‖ = ‖Cᴴ * C‖ := by
        simpa [C] using (CStarRing.norm_star_mul_self (x := C)).symm
      _ = ‖A.supportProj.mat‖ := by
        rw [supportCpow_im_mul_conj _ hA]
  have hproj : ‖A.supportProj.mat‖ ≤ 1 := by
    have hproj' : ‖A.supportProj.mat‖ ≤ ‖(1 : Matrix d₂ d₂ ℂ)‖ :=
      matrix_norm_le_of_nonneg_of_le
        (by
          simpa [HermitianMat.supportProj] using
            (HermitianMat.projector_nonneg (S := A.support)).nonneg)
        (by simpa using (supportProj_le_one A))
    have hone : ‖(1 : Matrix d₂ d₂ ℂ)‖ ≤ 1 := by
      by_cases h : IsEmpty d₂
      · have h1 : (1 : Matrix d₂ d₂ ℂ) = 0 := Subsingleton.elim _ _
        simp [h1]
      · letI : Nonempty d₂ := not_isEmpty_iff.mp h
        calc
          ‖(1 : Matrix d₂ d₂ ℂ)‖ = ‖(fun _ : d₂ => (1 : ℂ))‖ := by
            simp
          _ = 1 := by simp
          _ ≤ 1 := le_rfl
    exact hproj'.trans hone
  have hnonneg : 0 ≤ ‖C‖ := norm_nonneg _
  have hsquare : ‖C‖ * ‖C‖ ≤ 1 := by
    rw [hsq]
    exact hproj
  nlinarith

private lemma norm_matrix_one_le_one : ‖(1 : Matrix d d ℂ)‖ ≤ 1 := by
  by_cases h : IsEmpty d
  · have h1 : (1 : Matrix d d ℂ) = 0 := Subsingleton.elim _ _
    simp [h1]
  · letI : Nonempty d := not_isEmpty_iff.mp h
    calc
      ‖(1 : Matrix d d ℂ)‖ = ‖(fun _ : d => (1 : ℂ))‖ := by
        simp
      _ = 1 := by simp
      _ ≤ 1 := le_rfl

private lemma supportCpow_re_add_im (A : HermitianMat d ℂ) (r t : ℝ) :
    supportCpow A ((r : ℂ) + Complex.I * t) =
      supportCpow A (r : ℂ) * supportCpow A (Complex.I * t) := by
  simpa using (supportCpow_mul A (r : ℂ) (Complex.I * t)).symm

private lemma norm_supportCpow_mem_verticalClosedStrip_le_one
    (σ : MState d) {z : ℂ}
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1) :
    ‖supportCpow σ.M z‖ ≤ 1 := by
  have hz' : 0 ≤ z.re ∧ z.re ≤ 1 := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz
  set r : ℝ := z.re
  set t : ℝ := z.im
  have hzrepr : z = (r : ℂ) + Complex.I * t := by
    apply Complex.ext <;> simp [r, t]
  rw [hzrepr, supportCpow_re_add_im]
  calc
    ‖supportCpow σ.M (r : ℂ) * supportCpow σ.M (Complex.I * t)‖
      ≤ ‖supportCpow σ.M (r : ℂ)‖ * ‖supportCpow σ.M (Complex.I * t)‖ := norm_mul_le _ _
    _ ≤ ‖supportCpow σ.M (r : ℂ)‖ * 1 := by
          exact mul_le_mul_of_nonneg_left
            (norm_supportCpow_im_le_one σ.M σ.nonneg t) (norm_nonneg _)
    _ = ‖supportCpow σ.M (r : ℂ)‖ := by simp
    _ ≤ 1 := by
          by_cases hr0 : r = 0
          · have hproj :
                ‖σ.M.supportProj.mat‖ ≤ 1 :=
                (matrix_norm_le_of_nonneg_of_le
                  (by
                    simpa [HermitianMat.supportProj] using
                      (HermitianMat.projector_nonneg (S := σ.M.support)).nonneg)
                  (by simpa using supportProj_le_one σ.M)).trans norm_matrix_one_le_one
            simpa [hr0, supportCpow_zero] using hproj
          · have hr : 0 < r := lt_of_le_of_ne hz'.1 (Ne.symm hr0)
            rw [supportCpow_ofReal σ.M σ.nonneg hr]
            exact
              (matrix_norm_le_of_nonneg_of_le
                (HermitianMat.zero_le_iff.mp (HermitianMat.rpow_nonneg σ.nonneg)).nonneg
                (MState.rpow_le_one' (σ := σ) hr)).trans norm_matrix_one_le_one

private lemma exists_norm_supportCpow_le_on_verticalClosedStrip
    (A : HermitianMat d ℂ) (hA : 0 ≤ A) (l u : ℝ) :
    ∃ K : ℝ, ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip l u,
      ‖supportCpow A z‖ ≤ K := by
  classical
  let K : ℝ := ∑ i,
    max
      (if h0 : A.H.eigenvalues i = 0 then 0 else A.H.eigenvalues i ^ l)
      (if h0 : A.H.eigenvalues i = 0 then 0 else A.H.eigenvalues i ^ u) *
        ‖spectralProj A i‖
  refine ⟨K, ?_⟩
  intro z hz
  have hz' : l ≤ z.re ∧ z.re ≤ u := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz
  set r : ℝ := z.re
  set t : ℝ := z.im
  have hzrepr : z = (r : ℂ) + Complex.I * t := by
    apply Complex.ext <;> simp [r, t]
  rw [hzrepr, supportCpow_re_add_im]
  calc
    ‖supportCpow A (r : ℂ) * supportCpow A (Complex.I * t)‖
      ≤ ‖supportCpow A (r : ℂ)‖ * ‖supportCpow A (Complex.I * t)‖ := norm_mul_le _ _
    _ ≤ ‖supportCpow A (r : ℂ)‖ * 1 := by
          exact mul_le_mul_of_nonneg_left
            (norm_supportCpow_im_le_one A hA t) (norm_nonneg _)
    _ = ‖supportCpow A (r : ℂ)‖ := by simp
    _ = ‖∑ i,
          (if A.H.eigenvalues i = 0 then 0 else ((A.H.eigenvalues i : ℂ) ^ (r : ℂ))) •
            spectralProj A i‖ := by
          rfl
    _ ≤ ∑ i,
          ‖(if A.H.eigenvalues i = 0 then 0 else ((A.H.eigenvalues i : ℂ) ^ (r : ℂ))) •
            spectralProj A i‖ := by
          simpa using norm_sum_le (s := Finset.univ)
            (f := fun i =>
              (if A.H.eigenvalues i = 0 then 0 else ((A.H.eigenvalues i : ℂ) ^ (r : ℂ))) •
                spectralProj A i)
    _ ≤ K := by
          unfold K
          refine Finset.sum_le_sum ?_
          intro i hi
          by_cases h0 : A.H.eigenvalues i = 0
          · simp [h0]
          · have hnn : 0 ≤ A.H.eigenvalues i :=
              (HermitianMat.zero_le_iff.mp hA).eigenvalues_nonneg i
            have h0' : A.H.eigenvalues i ≠ 0 := by simpa using h0
            have hpos : 0 < A.H.eigenvalues i := lt_of_le_of_ne hnn (Ne.symm h0')
            have hpow_bound :
                A.H.eigenvalues i ^ r ≤
                  max
                    (if h0 : A.H.eigenvalues i = 0 then 0 else A.H.eigenvalues i ^ l)
                    (if h0 : A.H.eigenvalues i = 0 then 0 else A.H.eigenvalues i ^ u) := by
              by_cases hle1 : A.H.eigenvalues i ≤ 1
              · have hmono :
                    A.H.eigenvalues i ^ r ≤ A.H.eigenvalues i ^ l := by
                    exact Real.rpow_le_rpow_of_exponent_ge hpos hle1 (by simpa [r] using hz'.1)
                simpa [h0] using hmono.trans (le_max_left (A.H.eigenvalues i ^ l) (A.H.eigenvalues i ^ u))
              · have h1le : 1 ≤ A.H.eigenvalues i := le_of_not_ge hle1
                have hmono :
                    A.H.eigenvalues i ^ r ≤ A.H.eigenvalues i ^ u := by
                    exact Real.rpow_le_rpow_of_exponent_le h1le (by simpa [r] using hz'.2)
                simpa [h0] using hmono.trans (le_max_right (A.H.eigenvalues i ^ l) (A.H.eigenvalues i ^ u))
            have hnorm_scalar :
                ‖if A.H.eigenvalues i = 0 then 0 else ((A.H.eigenvalues i : ℂ) ^ (r : ℂ))‖ =
                  A.H.eigenvalues i ^ r := by
              simp [h0, Complex.norm_cpow_eq_rpow_re_of_pos hpos, r]
            rw [norm_smul, hnorm_scalar]
            exact mul_le_mul_of_nonneg_right hpow_bound (norm_nonneg _)

private lemma matrix_le_smul_one_of_nonneg {A : Matrix d d ℂ}
    (hA : (0 : Matrix d d ℂ) ≤ A) :
    A ≤ ‖A‖ • (1 : Matrix d d ℂ) := by
  classical
  by_cases h : IsEmpty d
  · have hA0 : A = 0 := Subsingleton.elim _ _
    simp [hA0]
  · letI : Nonempty d := not_isEmpty_iff.mp h
    letI : Nontrivial (EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d) := inferInstance
    let e := Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)
    have hA' : 0 ≤ e A := map_nonneg e hA
    have hA'' : IsSelfAdjoint (e A) := IsSelfAdjoint.of_nonneg hA'
    have h' := IsSelfAdjoint.le_algebraMap_norm_self (a := e A) hA''
    have hnorm_eq : ‖e A‖ = ‖A‖ := by
      simpa [e] using Matrix.l2_opNorm_toEuclideanCLM A
    have hs :
        (algebraMap ℝ (EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d)) ‖e A‖ =
          e (‖A‖ • (1 : Matrix d d ℂ)) := by
      calc
        (algebraMap ℝ (EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d)) ‖e A‖
            = (algebraMap ℝ (EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d)) ‖A‖ := by
                rw [hnorm_eq]
        _ = e (‖A‖ • (1 : Matrix d d ℂ)) := by
              ext x i
              change (((‖A‖ : ℂ) • x).ofLp i) = (((‖A‖ : ℂ) • (1 : Matrix d d ℂ)) *ᵥ x.ofLp) i
              rw [Matrix.smul_mulVec, Matrix.one_mulVec, WithLp.ofLp_smul]
    exact (map_le_map_iff e).1 (h'.trans_eq hs)

private lemma cp_subunital_kadison_schwarz {M : MatrixMap d d₂ ℂ}
    (hM : M.IsCompletelyPositive) (hM1 : M 1 ≤ (1 : Matrix d₂ d₂ ℂ))
    (X : Matrix d d ℂ) :
    (M X)ᴴ * M X ≤ M (Xᴴ * X) := by
  have hgap : (1 - M 1).PosSemidef := by
    simpa [sub_nonneg] using hM1
  have hblock :
      (Matrix.fromBlocks (M 1) (M X) ((M X)ᴴ) (M (Xᴴ * X))).PosSemidef :=
    cp_block_posSemidef hM X
  have hgap_block :
      (Matrix.fromBlocks (1 - M 1) 0 0 (0 : Matrix d₂ d₂ ℂ)).PosSemidef :=
    fromBlocks_topleft_posSemidef hgap
  have hsum :
      (Matrix.fromBlocks (1 : Matrix d₂ d₂ ℂ) (M X) ((M X)ᴴ) (M (Xᴴ * X))).PosSemidef := by
    have hadd :
        Matrix.fromBlocks (1 : Matrix d₂ d₂ ℂ) (M X) ((M X)ᴴ) (M (Xᴴ * X)) =
          Matrix.fromBlocks (M 1) (M X) ((M X)ᴴ) (M (Xᴴ * X)) +
          Matrix.fromBlocks (1 - M 1) 0 0 (0 : Matrix d₂ d₂ ℂ) := by
      ext i j
      cases i <;> cases j <;>
        simp [Matrix.fromBlocks, sub_eq_add_neg, add_left_comm, add_comm]
    rw [hadd]
    exact hblock.add hgap_block
  letI : Invertible (1 : Matrix d₂ d₂ ℂ) := invertibleOne
  have hschur :=
    (Matrix.PosDef.fromBlocks₁₁ (B := M X) (D := M (Xᴴ * X))
      (hA := (Matrix.PosDef.one : (1 : Matrix d₂ d₂ ℂ).PosDef))).mp hsum
  simpa [sub_nonneg] using hschur

set_option maxHeartbeats 400000 in
private lemma positive_subunital_norm_apply_le {M : MatrixMap d d₂ ℂ}
    (hM : M.IsPositive) (hM1 : M 1 ≤ (1 : Matrix d₂ d₂ ℂ))
    {X : Matrix d d ℂ} (hX : 0 ≤ X) :
    ‖M X‖ ≤ ‖X‖ := by
  have hXpsd : X.PosSemidef := by
    simpa [Matrix.nonneg_iff_posSemidef] using hX
  have hXle : X ≤ ‖X‖ • (1 : Matrix d d ℂ) :=
    matrix_le_smul_one_of_nonneg hX
  have hM_nonneg : (0 : Matrix d₂ d₂ ℂ) ≤ M X := (hM hXpsd).nonneg
  have hM_bound : M X ≤ ‖X‖ • (M 1) := by
    have hdiff : (‖X‖ • (1 : Matrix d d ℂ) - X).PosSemidef := by
      simpa [sub_nonneg] using hXle
    have hMdiff : (0 : Matrix d₂ d₂ ℂ) ≤ M (‖X‖ • (1 : Matrix d d ℂ) - X) :=
      (hM hdiff).nonneg
    simpa [sub_nonneg, map_sub, map_smul] using hMdiff
  have hM_bound' : M X ≤ ‖X‖ • (1 : Matrix d₂ d₂ ℂ) := by
    exact le_trans hM_bound (smul_le_smul_of_nonneg_left hM1 (norm_nonneg X))
  classical
  by_cases h : IsEmpty d₂
  · have hMX0 : M X = 0 := Subsingleton.elim _ _
    simp [hMX0]
  · letI : Nonempty d₂ := not_isEmpty_iff.mp h
    have hnorm := matrix_norm_le_of_nonneg_of_le hM_nonneg hM_bound'
    have hsmul_eq : (‖X‖ • (1 : Matrix d₂ d₂ ℂ)) = ((‖X‖ : ℂ) • (1 : Matrix d₂ d₂ ℂ)) := by
      ext i j; simp
    have hnorm_smul : ‖(‖X‖ • (1 : Matrix d₂ d₂ ℂ))‖ ≤ ‖X‖ := by
      rw [hsmul_eq, norm_smul]
      have h1 : ‖(1 : Matrix d₂ d₂ ℂ)‖ ≤ 1 := norm_matrix_one_le_one
      calc ‖(‖X‖ : ℂ)‖ * ‖(1 : Matrix d₂ d₂ ℂ)‖
          ≤ ‖(‖X‖ : ℂ)‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = ‖X‖ := by simp
    linarith [hnorm, hnorm_smul]

set_option maxHeartbeats 400000 in
private lemma cp_subunital_opNorm_le_one {M : MatrixMap d d₂ ℂ}
    (hM : M.IsCompletelyPositive) (hM1 : M 1 ≤ (1 : Matrix d₂ d₂ ℂ))
    (X : Matrix d d ℂ) :
    ‖M X‖ ≤ ‖X‖ := by
  have hks : (M X)ᴴ * M X ≤ M (Xᴴ * X) := cp_subunital_kadison_schwarz hM hM1 X
  have hpos : (0 : Matrix d d ℂ) ≤ Xᴴ * X := star_mul_self_nonneg X
  have hright : ‖M (Xᴴ * X)‖ ≤ ‖Xᴴ * X‖ :=
    positive_subunital_norm_apply_le (MatrixMap.IsCompletelyPositive.IsPositive hM) hM1 hpos
  have hleft :
      ‖(M X)ᴴ * M X‖ ≤ ‖M (Xᴴ * X)‖ := by
    exact matrix_norm_le_of_nonneg_of_le (star_mul_self_nonneg (M X)) hks
  have hsq : ‖M X‖ * ‖M X‖ ≤ ‖X‖ * ‖X‖ := by
    calc
      ‖M X‖ * ‖M X‖ = ‖(M X)ᴴ * M X‖ := by
        simpa using (CStarRing.norm_star_mul_self (x := M X)).symm
      _ ≤ ‖M (Xᴴ * X)‖ := hleft
      _ ≤ ‖Xᴴ * X‖ := hright
      _ = ‖X‖ * ‖X‖ := by
        simpa using (CStarRing.norm_star_mul_self (x := X))
  nlinarith [norm_nonneg (M X), norm_nonneg X]

private lemma schattenNorm_one_eq_traceNorm (A : Matrix d d ℂ) :
    schattenNorm A 1 = A.traceNorm := by
  rw [schattenNorm_eq_sum_singularValues_rpow A (by norm_num), Matrix.traceNorm_eq_sum_singularValues]
  simp

private lemma weighted_norm_one_T_map_le
    (σ : MState d) (Φ : CPTPMap d d₂) (X : Matrix d d ℂ) :
    weighted_norm 1 (Φ σ) ((T_map σ Φ) X) ≤ weighted_norm 1 σ X := by
  let P : Matrix d₂ d₂ ℂ := (Φ σ).M.supportProj.mat
  let Mcomp : MatrixMap d d₂ ℂ := (MatrixMap.conj P) ∘ₗ Φ.map
  have hP : Pᴴ = P := by
    simp [P]
  have hGamma :
      Gamma (Φ σ) ((T_map σ Φ) X) = Mcomp (Gamma σ X) := by
    rw [Gamma_T_map_eq_compression]
    simp [Mcomp, MatrixMap.conj, P, hP, Matrix.mul_assoc]
  have hMcomp_cp : Mcomp.IsCompletelyPositive := by
    dsimp [Mcomp]
    apply MatrixMap.IsCompletelyPositive.comp
    · exact Φ.cp
    · exact MatrixMap.conj_isCompletelyPositive P
  have hMcomp_dual : Mcomp.dual = Φ.map.dual ∘ₗ MatrixMap.conj P := by
    dsimp [Mcomp]
    rw [dual_comp, dual_conj P hP]
  have hconj1 : (MatrixMap.conj P) 1 ≤ (1 : Matrix d₂ d₂ ℂ) := by
    dsimp [P]
    simpa [MatrixMap.conj, hP, Matrix.mul_assoc, supportProj_idem] using
      (supportProj_le_one (Φ σ).M)
  have hMcomp_dual1 : Mcomp.dual 1 ≤ (1 : Matrix d d ℂ) := by
    rw [hMcomp_dual]
    have hΦdual_pos : Φ.map.dual.IsPositive := MatrixMap.IsPositive.dual Φ.cp.IsPositive
    have hΦdual1 : Φ.map.dual 1 = (1 : Matrix d d ℂ) := Φ.TP.dual.map_1
    have hdiff : (0 : Matrix d d ℂ) ≤ Φ.map.dual (1 - (MatrixMap.conj P) 1) := by
      have hpsd : (1 - (MatrixMap.conj P) 1).PosSemidef := by
        simpa [sub_nonneg] using hconj1
      exact (hΦdual_pos hpsd).nonneg
    have hmono : Φ.map.dual ((MatrixMap.conj P) 1) ≤ Φ.map.dual 1 := by
      simpa [map_sub, sub_nonneg] using hdiff
    simpa [hΦdual1] using hmono
  have hdual_bound : ∀ Z : Matrix d₂ d₂ ℂ, ‖Mcomp.dual Z‖ ≤ ‖Z‖ := by
    intro Z
    exact cp_subunital_opNorm_le_one (M := Mcomp.dual) (hMcomp_cp.dual) hMcomp_dual1 Z
  calc
    weighted_norm 1 (Φ σ) ((T_map σ Φ) X)
      = (Gamma (Φ σ) ((T_map σ Φ) X)).traceNorm := by
          rw [weighted_norm_one_eq_trace_norm_Gamma, schattenNorm_one_eq_traceNorm]
    _ = (Mcomp (Gamma σ X)).traceNorm := by rw [hGamma]
    _ ≤ (Gamma σ X).traceNorm := traceNorm_le_of_dual_opNorm_le hdual_bound _
    _ = weighted_norm 1 σ X := by
      rw [weighted_norm_one_eq_trace_norm_Gamma, schattenNorm_one_eq_traceNorm]

private lemma weighted_norm_infty_T_map_le
    (σ : MState d) (Φ : CPTPMap d d₂) (X : Matrix d d ℂ) :
    weighted_norm_infty (Φ σ) ((T_map σ Φ) X) ≤ weighted_norm_infty σ X := by
  dsimp [weighted_norm_infty]
  exact cp_subunital_opNorm_le_one (M := T_map σ Φ) (T_is_CP σ Φ)
    (by rw [T_map_supportProj]; simpa using supportProj_le_one (Φ σ).M) X

private lemma abs_trace_weighted_pair_le_left
    (σ : MState d) (X Y : Matrix d d ℂ) :
    ‖(Y * Gamma σ X).trace‖ ≤ weighted_norm_infty σ Y * weighted_norm 1 σ X := by
  calc
    ‖(Y * Gamma σ X).trace‖ ≤ (Y * Gamma σ X).traceNorm := Matrix.abs_trace_le_traceNorm _
    _ ≤ ‖Y‖ * (Gamma σ X).traceNorm := Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    _ = weighted_norm_infty σ Y * weighted_norm 1 σ X := by
          rw [weighted_norm_one_eq_trace_norm_Gamma, schattenNorm_one_eq_traceNorm]
          rfl

private lemma abs_trace_weighted_pair_le_right
    (σ : MState d) (X Y : Matrix d d ℂ) :
    ‖(Y * Gamma σ X).trace‖ ≤ weighted_norm 1 σ Y * weighted_norm_infty σ X := by
  let S : Matrix d d ℂ := (σ.M.cfc (fun x => x ^ (1 / 2 : ℝ))).mat
  have hcyc :
      (Y * Gamma σ X).trace = (X * Gamma σ Y).trace := by
    calc
      (Y * Gamma σ X).trace = (Y * S * X * S).trace := by
        simp [Gamma, S, Matrix.mul_assoc]
      _ = ((S * Y * S) * X).trace := by
        rw [show Y * S * X * S = ((Y * S * X) * S) by simp [Matrix.mul_assoc]]
        rw [Matrix.trace_mul_comm]
        simp [Matrix.mul_assoc]
      _ = (X * Gamma σ Y).trace := by
        rw [Matrix.trace_mul_comm]
        simp [Gamma, S, Matrix.mul_assoc]
  rw [hcyc]
  calc
    ‖(X * Gamma σ Y).trace‖ ≤ (X * Gamma σ Y).traceNorm := Matrix.abs_trace_le_traceNorm _
    _ ≤ ‖X‖ * (Gamma σ Y).traceNorm := Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    _ = weighted_norm 1 σ Y * weighted_norm_infty σ X := by
          rw [weighted_norm_one_eq_trace_norm_Gamma, schattenNorm_one_eq_traceNorm]
          rw [weighted_norm_infty, mul_comm]

private theorem sandwichedRenyiEntropy_DPI_at_one_of_gt_one
    (ρ σ : MState d) (Φ : CPTPMap d d₂)
    (hgt : ∀ {β : ℝ}, 1 < β → D̃_ β(Φ ρ‖Φ σ) ≤ D̃_ β(ρ‖σ)) :
    D̃_ 1(Φ ρ‖Φ σ) ≤ D̃_ 1(ρ‖σ) := by
  have hleft₀ :
      ContinuousWithinAt (fun β : ℝ => D̃_ β(Φ ρ‖Φ σ)) (Set.Ioi 0) 1 :=
    (sandwichedRelRentropy.continuousOn (Φ ρ) (Φ σ)) 1 (by norm_num)
  have hright₀ :
      ContinuousWithinAt (fun β : ℝ => D̃_ β(ρ‖σ)) (Set.Ioi 0) 1 :=
    (sandwichedRelRentropy.continuousOn ρ σ) 1 (by norm_num)
  have hsubset : Set.Ioi (1 : ℝ) ⊆ Set.Ioi 0 := by
    intro β hβ
    simpa [Set.mem_Ioi] using lt_trans zero_lt_one (by simpa [Set.mem_Ioi] using hβ)
  have hleft :
      Filter.Tendsto (fun β : ℝ => D̃_ β(Φ ρ‖Φ σ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (D̃_ 1(Φ ρ‖Φ σ))) :=
    hleft₀.mono_left (nhdsWithin_mono _ hsubset)
  have hright :
      Filter.Tendsto (fun β : ℝ => D̃_ β(ρ‖σ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (D̃_ 1(ρ‖σ))) :=
    hright₀.mono_left (nhdsWithin_mono _ hsubset)
  have h_event :
      ∀ᶠ β : ℝ in nhdsWithin 1 (Set.Ioi 1), D̃_ β(Φ ρ‖Φ σ) ≤ D̃_ β(ρ‖σ) := by
    filter_upwards [ (self_mem_nhdsWithin : Set.Ioi (1 : ℝ) ∈ nhdsWithin (1 : ℝ) (Set.Ioi 1)) ] with β hβ
    exact hgt hβ
  exact le_of_tendsto_of_tendsto hleft hright h_event

private lemma Gamma_Gamma_inv_density
    {ρ σ : MState d} (h : σ.M.ker ≤ ρ.M.ker) :
    Gamma σ (Gamma_inv σ ρ.M.mat) = ρ.M.mat := by
  have hleft : ρ.M.mat * σ.M.supportProj.mat = ρ.M.mat := by
    simpa using HermitianMat.mul_supportProj_of_ker_le (A := ρ.M) (B := σ.M) h
  have hright : σ.M.supportProj.mat * ρ.M.mat = ρ.M.mat := by
    have hρ : ρ.M.matᴴ = ρ.M.mat := by simpa using ρ.M.conjTranspose_mat
    have hP : σ.M.supportProj.matᴴ = σ.M.supportProj.mat := by
      simp
    calc
      σ.M.supportProj.mat * ρ.M.mat = σ.M.supportProj.mat * ρ.M.matᴴ := by rw [hρ]
      _ = (ρ.M.mat * σ.M.supportProj.mat)ᴴ := by
        simp [Matrix.conjTranspose_mul, hP]
      _ = ρ.M.matᴴ := by rw [hleft]
      _ = ρ.M.mat := hρ
  calc
    Gamma σ (Gamma_inv σ ρ.M.mat) = σ.M.supportProj.mat * ρ.M.mat * σ.M.supportProj.mat := by
      simpa using Gamma_Gamma_inv_supportProj (σ := σ) (X := ρ.M.mat)
    _ = ρ.M.mat * σ.M.supportProj.mat := by rw [hright]
    _ = ρ.M.mat := hleft

private lemma T_map_Gamma_inv_density
    {ρ σ : MState d} (Φ : CPTPMap d d₂) (h : σ.M.ker ≤ ρ.M.ker) :
    (T_map σ Φ) (Gamma_inv σ ρ.M.mat) = Gamma_inv (Φ σ) (Φ ρ).M.mat := by
  dsimp [T_map, T_op]
  rw [Gamma_Gamma_inv_density h, CPTPMap_apply_MState_M]

private lemma diffContOnCl_mul {f g : ℂ → Matrix d d ℂ} {s : Set ℂ}
    (hf : DiffContOnCl ℂ f s) (hg : DiffContOnCl ℂ g s) :
    DiffContOnCl ℂ (fun z => f z * g z) s := by
  refine ⟨hf.1.mul hg.1, hf.2.mul hg.2⟩

private lemma diffContOnCl_trace {f : ℂ → Matrix d d ℂ} {s : Set ℂ}
    (hf : DiffContOnCl ℂ f s) :
    DiffContOnCl ℂ (fun z => (f z).trace) s := by
  let trCLM : Matrix d d ℂ →L[ℂ] ℂ :=
    { toLinearMap := Matrix.traceLinearMap d ℂ ℂ
      cont := (Matrix.traceLinearMap d ℂ ℂ).continuous_of_finiteDimensional }
  simpa [Function.comp] using trCLM.differentiable.comp_diffContOnCl hf

private lemma smul_rpow_of_nonneg' {A : HermitianMat d ℂ} (hA : 0 ≤ A) {c r : ℝ} (hc : 0 ≤ c) :
    (c • A) ^ r = c ^ r • (A ^ r) := by
  rw [show c • A = A.cfc (fun x => c * x) from
    (HermitianMat.cfc_const_mul_id (A := A) (r := c)).symm]
  rw [HermitianMat.rpow_eq_cfc, ← HermitianMat.cfc_comp]
  calc
    A.cfc (((fun x => x ^ r) : ℝ → ℝ) ∘ fun x => c * x)
      = A.cfc (fun x => c ^ r * x ^ r) := by
          apply HermitianMat.cfc_congr_of_nonneg hA
          intro x hx
          rw [Function.comp_apply, Real.mul_rpow hc hx]
    _ = c ^ r • (A ^ r) := by
          rw [HermitianMat.cfc_const_mul, HermitianMat.rpow_eq_cfc]

private lemma exists_le_exp_of_ker_le {ρ σ : MState d} (hker : σ.M.ker ≤ ρ.M.ker) :
    ∃ x : ℝ, ρ.M ≤ Real.exp x • σ.M := by
  open ComplexOrder in
  let P := σ.M.supportProj
  have hright : ρ.M.mat * P.mat = ρ.M.mat := by
    dsimp [P]
    simpa using HermitianMat.mul_supportProj_of_ker_le (A := ρ.M) (B := σ.M) hker
  have hleft : P.mat * ρ.M.mat = ρ.M.mat := by
    have := congrArg Matrix.conjTranspose hright
    simp only [Matrix.conjTranspose_mul, HermitianMat.conjTranspose_mat] at this
    convert this using 2
  have hP_idem : P.mat * P.mat = P.mat := by
    have : P ^ 2 = P := by
      dsimp [P]
      rw [HermitianMat.supportProj_eq_cfc, ← HermitianMat.cfc_pow,
        ← HermitianMat.cfc_comp_apply]
      exact HermitianMat.cfc_congr_of_nonneg σ.nonneg fun x _ => by
        by_cases hx : x = 0 <;> simp [hx]
    simpa [pow_two] using congrArg (fun A : HermitianMat d ℂ => A.mat) this
  have hρ_le_P : ρ.M ≤ P := calc
    ρ.M = ρ.M.conj P.mat := by
      symm
      apply HermitianMat.ext
      simp only [HermitianMat.conj_apply_mat, HermitianMat.conjTranspose_mat, hright, hleft]
    _ ≤ (1 : HermitianMat d ℂ).conj P.mat := HermitianMat.conj_mono ρ.le_one
    _ = P := by
      apply HermitianMat.ext
      simp [HermitianMat.conj_apply_mat, hP_idem]
  let α0 : ℝ := ∑ i, if σ.M.H.eigenvalues i = 0 then 0 else (σ.M.H.eigenvalues i)⁻¹
  have hterm : ∀ j, 0 ≤ if σ.M.H.eigenvalues j = 0 then 0 else (σ.M.H.eigenvalues j)⁻¹ := by
    intro j
    split_ifs with hj
    · exact le_refl _
    · exact inv_nonneg.mpr (HermitianMat.eigenvalues_nonneg σ.nonneg j)
  have hα0_nonneg : 0 ≤ α0 := Finset.sum_nonneg fun i _ => hterm i
  have hP_le : P ≤ α0 • σ.M := by
    dsimp [P, α0]
    rw [← sub_nonneg, show
      (∑ i, if σ.M.H.eigenvalues i = 0 then 0 else (σ.M.H.eigenvalues i)⁻¹) • σ.M =
        σ.M.cfc (fun x => (∑ i, if σ.M.H.eigenvalues i = 0 then 0 else (σ.M.H.eigenvalues i)⁻¹) * x) from by
          simp,
      HermitianMat.supportProj_eq_cfc, ← HermitianMat.cfc_sub_apply, HermitianMat.cfc_nonneg_iff]
    intro i
    set y := σ.M.H.eigenvalues i
    by_cases hy0 : y = 0
    · simp [hy0]
    · have hy_pos := lt_of_le_of_ne (HermitianMat.eigenvalues_nonneg σ.nonneg i) (Ne.symm hy0)
      have hsingle : y⁻¹ ≤ α0 := by
        dsimp [α0]
        have hith : (if σ.M.H.eigenvalues i = 0 then 0 else (σ.M.H.eigenvalues i)⁻¹) = y⁻¹ := by
          rw [if_neg hy0]
        rw [← hith]
        exact Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ i)
      have hmul := mul_le_mul_of_nonneg_right hsingle hy_pos.le
      simp [hy0] at hmul ⊢
      have hyinv : y⁻¹ * y = 1 := inv_mul_cancel₀ hy0
      show 1 ≤ (∑ i, if σ.M.H.eigenvalues i = 0 then 0 else (σ.M.H.eigenvalues i)⁻¹) * y
      change y⁻¹ * y ≤ α0 * y at hmul
      linarith
  refine ⟨Real.log (α0 + 1), ?_⟩
  calc
    ρ.M ≤ P := hρ_le_P
    _ ≤ α0 • σ.M := hP_le
    _ ≤ (α0 + 1) • σ.M := smul_le_smul_of_nonneg_right (by linarith) σ.nonneg
    _ = Real.exp (Real.log (α0 + 1)) • σ.M := by
      rw [Real.exp_log (by positivity : (0 : ℝ) < α0 + 1)]

private lemma phi_le_smul_of_le_smul {ρ σ : MState d} (Φ : CPTPMap d d₂) {x : ℝ}
    (h : ρ.M ≤ Real.exp x • σ.M) :
    (Φ ρ).M ≤ Real.exp x • (Φ σ).M := by
  have hdiff : (0 : Matrix d d ℂ) ≤ Real.exp x • σ.M.mat - ρ.M.mat := by
    simpa [sub_nonneg] using h
  have hmap : (0 : Matrix d₂ d₂ ℂ) ≤ Φ.map (Real.exp x • σ.M.mat - ρ.M.mat) := by
    exact (Φ.cp.IsPositive (by simpa [Matrix.nonneg_iff_posSemidef] using hdiff)).nonneg
  simpa [sub_nonneg, map_sub, map_smul, CPTPMap_apply_MState_M] using hmap

private lemma traceNorm_le_card_mul_opNorm (A : Matrix d d ℂ) :
    A.traceNorm ≤ Fintype.card d * ‖A‖ := by
  classical
  rw [Matrix.traceNorm_eq_sum_singularValues]
  calc
    ∑ i : d, singularValues A i
      ≤ ∑ _i : d, ‖A‖ := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact Matrix.singularValues_le_opNorm A i
    _ = Fintype.card d * ‖A‖ := by simp

omit [DecidableEq d] in
set_option maxHeartbeats 800000 in
private lemma traceNorm_conjTranspose (A : Matrix d d ℂ) :
    Aᴴ.traceNorm = A.traceNorm := by
  classical
  letI : DecidableEq d := Classical.decEq d
  let hH : (Aᴴ * A).IsHermitian := by
    simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
  obtain ⟨V, W, hA⟩ :
      ∃ V W : Matrix.unitaryGroup d ℂ,
        A = V.val * Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ)) * W.valᴴ := by
    simpa [hH] using Matrix.exists_svd A
  let D : Matrix d d ℂ := Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ))
  have hV : V.val.Isometry := (Matrix.mem_unitaryGroup_iff_isometry V.val).mp V.prop |>.1
  have hW : W.val.Isometry := (Matrix.mem_unitaryGroup_iff_isometry W.val).mp W.prop |>.1
  have hdiagstar : Matrix.diagonal (star fun i => ((Real.sqrt (hH.eigenvalues i) : ℂ))) = D := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [D]
    · simp [D, hij]
  have hAstar : Aᴴ = W.val * D * V.valᴴ := by
    have hAstar0 : Aᴴ = W.val * (Matrix.diagonal (star fun i => ((Real.sqrt (hH.eigenvalues i) : ℂ))) * V.valᴴ) := by
      simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using congrArg Matrix.conjTranspose hA
    calc
      Aᴴ = W.val * (Matrix.diagonal (star fun i => ((Real.sqrt (hH.eigenvalues i) : ℂ))) * V.valᴴ) := hAstar0
      _ = W.val * (D * V.valᴴ) := by rw [hdiagstar]
      _ = W.val * D * V.valᴴ := by simp [Matrix.mul_assoc]
  calc
    Aᴴ.traceNorm = (W.val * D * V.valᴴ).traceNorm := by rw [hAstar]
    _ = D.traceNorm := by
      calc
        (W.val * D * V.valᴴ).traceNorm = (W.val * D).traceNorm := by
          simpa [Matrix.mul_assoc] using (Matrix.traceNorm_isometry_right (A := W.val * D) (u := V.val) hV)
        _ = D.traceNorm := by
          simpa using (Matrix.traceNorm_isometry_left (A := D) (u := W.val) hW)
    _ = (V.val * D * W.valᴴ).traceNorm := by
      symm
      calc
        (V.val * D * W.valᴴ).traceNorm = (V.val * D).traceNorm := by
          simpa [Matrix.mul_assoc] using (Matrix.traceNorm_isometry_right (A := V.val * D) (u := W.val) hW)
        _ = D.traceNorm := by
          simpa using (Matrix.traceNorm_isometry_left (A := D) (u := V.val) hV)
    _ = A.traceNorm := by rw [hA]

private lemma traceNorm_mul_le_traceNorm_opNorm (A B : Matrix d d ℂ) :
    (A * B).traceNorm ≤ A.traceNorm * ‖B‖ := by
  calc
    (A * B).traceNorm = ((A * B)ᴴ).traceNorm := by
      symm
      exact traceNorm_conjTranspose (A * B)
    _ = (Bᴴ * Aᴴ).traceNorm := by simp [Matrix.conjTranspose_mul]
    _ ≤ ‖Bᴴ‖ * (Aᴴ).traceNorm := Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    _ = ‖B‖ * A.traceNorm := by
      rw [traceNorm_conjTranspose A]
      have hnorm : ‖Bᴴ‖ = ‖B‖ := Matrix.l2_opNorm_conjTranspose B
      simp [hnorm]
    _ = A.traceNorm * ‖B‖ := by ring

private lemma weighted_norm_Gamma_inv_density_eq
    (α : ℝ) (hα : 1 < α) (ρ σ : MState d) :
    weighted_norm α σ (Gamma_inv σ ρ.M.mat) =
      ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace ^ (1 / α) := by
  let t : ℝ := (1 - α) / (2 * α)
  let A : HermitianMat d ℂ := ρ.M.conj (σ.M ^ t).mat
  have hA : 0 ≤ A := HermitianMat.conj_nonneg _ ρ.nonneg
  have hsum_ne : (1 / (2 * α : ℝ)) + (-(1 / 2 : ℝ)) ≠ 0 := by
    have hα0 : α ≠ 0 := by linarith
    intro h0
    have : α = 1 := by
      field_simp [hα0] at h0
      linarith
    linarith
  have hleft :
      (σ.M ^ (1 / (2 * α : ℝ))).mat * (σ.M ^ (-(1 / 2 : ℝ))).mat =
        (σ.M ^ t).mat := by
    have ht :
        (1 / (2 * α : ℝ)) + (-(1 / 2 : ℝ)) = t := by
      dsimp [t]
      field_simp [show α ≠ 0 by linarith]
      ring
    calc
      (σ.M ^ (1 / (2 * α : ℝ))).mat * (σ.M ^ (-(1 / 2 : ℝ))).mat
        = (σ.M ^ ((1 / (2 * α : ℝ)) + (-(1 / 2 : ℝ)))).mat := by
            simpa using (HermitianMat.mat_rpow_add (A := σ.M) σ.nonneg
              (p := 1 / (2 * α : ℝ)) (q := (-(1 / 2 : ℝ))) hsum_ne).symm
      _ = (σ.M ^ t).mat := by rw [ht]
  have hright :
      (σ.M ^ (-(1 / 2 : ℝ))).mat * (σ.M ^ (1 / (2 * α : ℝ))).mat =
        (σ.M ^ t).mat := by
    have ht :
        (-(1 / 2 : ℝ)) + (1 / (2 * α : ℝ)) = t := by
      dsimp [t]
      field_simp [show α ≠ 0 by linarith]
      ring
    calc
      (σ.M ^ (-(1 / 2 : ℝ))).mat * (σ.M ^ (1 / (2 * α : ℝ))).mat
        = (σ.M ^ ((-(1 / 2 : ℝ)) + (1 / (2 * α : ℝ)))).mat := by
            simpa using (HermitianMat.mat_rpow_add (A := σ.M) σ.nonneg
              (p := -(1 / 2 : ℝ)) (q := (1 / (2 * α : ℝ)))
              (by simpa [add_comm] using hsum_ne)).symm
      _ = (σ.M ^ t).mat := by rw [ht]
  calc
    weighted_norm α σ (Gamma_inv σ ρ.M.mat)
      = schattenNorm
          ((σ.M ^ (1 / (2 * α : ℝ))).mat *
            ((σ.M ^ (-(1 / 2 : ℝ))).mat * ρ.M.mat * (σ.M ^ (-(1 / 2 : ℝ))).mat) *
            (σ.M ^ (1 / (2 * α : ℝ))).mat) α := by
            unfold weighted_norm Gamma_inv
            simp only [HermitianMat.rpow_eq_cfc]
            ring_nf
    _ = schattenNorm
          (((σ.M ^ (1 / (2 * α : ℝ))).mat * (σ.M ^ (-(1 / 2 : ℝ))).mat) *
            (ρ.M.mat * ((σ.M ^ (-(1 / 2 : ℝ))).mat * (σ.M ^ (1 / (2 * α : ℝ))).mat))) α := by
          simp [Matrix.mul_assoc]
    _ = schattenNorm ((σ.M ^ t).mat * (ρ.M.mat * (σ.M ^ t).mat)) α := by
          rw [hleft, hright]
    _ = schattenNorm ((ρ.M.conj (σ.M ^ t).mat).mat) α := by
          simp [HermitianMat.conj_apply_mat, Matrix.mul_assoc]
    _ = (A ^ α).trace ^ (1 / α) := by
          simpa [A] using schattenNorm_hermitian_pow (A := A) hA (p := α) (by linarith)
    _ = ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace ^ (1 / α) := by
          simp [A, t]

private lemma weighted_norm_Gamma_inv_density_pos
    (α : ℝ) (hα : 1 < α) {ρ σ : MState d} (hker : σ.M.ker ≤ ρ.M.ker) :
    0 < weighted_norm α σ (Gamma_inv σ ρ.M.mat) := by
  have hcore_pos :
      0 < ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat := by
    apply HermitianMat.conj_pos ρ.pos
    grw [← hker]
    exact HermitianMat.ker_rpow_le_of_nonneg σ.nonneg
  have htrace_pos :
      0 < ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace := by
    apply HermitianMat.trace_pos
    apply HermitianMat.rpow_pos
    exact hcore_pos
  rw [weighted_norm_Gamma_inv_density_eq α hα ρ σ]
  exact Real.rpow_pos_of_pos htrace_pos _

private lemma sandwich_core_trace_eq_weighted_norm_rpow
    (α : ℝ) (hα : 1 < α) (ρ σ : MState d) :
    ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace =
      weighted_norm α σ (Gamma_inv σ ρ.M.mat) ^ α := by
  rw [weighted_norm_Gamma_inv_density_eq α hα ρ σ]
  have hnonneg :
      0 ≤ ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace := by
    apply HermitianMat.trace_nonneg
    apply HermitianMat.rpow_nonneg
    exact HermitianMat.conj_nonneg _ ρ.nonneg
  symm
  rw [← Real.rpow_mul hnonneg]
  field_simp [show α ≠ 0 by linarith]
  rw [Real.rpow_one]

private lemma normalized_sandwich_core_trace_eq_one
    (α : ℝ) (hα : 1 < α) {ρ σ : MState d} (hker : σ.M.ker ≤ ρ.M.ker) :
    ((((weighted_norm α σ (Gamma_inv σ ρ.M.mat))⁻¹) •
        (ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat)) ^ α).trace = 1 := by
  have hpos := weighted_norm_Gamma_inv_density_pos α hα hker
  have hcore_nonneg :
      0 ≤ ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat :=
    HermitianMat.conj_nonneg _ ρ.nonneg
  have hnorm_nonneg :
      0 ≤ (weighted_norm α σ (Gamma_inv σ ρ.M.mat))⁻¹ := inv_nonneg.mpr hpos.le
  rw [smul_rpow_of_nonneg' hcore_nonneg hnorm_nonneg, HermitianMat.trace_smul]
  rw [sandwich_core_trace_eq_weighted_norm_rpow α hα ρ σ]
  rw [Real.inv_rpow hpos.le]
  field_simp [hpos.ne']

private lemma sandwichedRelRentropy_eq_log_weighted_norm_rpow
    {α : ℝ} (hα : 1 < α) {ρ σ : MState d} (hker : σ.M.ker ≤ ρ.M.ker) :
    D̃_ α(ρ‖σ) =
      ENNReal.ofReal
        (Real.log (weighted_norm α σ (Gamma_inv σ ρ.M.mat) ^ α) / (α - 1)) := by
  have hα0 : 0 < α := by linarith
  have hcore_nonneg :
      0 ≤ ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace.log / (α - 1) := by
    simpa [hα.ne'] using
      (sandwichedRelRentropy_nonneg (ρ := ρ) (σ := σ) hα0 hker)
  have hnorm_nonneg :
      0 ≤ Real.log (weighted_norm α σ (Gamma_inv σ ρ.M.mat) ^ α) / (α - 1) := by
    simpa [sandwich_core_trace_eq_weighted_norm_rpow α hα ρ σ] using hcore_nonneg
  simp only [SandwichedRelRentropy, hα0, hker, hα.ne',
    sandwich_core_trace_eq_weighted_norm_rpow α hα ρ σ]
  change ENNReal.ofNNReal
      ⟨Real.log (weighted_norm α σ (Gamma_inv σ ρ.M.mat) ^ α) / (α - 1),
        hnorm_nonneg⟩ =
    ENNReal.ofReal (Real.log (weighted_norm α σ (Gamma_inv σ ρ.M.mat) ^ α) / (α - 1))
  exact (ENNReal.ofReal_eq_coe_nnreal hnorm_nonneg).symm

private lemma sandwichedRelRentropy_eq_log_weighted_norm_pow
    {α : ℝ} (hα : 1 < α) {ρ σ : MState d} (hker : σ.M.ker ≤ ρ.M.ker) :
    D̃_ α(ρ‖σ) =
      ENNReal.ofReal
        (Real.log
          (weighted_norm α σ (Gamma_inv σ ρ.M.mat) ^ (α / (α - 1)))) := by
  have hpos := weighted_norm_Gamma_inv_density_pos α hα hker
  rw [sandwichedRelRentropy_eq_log_weighted_norm_rpow hα hker]
  congr 1
  rw [Real.log_rpow hpos, Real.log_rpow hpos]
  field_simp [show α ≠ 0 by linarith, show α - 1 ≠ 0 by linarith]

private lemma exists_interp_theta_of_one_lt_lt {α β : ℝ}
    (hα : 1 < α) (hαβ : α < β) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ 1 / α = (1 - θ) + θ / β := by
  have hβ : 1 < β := by linarith
  refine ⟨β * (α - 1) / (α * (β - 1)), ?_⟩
  constructor
  · have hα0 : 0 < α := by linarith
    have hβ0 : 0 < β := by linarith
    have hβ1 : 0 < β - 1 := by linarith
    exact div_pos (mul_pos hβ0 (by linarith)) (mul_pos hα0 hβ1)
  constructor
  · have hα0 : 0 < α := by linarith
    have hβ0 : 0 < β := by linarith
    have hβ1 : 0 < β - 1 := by linarith
    field_simp [show α ≠ 0 by linarith, show β ≠ 0 by linarith, show β - 1 ≠ 0 by linarith]
    nlinarith
  · field_simp [show α ≠ 0 by linarith, show β ≠ 0 by linarith, show β - 1 ≠ 0 by linarith]
    ring

private lemma interp_theta_mul_conj_eq {α β θ : ℝ}
    (hα : 1 < α) (hβ : 1 < β) (h : 1 / α = (1 - θ) + θ / β) :
    θ * (α / (α - 1)) = β / (β - 1) := by
  field_simp [show α ≠ 0 by linarith, show β ≠ 0 by linarith,
    show α - 1 ≠ 0 by linarith, show β - 1 ≠ 0 by linarith] at h ⊢
  nlinarith

private lemma traceNorm_supportCpow_beta_add_im_le_one
    {A : HermitianMat d ℂ} (β : ℝ) (hβ : 1 < β) (hA : 0 ≤ A)
    (htrace : (A ^ β).trace = 1) (t : ℝ) :
    (supportCpow A ((β : ℂ) + Complex.I * t)).traceNorm ≤ 1 := by
  have hβ0 : 0 < β := lt_trans zero_lt_one hβ
  calc
    (supportCpow A ((β : ℂ) + Complex.I * t)).traceNorm
      = (supportCpow A (β : ℂ) * supportCpow A (Complex.I * t)).traceNorm := by
          rw [supportCpow_re_add_im]
    _ ≤ (supportCpow A (β : ℂ)).traceNorm * ‖supportCpow A (Complex.I * t)‖ := by
          exact traceNorm_mul_le_traceNorm_opNorm _ _
    _ ≤ (supportCpow A (β : ℂ)).traceNorm * 1 := by
          exact mul_le_mul_of_nonneg_left
            (norm_supportCpow_im_le_one A hA t) (Matrix.traceNorm_nonneg _)
    _ = (supportCpow A (β : ℂ)).traceNorm := by simp
    _ = ((A ^ β).mat).traceNorm := by rw [supportCpow_ofReal A hA hβ0]
    _ = 1 := by
          have htraceC : ((A ^ β).trace : ℂ) = 1 := by
            exact_mod_cast htrace
          have hmat_trace : ((A ^ β).mat).trace = (1 : ℂ) := by
            exact (HermitianMat.trace_eq_trace_rc (A := A ^ β)).symm.trans htraceC
          have hpsd_trace : (((A ^ β).mat).traceNorm : ℂ) = ((A ^ β).mat).trace := by
            exact Matrix.PosSemidef.traceNorm_PSD_eq_trace
              (HermitianMat.zero_le_iff.mp (HermitianMat.rpow_nonneg hA))
          have hnormC : (((A ^ β).mat).traceNorm : ℂ) = 1 := hpsd_trace.trans hmat_trace
          exact_mod_cast hnormC

private lemma map_ker_le_of_ker_le
    {ρ σ : MState d} (Φ : CPTPMap d d₂) (hker : σ.M.ker ≤ ρ.M.ker) :
    (Φ σ).M.ker ≤ (Φ ρ).M.ker := by
  rcases exists_le_exp_of_ker_le hker with ⟨x, hx⟩
  have hmap : (Φ ρ).M ≤ Real.exp x • (Φ σ).M := phi_le_smul_of_le_smul Φ hx
  exact HermitianMat.ker_le_of_le_smul (by positivity) (Φ ρ).nonneg hmap

set_option maxHeartbeats 400000 in
private lemma traceNorm_sandwich_le {n : Type*} [Fintype n] [DecidableEq n]
    {S M : Matrix n n ℂ} (hS : ‖S‖ ≤ 1) :
    (S * M * S).traceNorm ≤ M.traceNorm :=
  calc (S * M * S).traceNorm
      ≤ ‖S‖ * (M * S).traceNorm := by
        rw [Matrix.mul_assoc]; exact Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    _ ≤ 1 * (M * S).traceNorm := mul_le_mul_of_nonneg_right hS (Matrix.traceNorm_nonneg _)
    _ = (M * S).traceNorm := one_mul _
    _ ≤ M.traceNorm * ‖S‖ := traceNorm_mul_le_traceNorm_opNorm _ _
    _ ≤ M.traceNorm * 1 := mul_le_mul_of_nonneg_left hS (Matrix.traceNorm_nonneg _)
    _ = M.traceNorm := mul_one _

set_option maxHeartbeats 400000 in
private lemma opNorm_sandwich_le {n : Type*} [Fintype n] [DecidableEq n]
    {S M : Matrix n n ℂ} (hS : ‖S‖ ≤ 1) :
    ‖S * M * S‖ ≤ ‖M‖ :=
  calc ‖S * M * S‖
      ≤ ‖S‖ * ‖M * S‖ := by rw [Matrix.mul_assoc]; exact norm_mul_le _ _
    _ ≤ 1 * ‖M * S‖ := mul_le_mul_of_nonneg_right hS (norm_nonneg _)
    _ = ‖M * S‖ := one_mul _
    _ ≤ ‖M‖ * ‖S‖ := norm_mul_le _ _
    _ ≤ ‖M‖ * 1 := mul_le_mul_of_nonneg_left hS (norm_nonneg _)
    _ = ‖M‖ := mul_one _

set_option maxHeartbeats 400000 in
private lemma traceNorm_supportCpow_im_beta_add_sandwich_le_one
    {n : Type*} [Fintype n] [DecidableEq n]
    (β : ℝ) (hβ : 1 < β) (σ : MState n) (A : HermitianMat n ℂ)
    (hA_nonneg : 0 ≤ A) (hA_trace1 : (A ^ β).trace = 1) (t s : ℝ) :
    (supportCpow σ.M (Complex.I * t) *
        supportCpow A ((β : ℂ) + Complex.I * s) *
        supportCpow σ.M (Complex.I * t)).traceNorm ≤ 1 := by
  calc
    (supportCpow σ.M (Complex.I * t) *
        supportCpow A ((β : ℂ) + Complex.I * s) *
        supportCpow σ.M (Complex.I * t)).traceNorm
      ≤ (supportCpow A ((β : ℂ) + Complex.I * s)).traceNorm := traceNorm_sandwich_le
          (norm_supportCpow_im_le_one σ.M σ.nonneg t)
    _ ≤ 1 := traceNorm_supportCpow_beta_add_im_le_one β hβ hA_nonneg hA_trace1 s

set_option maxHeartbeats 400000 in
private lemma opNorm_supportCpow_im_sandwich_le_one
    {n : Type*} [Fintype n] [DecidableEq n]
    (σ : MState n) (A : HermitianMat n ℂ) (hA_nonneg : 0 ≤ A) (t s : ℝ) :
    ‖supportCpow σ.M (Complex.I * t) *
        supportCpow A (Complex.I * s) *
        supportCpow σ.M (Complex.I * t)‖ ≤ 1 := by
  calc
    ‖supportCpow σ.M (Complex.I * t) *
        supportCpow A (Complex.I * s) *
        supportCpow σ.M (Complex.I * t)‖
      ≤ ‖supportCpow A (Complex.I * s)‖ := opNorm_sandwich_le
          (norm_supportCpow_im_le_one σ.M σ.nonneg t)
    _ ≤ 1 := norm_supportCpow_im_le_one A hA_nonneg s

set_option maxHeartbeats 1600000 in
private lemma sandwichedRenyiEntropy_DPI_hnorm {β : ℝ} (hβ : 1 < β)
    (ρ σ : MState d) (Φ : CPTPMap d d₂)
    (hker : σ.M.ker ≤ ρ.M.ker) (hker_map : (Φ σ).M.ker ≤ (Φ ρ).M.ker) :
    weighted_norm β (Φ σ) (Gamma_inv (Φ σ) (Φ ρ).M.mat) ≤
      weighted_norm β σ (Gamma_inv σ ρ.M.mat) := by
  set cin := weighted_norm β σ (Gamma_inv σ ρ.M.mat)
  set cout := weighted_norm β (Φ σ) (Gamma_inv (Φ σ) (Φ ρ).M.mat)
  have hcin_pos : 0 < cin := by dsimp [cin]; exact weighted_norm_Gamma_inv_density_pos β hβ hker
  have hcout_pos : 0 < cout := by dsimp [cout]; exact weighted_norm_Gamma_inv_density_pos β hβ hker_map
  set Ain : HermitianMat d ℂ := (cin⁻¹) • (ρ.M.conj (σ.M ^ ((1 - β) / (2 * β))).mat)
  set Aout : HermitianMat d₂ ℂ := (cout⁻¹) • ((Φ ρ).M.conj ((Φ σ).M ^ ((1 - β) / (2 * β))).mat)
  have hAin_nonneg : 0 ≤ Ain := by
    simp only [Ain]
    exact smul_nonneg (inv_nonneg.mpr hcin_pos.le) (HermitianMat.conj_nonneg _ ρ.nonneg)
  have hAout_nonneg : 0 ≤ Aout := by
    simp only [Aout]
    exact smul_nonneg (inv_nonneg.mpr hcout_pos.le) (HermitianMat.conj_nonneg _ (Φ ρ).nonneg)
  have hAin_trace1 : (Ain ^ β).trace = 1 := by
    simpa [Ain, cin] using normalized_sandwich_core_trace_eq_one β hβ hker
  have hAout_trace1 : (Aout ^ β).trace = 1 := by
    simpa [Aout, cout] using normalized_sandwich_core_trace_eq_one β hβ hker_map
  let Xin : ℂ → Matrix d d ℂ := fun z =>
    supportCpow σ.M (-z / 2) * supportCpow Ain ((β : ℂ) * z) * supportCpow σ.M (-z / 2)
  let Yout : ℂ → Matrix d₂ d₂ ℂ := fun z =>
    supportCpow (Φ σ).M ((z - 1) / 2) *
      supportCpow Aout ((β : ℂ) * (1 - z)) *
      supportCpow (Φ σ).M ((z - 1) / 2)
  let f : ℂ → ℂ := fun z =>
    (Yout z * Gamma (Φ σ) ((T_map σ Φ) (Xin z))).trace
  have hXinL_dc :
      DiffContOnCl ℂ (fun z : ℂ => supportCpow σ.M (-z / 2))
        (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    apply (supportCpow_diffContOnCl_strip σ.M (-1 / 2) 0).comp
    · have hg : Differentiable ℂ (fun z : ℂ => -z / 2) := by
        fun_prop
      exact hg.diffContOnCl
    · intro z hz
      simp [Complex.HadamardThreeLines.verticalStrip, Set.mem_preimage] at hz ⊢
      constructor <;> linarith
  have hXinC_dc :
      DiffContOnCl ℂ (fun z : ℂ => supportCpow Ain ((β : ℂ) * z))
        (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    apply (supportCpow_diffContOnCl_strip Ain 0 β).comp
    · have hg : Differentiable ℂ (fun z : ℂ => (β : ℂ) * z) := by
        fun_prop
      exact hg.diffContOnCl
    · intro z hz
      simp [Complex.HadamardThreeLines.verticalStrip, Set.mem_preimage] at hz ⊢
      constructor <;> nlinarith [hz.1, hz.2, hβ]
  have hYoutL_dc :
      DiffContOnCl ℂ (fun z : ℂ => supportCpow (Φ σ).M ((z - 1) / 2))
        (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    apply (supportCpow_diffContOnCl_strip (Φ σ).M (-1 / 2) 0).comp
    · have hg : Differentiable ℂ (fun z : ℂ => (z - 1) / 2) := by
        fun_prop
      exact hg.diffContOnCl
    · intro z hz
      simp [Complex.HadamardThreeLines.verticalStrip, Set.mem_preimage] at hz ⊢
      constructor <;> linarith
  have hYoutC_dc :
      DiffContOnCl ℂ (fun z : ℂ => supportCpow Aout ((β : ℂ) * (1 - z)))
        (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    apply (supportCpow_diffContOnCl_strip Aout 0 β).comp
    · have hg : Differentiable ℂ (fun z : ℂ => (β : ℂ) * (1 - z)) := by
        fun_prop
      exact hg.diffContOnCl
    · intro z hz
      simp [Complex.HadamardThreeLines.verticalStrip, Set.mem_preimage] at hz ⊢
      constructor <;> nlinarith [hz.1, hz.2, hβ]
  have hXin_dc :
      DiffContOnCl ℂ Xin (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    dsimp [Xin]
    exact diffContOnCl_mul (diffContOnCl_mul hXinL_dc hXinC_dc) hXinL_dc
  have hYout_dc :
      DiffContOnCl ℂ Yout (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    dsimp [Yout]
    exact diffContOnCl_mul (diffContOnCl_mul hYoutL_dc hYoutC_dc) hYoutL_dc
  let G : Matrix d d ℂ →L[ℂ] Matrix d₂ d₂ ℂ :=
    { toLinearMap :=
        { toFun := fun X => Gamma (Φ σ) ((T_map σ Φ) X)
          map_add' := by
            intro X Y
            simp only [Gamma, T_map, map_add, Matrix.mul_add, Matrix.add_mul]
          map_smul' := by
            intro c X
            simp only [Gamma, T_map, map_smul, Matrix.mul_smul, Matrix.smul_mul,
              RingHom.id_apply] }
      cont := by
        exact
              ({ toFun := fun X => Gamma (Φ σ) ((T_map σ Φ) X)
                 map_add' := by
                   intro X Y
                   simp only [Gamma, T_map, map_add, Matrix.mul_add, Matrix.add_mul]
                 map_smul' := by
                   intro c X
                   simp only [Gamma, T_map, map_smul, Matrix.mul_smul, Matrix.smul_mul,
                     RingHom.id_apply] } :
                Matrix d d ℂ →ₗ[ℂ] Matrix d₂ d₂ ℂ).continuous_of_finiteDimensional }
  have hGX_dc :
      DiffContOnCl ℂ (fun z => G (Xin z))
        (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    exact G.differentiable.comp_diffContOnCl hXin_dc
  have hf_dc :
      DiffContOnCl ℂ f (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    dsimp [f]
    exact diffContOnCl_trace (diffContOnCl_mul hYout_dc hGX_dc)
  obtain ⟨Kσneg, hKσneg⟩ :=
    exists_norm_supportCpow_le_on_verticalClosedStrip σ.M σ.nonneg (-1 / 2) 0
  obtain ⟨KAin, hKAin⟩ :=
    exists_norm_supportCpow_le_on_verticalClosedStrip Ain hAin_nonneg 0 β
  obtain ⟨KAout, hKAout⟩ :=
    exists_norm_supportCpow_le_on_verticalClosedStrip Aout hAout_nonneg 0 β
  let KXin : ℝ := Kσneg * KAin * Kσneg
  let KYout : ℝ := Fintype.card d₂ * KAout
  have hXin_bound :
      ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1,
        weighted_norm_infty σ (Xin z) ≤ KXin := by
    intro z hz
    have hzL : -z / 2 ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1 / 2) 0 := by
      simp [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage] at hz ⊢
      constructor <;> linarith
    have hzC : (β : ℂ) * z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 β := by
      simp [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage] at hz ⊢
      constructor <;> nlinarith [hz.1, hz.2, hβ]
    let L : Matrix d d ℂ := supportCpow σ.M (-z / 2)
    let M : Matrix d d ℂ := supportCpow Ain ((β : ℂ) * z)
    dsimp [weighted_norm_infty, Xin, KXin, L, M]
    have hML : ‖M * L‖ ≤ ‖M‖ * ‖L‖ := norm_mul_le _ _
    have hLM : ‖L‖ * ‖M * L‖ ≤ ‖L‖ * (‖M‖ * ‖L‖) := by
      exact mul_le_mul_of_nonneg_left hML (norm_nonneg _)
    have hMK : ‖M‖ * ‖L‖ ≤ KAin * Kσneg := by
      exact mul_le_mul (hKAin _ hzC) (hKσneg _ hzL) (norm_nonneg _)
        ((norm_nonneg _).trans (hKAin _ hzC))
    have hright : ‖L‖ * (‖M‖ * ‖L‖) ≤ Kσneg * (KAin * Kσneg) := by
      exact mul_le_mul (hKσneg _ hzL) hMK (by positivity)
        ((norm_nonneg _).trans (hKσneg _ hzL))
    calc
      ‖L * M * L‖ ≤ ‖L‖ * ‖M * L‖ := by
              rw [Matrix.mul_assoc]; exact norm_mul_le _ _
          _ ≤ ‖L‖ * (‖M‖ * ‖L‖) := hLM
          _ ≤ Kσneg * (KAin * Kσneg) := hright
          _ = KXin := by ring
  have hYout_bound :
      ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1,
        weighted_norm 1 (Φ σ) (Yout z) ≤ KYout := by
      intro z hz
      have hzhalf : z / 2 ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
        simp [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage] at hz ⊢
        constructor <;> linarith
      have hzC : (β : ℂ) * (1 - z) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 β := by
        simp [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage] at hz ⊢
        constructor <;> nlinarith [hz.1, hz.2, hβ]
      rw [weighted_norm_one_eq_trace_norm_Gamma, schattenNorm_one_eq_traceNorm]
      let S : Matrix d₂ d₂ ℂ := supportCpow (Φ σ).M (z / 2)
      let M : Matrix d₂ d₂ ℂ := supportCpow Aout ((β : ℂ) * (1 - z))
      have hGammaY : Gamma (Φ σ) (Yout z) = S * M * S := by
        dsimp [Yout, S, M]
        rw [Gamma_supportCpow_shift]
        congr 1 <;> push_cast <;> ring_nf
      rw [hGammaY]
      dsimp [KYout, S, M]
      calc (S * M * S).traceNorm
          ≤ M.traceNorm := traceNorm_sandwich_le
            (norm_supportCpow_mem_verticalClosedStrip_le_one (σ := Φ σ) hzhalf)
        _ ≤ Fintype.card d₂ * ‖M‖ := traceNorm_le_card_mul_opNorm M
        _ ≤ Fintype.card d₂ * KAout :=
            mul_le_mul_of_nonneg_left (hKAout _ hzC) (by positivity)
  have hB :
      BddAbove ((norm ∘ f) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
      have hKAout_nonneg : 0 ≤ KAout := by
        have hβ0 : 0 ≤ β := by linarith
        have h0mem : (0 : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 β := by
          simp [Complex.HadamardThreeLines.verticalClosedStrip, hβ0]
        exact le_trans (norm_nonneg _) (hKAout 0 h0mem)
      have hKYout_nonneg : 0 ≤ KYout := by
        dsimp [KYout]
        positivity
      refine ⟨KYout * KXin, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      have hmain :
          ‖(Yout z * Gamma (Φ σ) ((T_map σ Φ) (Xin z))).trace‖
            ≤ weighted_norm 1 (Φ σ) (Yout z) *
                weighted_norm_infty (Φ σ) ((T_map σ Φ) (Xin z)) :=
        abs_trace_weighted_pair_le_right (σ := Φ σ)
            (X := (T_map σ Φ) (Xin z)) (Y := Yout z)
      have hTin : weighted_norm_infty (Φ σ) ((T_map σ Φ) (Xin z)) ≤ KXin :=
        (weighted_norm_infty_T_map_le σ Φ (Xin z)).trans (hXin_bound z hz)
      have hTin_nonneg : 0 ≤ weighted_norm_infty (Φ σ) ((T_map σ Φ) (Xin z)) := by
        dsimp [weighted_norm_infty]
        exact norm_nonneg _
      exact hmain.trans <|
        mul_le_mul (hYout_bound z hz) hTin hTin_nonneg hKYout_nonneg
  have ha :
      ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ), ‖f z‖ ≤ 1 := by
    intro z hz
    have hz0 : z.re = 0 := by simpa using hz
    have hY1 : weighted_norm 1 (Φ σ) (Yout z) ≤ 1 := by
      rw [weighted_norm_one_eq_trace_norm_Gamma, schattenNorm_one_eq_traceNorm]
      dsimp [Yout]
      rw [Gamma_supportCpow_sub_one_div]
      have hzhalf : z / 2 = Complex.I * (z.im / 2) := by
        apply Complex.ext <;> simp [hz0, div_eq_mul_inv]
      have hzC : (β : ℂ) * (1 - z) = (β : ℂ) + Complex.I * (-β * z.im) := by
        apply Complex.ext <;> simp [hz0]
      rw [hzhalf, hzC]
      simpa using
        (traceNorm_supportCpow_im_beta_add_sandwich_le_one β hβ (Φ σ) Aout
          hAout_nonneg hAout_trace1 (z.im / 2) (-β * z.im))
    have hX1 :
        weighted_norm_infty (Φ σ) ((T_map σ Φ) (Xin z)) ≤ 1 := by
      refine (weighted_norm_infty_T_map_le σ Φ (Xin z)).trans ?_
      dsimp [weighted_norm_infty, Xin]
      have hzhalf : -z / 2 = Complex.I * (-(z.im / 2)) := by
        apply Complex.ext <;> simp [hz0, div_eq_mul_inv]
      have hzC : (β : ℂ) * z = Complex.I * (β * z.im) := by
        apply Complex.ext <;> simp [hz0]
      rw [hzhalf, hzC]
      simpa using
        (opNorm_supportCpow_im_sandwich_le_one σ Ain hAin_nonneg (-(z.im / 2)) (β * z.im))
    have hmain :
        ‖f z‖ ≤ weighted_norm 1 (Φ σ) (Yout z) *
            weighted_norm_infty (Φ σ) ((T_map σ Φ) (Xin z)) :=
      abs_trace_weighted_pair_le_right (σ := Φ σ)
        (X := (T_map σ Φ) (Xin z)) (Y := Yout z)
    have hY1_nonneg : 0 ≤ weighted_norm 1 (Φ σ) (Yout z) := by
      unfold weighted_norm
      exact schattenNorm_nonneg _ _
    have hX1_nonneg : 0 ≤ weighted_norm_infty (Φ σ) ((T_map σ Φ) (Xin z)) := by
      dsimp [weighted_norm_infty]
      exact norm_nonneg _
    have hprod : weighted_norm 1 (Φ σ) (Yout z) *
        weighted_norm_infty (Φ σ) ((T_map σ Φ) (Xin z)) ≤ 1 := by
      nlinarith
    exact hmain.trans hprod
  have hb :
      ∀ z ∈ Complex.re ⁻¹' ({1} : Set ℝ), ‖f z‖ ≤ 1 := by
    intro z hz
    have hz1 : z.re = 1 := by simpa using hz
    have hY1 : weighted_norm_infty (Φ σ) (Yout z) ≤ 1 := by
      dsimp [weighted_norm_infty, Yout]
      have hzhalf : (z - 1) / 2 = Complex.I * (z.im / 2) := by
        apply Complex.ext <;> simp [hz1, div_eq_mul_inv]
      have hzC : (β : ℂ) * (1 - z) = Complex.I * (-β * z.im) := by
        apply Complex.ext <;> simp [hz1]
      rw [hzhalf, hzC]
      simpa using
        (opNorm_supportCpow_im_sandwich_le_one (Φ σ) Aout hAout_nonneg (z.im / 2) (-β * z.im))
    have hX1 : weighted_norm 1 σ (Xin z) ≤ 1 := by
      rw [weighted_norm_one_eq_trace_norm_Gamma, schattenNorm_one_eq_traceNorm]
      dsimp [Xin]
      rw [Gamma_supportCpow_neg_div]
      have hzhalf : (((1 : ℂ) - z) / 2) = Complex.I * (-(z.im / 2)) := by
        apply Complex.ext <;> simp [hz1, div_eq_mul_inv]
      have hzC : (β : ℂ) * z = (β : ℂ) + Complex.I * (β * z.im) := by
        apply Complex.ext <;> simp [hz1]
      rw [hzhalf, hzC]
      simpa using
        (traceNorm_supportCpow_im_beta_add_sandwich_le_one β hβ σ Ain
          hAin_nonneg hAin_trace1 (-(z.im / 2)) (β * z.im))
    have hTX1 : weighted_norm 1 (Φ σ) ((T_map σ Φ) (Xin z)) ≤ 1 :=
      (weighted_norm_one_T_map_le σ Φ (Xin z)).trans hX1
    have hmain :
        ‖f z‖ ≤ weighted_norm_infty (Φ σ) (Yout z) *
            weighted_norm 1 (Φ σ) ((T_map σ Φ) (Xin z)) :=
      abs_trace_weighted_pair_le_left (σ := Φ σ)
        (X := (T_map σ Φ) (Xin z)) (Y := Yout z)
    have hY1_nonneg : 0 ≤ weighted_norm_infty (Φ σ) (Yout z) := by
      dsimp [weighted_norm_infty]
      exact norm_nonneg _
    have hTX1_nonneg : 0 ≤ weighted_norm 1 (Φ σ) ((T_map σ Φ) (Xin z)) := by
      unfold weighted_norm
      exact schattenNorm_nonneg _ _
    have hprod : weighted_norm_infty (Φ σ) (Yout z) *
        weighted_norm 1 (Φ σ) ((T_map σ Φ) (Xin z)) ≤ 1 := by
      nlinarith
    exact hmain.trans hprod
  have hθmem :
      (((1 / β : ℝ) : ℂ)) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    have hβpos : 0 < β := by linarith
    simp [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage]
    constructor
    · positivity
    · have hβinv_le : (1 / β : ℝ) ≤ 1 := (div_le_one hβpos).2 (le_of_lt hβ)
      simpa [one_div] using hβinv_le
  have hfθ :
      ‖f (((1 / β : ℝ) : ℂ))‖ ≤ 1 := by
    simpa using
      (Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
        (f := f) (l := 0) (u := 1) (a := 1) (b := 1) zero_lt_one hθmem hf_dc hB ha hb)
  have hθeval : f (((1 / β : ℝ) : ℂ)) = cout / cin := by
    have hβne : (β : ℝ) ≠ 0 := by linarith
    have hθ1R : β * (1 / β : ℝ) = 1 := by
      field_simp [hβne]
    have hθ1 : ((β : ℂ) * (((1 / β : ℝ) : ℂ))) = 1 := by
      exact_mod_cast hθ1R
    have hθ2R : β * (1 - (1 / β : ℝ)) = β - 1 := by
      field_simp [hβne]
    have hθ2 :
        ((β : ℂ) * (1 - (((1 / β : ℝ) : ℂ)))) = (β - 1 : ℂ) := by
      exact_mod_cast hθ2R
    have hs_addR :
        (-(1 / (2 * β : ℝ))) + (((1 - β) / (2 * β) : ℝ)) = (-1 / 2 : ℝ) := by
      field_simp [hβne]
      ring_nf
    have hs_add :
        ((-(1 / (2 * β : ℝ)) : ℂ)) + ((((1 - β) / (2 * β) : ℝ) : ℂ)) = ((-1 / 2 : ℝ) : ℂ) := by
      exact_mod_cast hs_addR
    have hs_add' :
        ((((1 - β) / (2 * β) : ℝ) : ℂ)) + ((-(1 / (2 * β : ℝ)) : ℂ)) = ((-1 / 2 : ℝ) : ℂ) := by
      simpa [add_comm] using hs_add
    have hXinExp :
        ((β : ℂ)⁻¹ * ((-1 / 2 : ℝ) : ℂ)) = ((-(1 / (2 * β : ℝ)) : ℂ)) := by
      apply Complex.ext <;> simp; field_simp [hβne]
    have hσt :
        ((σ.M ^ ((1 - β) / (2 * β))).mat) =
          supportCpow σ.M ((((1 - β) / (2 * β) : ℝ) : ℂ)) := by
      symm
      exact supportCpow_ofReal_ne_zero σ.M σ.nonneg (by
        have hnum : (1 - β : ℝ) ≠ 0 := by linarith
        have hden : (2 * β : ℝ) ≠ 0 := by nlinarith
        exact div_ne_zero hnum hden)
    have hΦσt :
        (((Φ σ).M ^ ((1 - β) / (2 * β))).mat) =
          supportCpow (Φ σ).M ((((1 - β) / (2 * β) : ℝ) : ℂ)) := by
      symm
      exact supportCpow_ofReal_ne_zero (Φ σ).M (Φ σ).nonneg (by
        have hnum : (1 - β : ℝ) ≠ 0 := by linarith
        have hden : (2 * β : ℝ) ≠ 0 := by nlinarith
        exact div_ne_zero hnum hden)
    have hσtH :
        ((σ.M ^ ((1 - β) / (2 * β))).mat)ᴴ =
          supportCpow σ.M ((((1 - β) / (2 * β) : ℝ) : ℂ)) := by
      calc
        ((σ.M ^ ((1 - β) / (2 * β))).mat)ᴴ
          = (supportCpow σ.M ((((1 - β) / (2 * β) : ℝ) : ℂ)))ᴴ := by rw [hσt]
        _ = supportCpow σ.M ((((1 - β) / (2 * β) : ℝ) : ℂ)) := by
            rw [supportCpow_conjTranspose σ.M σ.nonneg]
            simp
    have hsuppσtH :
        (supportCpow σ.M ((((1 - β) / (2 * β) : ℝ) : ℂ)))ᴴ =
          supportCpow σ.M ((((1 - β) / (2 * β) : ℝ) : ℂ)) := by
      rw [supportCpow_conjTranspose σ.M σ.nonneg]
      simp
    have hσnegHalf :
        supportCpow σ.M (((-1 / 2 : ℝ) : ℂ)) =
          ((σ.M.cfc (fun x => x ^ (-1 / 2 : ℝ))).mat) := by
      simpa [HermitianMat.rpow_eq_cfc] using
        (supportCpow_ofReal_ne_zero (A := σ.M) (hA := σ.nonneg) (r := (-1 / 2))
          (by norm_num))
    have hXinθ :
        Xin (((1 / β : ℝ) : ℂ)) = cin⁻¹ • Gamma_inv σ ρ.M.mat := by
      calc
        Xin (((1 / β : ℝ) : ℂ))
          = supportCpow σ.M ((-(1 / (2 * β : ℝ)) : ℂ)) *
              Ain.mat *
              supportCpow σ.M ((-(1 / (2 * β : ℝ)) : ℂ)) := by
                dsimp [Xin]
                rw [hθ1, supportCpow_one Ain hAin_nonneg]
                simp [div_eq_mul_inv]
        _ = supportCpow σ.M ((-(1 / (2 * β : ℝ)) : ℂ)) *
              ((cin⁻¹) • (((σ.M ^ ((1 - β) / (2 * β))).mat) * ρ.M.mat *
                ((σ.M ^ ((1 - β) / (2 * β))).mat)ᴴ)) *
              supportCpow σ.M ((-(1 / (2 * β : ℝ)) : ℂ)) := by
                simp [Ain, HermitianMat.conj_apply_mat]
        _ = cin⁻¹ •
              (supportCpow σ.M ((-(1 / (2 * β : ℝ)) : ℂ)) *
                supportCpow σ.M ((((1 - β) / (2 * β) : ℝ) : ℂ)) *
                ρ.M.mat *
                (supportCpow σ.M ((((1 - β) / (2 * β) : ℝ) : ℂ)) *
                  supportCpow σ.M ((-(1 / (2 * β : ℝ)) : ℂ)))) := by
                rw [hσt, hsuppσtH]
                simp [Matrix.mul_assoc]
        _ = cin⁻¹ •
              (supportCpow σ.M (((-1 / 2 : ℝ) : ℂ)) *
                ρ.M.mat *
                supportCpow σ.M (((-1 / 2 : ℝ) : ℂ))) := by
                rw [supportCpow_mul, supportCpow_mul, hs_add, hs_add']
        _ = cin⁻¹ • Gamma_inv σ ρ.M.mat := by
              rw [Gamma_inv, hσnegHalf]
    have hTθ :
        Gamma (Φ σ) ((T_map σ Φ) (Xin (((1 / β : ℝ) : ℂ)))) = (cin⁻¹) • (Φ ρ).M.mat := by
      calc
        Gamma (Φ σ) ((T_map σ Φ) (Xin (((1 / β : ℝ) : ℂ))))
          = Gamma (Φ σ) ((T_map σ Φ) ((cin⁻¹) • Gamma_inv σ ρ.M.mat)) := by rw [hXinθ]
        _ = (cin⁻¹) • Gamma (Φ σ) ((T_map σ Φ) (Gamma_inv σ ρ.M.mat)) := by
              simp [T_map, T_op, Gamma, Gamma_inv, Matrix.mul_assoc]
        _ = (cin⁻¹) • Gamma (Φ σ) (Gamma_inv (Φ σ) (Φ ρ).M.mat) := by
              rw [T_map_Gamma_inv_density (Φ := Φ) hker]
        _ = (cin⁻¹) • (Φ ρ).M.mat := by
              rw [Gamma_Gamma_inv_density hker_map]
    have hYθ :
        Yout (((1 / β : ℝ) : ℂ)) =
          supportCpow (Φ σ).M ((((1 - β) / (2 * β) : ℝ) : ℂ)) *
            (Aout ^ (β - 1)).mat *
            supportCpow (Φ σ).M ((((1 - β) / (2 * β) : ℝ) : ℂ)) := by
      have hYexpR : (((1 / β : ℝ) - 1) / 2) = ((1 - β) / (2 * β) : ℝ) := by
        field_simp [hβne]
      have hβsub : 0 < β - 1 := by linarith
      have hAoutPow : supportCpow Aout ((β : ℂ) - 1) = (Aout ^ (β - 1)).mat := by
        simpa using (supportCpow_ofReal Aout hAout_nonneg hβsub)
      dsimp [Yout]
      rw [show ((((1 / β : ℝ) : ℂ) - 1) / 2) = ((((1 - β) / (2 * β) : ℝ) : ℂ)) by
        exact_mod_cast hYexpR]
      rw [hθ2]
      exact congrArg
        (fun M =>
          supportCpow (Φ σ).M ((((1 - β) / (2 * β) : ℝ) : ℂ)) * M *
            supportCpow (Φ σ).M ((((1 - β) / (2 * β) : ℝ) : ℂ)))
        hAoutPow
    have hBout :
        supportCpow (Φ σ).M ((((1 - β) / (2 * β) : ℝ) : ℂ)) * (Φ ρ).M.mat *
          supportCpow (Φ σ).M ((((1 - β) / (2 * β) : ℝ) : ℂ)) =
            cout • Aout.mat := by
      rw [← hΦσt]
      simp [Aout, HermitianMat.conj_apply_mat, Matrix.mul_assoc]
      have hcout_cancel : cout * cout⁻¹ = (1 : ℝ) := by
        field_simp [hcout_pos.ne']
      simp [smul_smul, hcout_cancel]
    have hpowmul :
        (Aout ^ (β - 1)).mat * Aout.mat = (Aout ^ β).mat := by
      calc
        (Aout ^ (β - 1)).mat * Aout.mat
          = supportCpow Aout (((β - 1 : ℝ) : ℂ)) * supportCpow Aout (1 : ℂ) := by
              rw [supportCpow_ofReal Aout hAout_nonneg (by linarith), supportCpow_one Aout hAout_nonneg]
        _ = supportCpow Aout (β : ℂ) := by
              rw [supportCpow_mul]
              congr 1
              simp
        _ = (Aout ^ β).mat := by
              symm
              rw [supportCpow_ofReal Aout hAout_nonneg (show 0 < β by linarith)]
    let Sout : Matrix d₂ d₂ ℂ :=
      supportCpow (Φ σ).M ((((1 - β) / (2 * β) : ℝ) : ℂ))
    calc
      f (((1 / β : ℝ) : ℂ))
          = ((Yout (((1 / β : ℝ) : ℂ))) * ((cin⁻¹) • (Φ ρ).M.mat)).trace := by
              dsimp [f]
              rw [hTθ]
      _ = cin⁻¹ * (Yout (((1 / β : ℝ) : ℂ)) * (Φ ρ).M.mat).trace := by
              simp
      _ = cin⁻¹ * (((Sout * (Aout ^ (β - 1)).mat * Sout) * (Φ ρ).M.mat).trace) := by
              rw [hYθ]
      _ = cin⁻¹ * (((Aout ^ (β - 1)).mat * (Sout * (Φ ρ).M.mat * Sout)).trace) := by
              congr 1
              let A : Matrix d₂ d₂ ℂ := (Aout ^ (β - 1)).mat
              let R : Matrix d₂ d₂ ℂ := (Φ ρ).M.mat
              have hcyc : ((Sout * A * Sout) * R).trace = (A * (Sout * R * Sout)).trace := by
                calc
                  ((Sout * A * Sout) * R).trace = (Sout * A * (Sout * R)).trace := by
                    rw [Matrix.mul_assoc]
                  _ = ((Sout * R) * Sout * A).trace := by
                    rw [Matrix.trace_mul_cycle]
                  _ = (A * (Sout * R) * Sout).trace := by
                    rw [Matrix.trace_mul_cycle]
                  _ = (A * (Sout * R * Sout)).trace := by
                    refine congrArg Matrix.trace ?_
                    calc
                      A * (Sout * R) * Sout = (A * (Sout * R)) * Sout := by rfl
                      _ = A * ((Sout * R) * Sout) := by rw [Matrix.mul_assoc]
                      _ = A * (Sout * R * Sout) := by rfl
              simpa [A, R] using hcyc
      _ = cin⁻¹ * (((Aout ^ (β - 1)).mat * (cout • Aout.mat)).trace) := by rw [hBout]
      _ = cin⁻¹ * (cout * ((Aout ^ β).mat).trace) := by
              rw [Matrix.mul_smul, Matrix.trace_smul]
              simp [hpowmul]
      _ = cin⁻¹ * (cout * 1) := by
              have htraceβC : (((Aout ^ β).trace : ℂ) = 1) := by
                exact_mod_cast hAout_trace1
              have htraceβ : ((Aout ^ β).mat).trace = (1 : ℂ) := by
                exact (HermitianMat.trace_eq_trace_rc (A := Aout ^ β)).symm.trans htraceβC
              rw [htraceβ]
      _ = cout / cin := by
              calc
                (((cin⁻¹ : ℝ) : ℂ) * (cout * 1))
                    = ((cin : ℂ)⁻¹ * ((cout : ℂ) * 1)) := by simp
                _ = (cout : ℂ) / cin := by simp [div_eq_mul_inv, mul_comm]
  have hratio_nonneg : 0 ≤ cout / cin := by positivity
  have hratio_le_one : cout / cin ≤ 1 := by
    have hnorm_ratioC : ‖(((cout / cin : ℝ) : ℂ))‖ ≤ 1 := by
      have hθeval' : f (((1 / β : ℝ) : ℂ)) = (((cout / cin : ℝ) : ℂ) : ℂ) := by
        simpa using hθeval
      rw [← hθeval']
      exact hfθ
    have hnorm_ratio : ‖cout / cin‖ ≤ 1 := by simpa using hnorm_ratioC
    rwa [Real.norm_eq_abs, abs_of_nonneg hratio_nonneg] at hnorm_ratio
  exact (div_le_one hcin_pos).mp hratio_le_one

set_option maxHeartbeats 800000 in
private lemma sandwichedRenyiEntropy_DPI_ker {β : ℝ} (hβ : 1 < β)
    (ρ σ : MState d) (Φ : CPTPMap d d₂) (hker : σ.M.ker ≤ ρ.M.ker) :
    D̃_ β(Φ ρ‖Φ σ) ≤ D̃_ β(ρ‖σ) := by
  have hker_map : (Φ σ).M.ker ≤ (Φ ρ).M.ker := map_ker_le_of_ker_le Φ hker
  set cin : ℝ := weighted_norm β σ (Gamma_inv σ ρ.M.mat)
  set cout : ℝ := weighted_norm β (Φ σ) (Gamma_inv (Φ σ) (Φ ρ).M.mat)
  have hcin_pos : 0 < cin := by
    dsimp [cin]; exact weighted_norm_Gamma_inv_density_pos β hβ hker
  have hcout_pos : 0 < cout := by
    dsimp [cout]; exact weighted_norm_Gamma_inv_density_pos β hβ hker_map
  have hnorm : cout ≤ cin :=
    sandwichedRenyiEntropy_DPI_hnorm hβ ρ σ Φ hker hker_map
  have hβ0 : 0 < β := lt_trans zero_lt_one hβ
  have hout :
      D̃_ β(Φ ρ‖Φ σ) = ENNReal.ofReal (Real.log (cout ^ β) / (β - 1)) := by
    have hnonneg :
        0 ≤ Real.log (cout ^ β) / (β - 1) := by
      simpa [hβ.ne', cout, sandwich_core_trace_eq_weighted_norm_rpow β hβ (Φ ρ) (Φ σ)] using
        (sandwichedRelRentropy_nonneg hβ0 hker_map)
    unfold SandwichedRelRentropy
    simpa [hβ0, hβ.ne', hker_map, cout,
      sandwich_core_trace_eq_weighted_norm_rpow β hβ (Φ ρ) (Φ σ)] using
      (ENNReal.ofReal_eq_coe_nnreal hnonneg).symm
  have hin :
      D̃_ β(ρ‖σ) = ENNReal.ofReal (Real.log (cin ^ β) / (β - 1)) := by
    have hnonneg :
        0 ≤ Real.log (cin ^ β) / (β - 1) := by
      simpa [hβ.ne', cin, sandwich_core_trace_eq_weighted_norm_rpow β hβ ρ σ] using
        (sandwichedRelRentropy_nonneg hβ0 hker)
    unfold SandwichedRelRentropy
    simpa [hβ0, hβ.ne', hker, cin,
      sandwich_core_trace_eq_weighted_norm_rpow β hβ ρ σ] using
      (ENNReal.ofReal_eq_coe_nnreal hnonneg).symm
  rw [hout, hin]
  apply ENNReal.ofReal_le_ofReal
  have hpow_le : cout ^ β ≤ cin ^ β := by
    exact Real.rpow_le_rpow hcout_pos.le hnorm (by linarith)
  have hpow_pos_out : 0 < cout ^ β := by
    exact Real.rpow_pos_of_pos hcout_pos _
  have hpow_pos_in : 0 < cin ^ β := by
    exact Real.rpow_pos_of_pos hcin_pos _
  have hlog_le : Real.log (cout ^ β) ≤ Real.log (cin ^ β) := by
    exact Real.strictMonoOn_log.monotoneOn hpow_pos_out hpow_pos_in hpow_le
  exact div_le_div_of_nonneg_right hlog_le (by linarith)

/-- The Data Processing Inequality for the Sandwiched Renyi relative entropy.
Proved in `https://arxiv.org/pdf/1306.5920`. Seems kind of involved. -/
theorem sandwichedRenyiEntropy_DPI (hα : 1 ≤ α) (ρ σ : MState d) (Φ : CPTPMap d d₂) :
    D̃_ α(Φ ρ‖Φ σ) ≤ D̃_ α(ρ‖σ) := by
  have hstrict : ∀ {β : ℝ}, 1 < β → D̃_ β(Φ ρ‖Φ σ) ≤ D̃_ β(ρ‖σ) := by
    intro β hβ
    by_cases hker : σ.M.ker ≤ ρ.M.ker
    · exact sandwichedRenyiEntropy_DPI_ker hβ ρ σ Φ hker
    · have : D̃_ β(ρ‖σ) = ⊤ := by
        unfold SandwichedRelRentropy; simp [show 0 < β from lt_trans zero_lt_one hβ, hker]
      rw [this]; exact le_top
  rcases eq_or_lt_of_le hα with rfl | hgt
  · exact sandwichedRenyiEntropy_DPI_at_one_of_gt_one ρ σ Φ (fun hβ => hstrict hβ)
  · exact hstrict hgt

private lemma weighted_norm_one_Gamma_inv_density_eq_one
    (ρ σ : MState d) (hker : σ.M.ker ≤ ρ.M.ker) :
    weighted_norm 1 σ (Gamma_inv σ ρ.M.mat) = 1 := by
  rw [weighted_norm_one_eq_trace_norm_Gamma, schattenNorm_one_eq_traceNorm]
  rw [Gamma_Gamma_inv_density hker]
  exact ρ.traceNorm_eq_1

private lemma schattenNorm_eq_of_star_mul_self_eq
    {A B : Matrix d d ℂ} {p : ℝ} (hp : 0 < p) (h : Aᴴ * A = Bᴴ * B) :
    schattenNorm A p = schattenNorm B p := by
  rw [schattenNorm_eq_sum_singularValues_rpow A hp,
    schattenNorm_eq_sum_singularValues_rpow B hp]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [singularValues, h]

private lemma schattenNorm_mul_le_schattenNorm_opNorm
    (A B : Matrix d d ℂ) {p : ℝ} (hp : 0 < p) :
    schattenNorm (A * B) p ≤ schattenNorm A p * ‖B‖ := by
  classical
  by_cases h : IsEmpty d
  · letI := h
    have hA : A = 0 := Subsingleton.elim _ _
    have hB : B = 0 := Subsingleton.elim _ _
    rw [hA, hB]
    unfold schattenNorm
    have hpinv0 : p⁻¹ ≠ 0 := inv_ne_zero hp.ne'
    simp [Real.zero_rpow hpinv0]
  · letI : Nonempty d := not_isEmpty_iff.mp h
    have hcard : 0 < Fintype.card d := Fintype.card_pos_iff.mpr ‹Nonempty d›
    rw [schattenNorm_eq_sum_singularValues_rpow (A * B) hp,
      schattenNorm_eq_sum_singularValues_rpow A hp,
      sum_singularValues_rpow_eq_sum_sorted (A * B) p,
      sum_singularValues_rpow_eq_sum_sorted A p]
    have hmul := sum_rpow_singularValues_mul_le A B hp
    have htop : singularValuesSorted B ⟨0, hcard⟩ ≤ ‖B‖ := by
      rw [singularValuesSorted_zero_eq_sup B hcard]
      rw [Finset.sup'_le_iff]
      intro i hi
      exact Matrix.singularValues_le_opNorm B i
    have hpoint :
        ∀ i : Fin (Fintype.card d),
          singularValuesSorted A i ^ p * singularValuesSorted B i ^ p ≤
            singularValuesSorted A i ^ p * ‖B‖ ^ p := by
      intro i
      have hBi : singularValuesSorted B i ≤ ‖B‖ := by
        exact ((singularValuesSorted_antitone B) (Fin.zero_le i)).trans htop
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (singularValuesSorted_nonneg B i) hBi hp.le)
        (Real.rpow_nonneg (singularValuesSorted_nonneg A i) _)
    have hsum :
        ∑ i : Fin (Fintype.card d),
            singularValuesSorted A i ^ p * singularValuesSorted B i ^ p ≤
          ∑ i : Fin (Fintype.card d),
            singularValuesSorted A i ^ p * ‖B‖ ^ p := by
      exact Finset.sum_le_sum fun i _ => hpoint i
    have hsumA_nonneg :
        0 ≤ ∑ i : Fin (Fintype.card d), singularValuesSorted A i ^ p := by
      exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValuesSorted_nonneg A i) _
    have hnormp_nonneg : 0 ≤ ‖B‖ ^ p := Real.rpow_nonneg (norm_nonneg B) _
    have hmain :
        ∑ i : Fin (Fintype.card d), singularValuesSorted (A * B) i ^ p ≤
          (∑ i : Fin (Fintype.card d), singularValuesSorted A i ^ p) * ‖B‖ ^ p := by
      refine hmul.trans ?_
      calc
        ∑ i : Fin (Fintype.card d),
            singularValuesSorted A i ^ p * singularValuesSorted B i ^ p
            ≤
              ∑ i : Fin (Fintype.card d),
                singularValuesSorted A i ^ p * ‖B‖ ^ p := hsum
        _ = (∑ i : Fin (Fintype.card d), singularValuesSorted A i ^ p) * ‖B‖ ^ p := by
              rw [Finset.sum_mul]
    have hsumAB_nonneg :
        0 ≤ ∑ i : Fin (Fintype.card d), singularValuesSorted (A * B) i ^ p := by
      exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValuesSorted_nonneg (A * B) i) _
    have hroot :=
      Real.rpow_le_rpow hsumAB_nonneg hmain (by positivity : 0 ≤ (1 / p : ℝ))
    have hnormp :
        (‖B‖ ^ p) ^ (1 / p) = ‖B‖ := by
      rw [← Real.rpow_mul (norm_nonneg B)]
      field_simp [hp.ne']
      rw [Real.rpow_one]
    calc
      (∑ i : Fin (Fintype.card d), singularValuesSorted (A * B) i ^ p) ^ (1 / p)
          ≤ ((∑ i : Fin (Fintype.card d), singularValuesSorted A i ^ p) * ‖B‖ ^ p) ^ (1 / p) := hroot
      _ = (∑ i : Fin (Fintype.card d), singularValuesSorted A i ^ p) ^ (1 / p) *
            (‖B‖ ^ p) ^ (1 / p) := by
              rw [Real.mul_rpow hsumA_nonneg hnormp_nonneg]
      _ = (∑ i : Fin (Fintype.card d), singularValuesSorted A i ^ p) ^ (1 / p) * ‖B‖ := by
            rw [hnormp]

private lemma schattenNorm_mul_le_opNorm_schattenNorm
    (A B : Matrix d d ℂ) {p : ℝ} (hp : 0 < p) :
    schattenNorm (A * B) p ≤ ‖A‖ * schattenNorm B p := by
  classical
  by_cases h : IsEmpty d
  · letI := h
    have hA : A = 0 := Subsingleton.elim _ _
    have hB : B = 0 := Subsingleton.elim _ _
    rw [hA, hB]
    unfold schattenNorm
    have hpinv0 : p⁻¹ ≠ 0 := inv_ne_zero hp.ne'
    simp [Real.zero_rpow hpinv0]
  · letI : Nonempty d := not_isEmpty_iff.mp h
    have hcard : 0 < Fintype.card d := Fintype.card_pos_iff.mpr ‹Nonempty d›
    rw [schattenNorm_eq_sum_singularValues_rpow (A * B) hp,
      schattenNorm_eq_sum_singularValues_rpow B hp,
      sum_singularValues_rpow_eq_sum_sorted (A * B) p,
      sum_singularValues_rpow_eq_sum_sorted B p]
    have hmul := sum_rpow_singularValues_mul_le A B hp
    have htop : singularValuesSorted A ⟨0, hcard⟩ ≤ ‖A‖ := by
      rw [singularValuesSorted_zero_eq_sup A hcard]
      rw [Finset.sup'_le_iff]
      intro i hi
      exact Matrix.singularValues_le_opNorm A i
    have hpoint :
        ∀ i : Fin (Fintype.card d),
          singularValuesSorted A i ^ p * singularValuesSorted B i ^ p ≤
            ‖A‖ ^ p * singularValuesSorted B i ^ p := by
      intro i
      have hAi : singularValuesSorted A i ≤ ‖A‖ := by
        exact ((singularValuesSorted_antitone A) (Fin.zero_le i)).trans htop
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (singularValuesSorted_nonneg A i) hAi hp.le)
        (Real.rpow_nonneg (singularValuesSorted_nonneg B i) _)
    have hsum :
        ∑ i : Fin (Fintype.card d),
            singularValuesSorted A i ^ p * singularValuesSorted B i ^ p ≤
          ∑ i : Fin (Fintype.card d),
            ‖A‖ ^ p * singularValuesSorted B i ^ p := by
      exact Finset.sum_le_sum fun i _ => hpoint i
    have hsumB_nonneg :
        0 ≤ ∑ i : Fin (Fintype.card d), singularValuesSorted B i ^ p := by
      exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValuesSorted_nonneg B i) _
    have hnormp_nonneg : 0 ≤ ‖A‖ ^ p := Real.rpow_nonneg (norm_nonneg A) _
    have hmain :
        ∑ i : Fin (Fintype.card d), singularValuesSorted (A * B) i ^ p ≤
          ‖A‖ ^ p * (∑ i : Fin (Fintype.card d), singularValuesSorted B i ^ p) := by
      refine hmul.trans ?_
      calc
        ∑ i : Fin (Fintype.card d),
            singularValuesSorted A i ^ p * singularValuesSorted B i ^ p
            ≤
              ∑ i : Fin (Fintype.card d),
                ‖A‖ ^ p * singularValuesSorted B i ^ p := hsum
        _ = ‖A‖ ^ p * (∑ i : Fin (Fintype.card d), singularValuesSorted B i ^ p) := by
              rw [Finset.mul_sum]
    have hroot :=
      Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValuesSorted_nonneg (A * B) i) _)
        hmain (by positivity : 0 ≤ (1 / p : ℝ))
    have hnormp :
        (‖A‖ ^ p) ^ (1 / p) = ‖A‖ := by
      rw [← Real.rpow_mul (norm_nonneg A)]
      field_simp [hp.ne']
      rw [Real.rpow_one]
    calc
      (∑ i : Fin (Fintype.card d), singularValuesSorted (A * B) i ^ p) ^ (1 / p)
          ≤ (‖A‖ ^ p * ∑ i : Fin (Fintype.card d), singularValuesSorted B i ^ p) ^ (1 / p) := hroot
      _ = (‖A‖ ^ p) ^ (1 / p) *
            (∑ i : Fin (Fintype.card d), singularValuesSorted B i ^ p) ^ (1 / p) := by
              rw [Real.mul_rpow hnormp_nonneg hsumB_nonneg]
      _ = ‖A‖ * (∑ i : Fin (Fintype.card d), singularValuesSorted B i ^ p) ^ (1 / p) := by
            rw [hnormp]

private lemma schattenNorm_sandwich_le {n : Type*} [Fintype n] [DecidableEq n]
    {S M : Matrix n n ℂ} {p : ℝ} (hp : 0 < p) (hS : ‖S‖ ≤ 1) :
    schattenNorm (S * M * S) p ≤ schattenNorm M p := by
  have hnonneg : 0 ≤ schattenNorm M p := schattenNorm_nonneg _ _
  have hSM : schattenNorm (S * M) p ≤ schattenNorm M p := by
    calc
      schattenNorm (S * M) p ≤ ‖S‖ * schattenNorm M p :=
        schattenNorm_mul_le_opNorm_schattenNorm S M hp
      _ ≤ 1 * schattenNorm M p := by
            exact mul_le_mul_of_nonneg_right hS hnonneg
      _ = schattenNorm M p := by ring
  calc
    schattenNorm (S * M * S) p ≤ schattenNorm (S * M) p * ‖S‖ :=
      schattenNorm_mul_le_schattenNorm_opNorm (S * M) S hp
    _ ≤ schattenNorm M p * ‖S‖ := by
          exact mul_le_mul_of_nonneg_right hSM (norm_nonneg _)
    _ ≤ schattenNorm M p * 1 := by
          exact mul_le_mul_of_nonneg_left hS hnonneg
    _ = schattenNorm M p := by ring

private lemma abs_trace_weighted_pair_le {p : ℝ} (hp : 1 < p)
    (σ : MState d) (X Y : Matrix d d ℂ) :
    ‖(Y * Gamma σ X).trace‖ ≤ weighted_norm (p / (p - 1)) σ Y * weighted_norm p σ X := by
  set q : ℝ := p / (p - 1)
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 < q := by
    dsimp [q]
    have hp1 : 0 < p - 1 := by linarith
    exact div_pos hp0 hp1
  have hpq : 1 / q + 1 / p = (1 : ℝ) := by
    dsimp [q]
    field_simp [show p - 1 ≠ 0 by linarith, show p ≠ 0 by linarith]
    ring
  have hsum_eq : (1 / (2 * q : ℝ)) + (1 / (2 * p : ℝ)) = (1 / 2 : ℝ) := by
    dsimp [q]
    field_simp [show p - 1 ≠ 0 by linarith, show p ≠ 0 by linarith]
    ring
  let Sq : Matrix d d ℂ := (σ.M ^ (1 / (2 * q : ℝ))).mat
  let Sp : Matrix d d ℂ := (σ.M ^ (1 / (2 * p : ℝ))).mat
  let SY : Matrix d d ℂ := Sq * Y * Sq
  let SX : Matrix d d ℂ := Sp * X * Sp
  have hsum_ne : (1 / (2 * q : ℝ)) + (1 / (2 * p : ℝ)) ≠ 0 := by
    rw [hsum_eq]
    norm_num
  have hleft :
      Sq * Sp =
        (σ.M ^ (1 / 2 : ℝ)).mat := by
    dsimp [Sq, Sp]
    calc
      (σ.M ^ (1 / (2 * q : ℝ))).mat * (σ.M ^ (1 / (2 * p : ℝ))).mat
          = (σ.M ^ ((1 / (2 * q : ℝ)) + (1 / (2 * p : ℝ)))).mat := by
              simpa using (HermitianMat.mat_rpow_add (A := σ.M) σ.nonneg
                (p := 1 / (2 * q : ℝ)) (q := 1 / (2 * p : ℝ)) hsum_ne).symm
      _ = (σ.M ^ (1 / 2 : ℝ)).mat := by rw [hsum_eq]
  have hright :
      Sp * Sq =
        (σ.M ^ (1 / 2 : ℝ)).mat := by
    dsimp [Sq, Sp]
    calc
      (σ.M ^ (1 / (2 * p : ℝ))).mat * (σ.M ^ (1 / (2 * q : ℝ))).mat
          = (σ.M ^ ((1 / (2 * p : ℝ)) + (1 / (2 * q : ℝ)))).mat := by
              simpa [add_comm] using (HermitianMat.mat_rpow_add (A := σ.M) σ.nonneg
                (p := 1 / (2 * p : ℝ)) (q := 1 / (2 * q : ℝ)) (by simpa [add_comm] using hsum_ne)).symm
      _ = (σ.M ^ (1 / 2 : ℝ)).mat := by rw [add_comm, hsum_eq]
  have htrace :
      (SY * SX).trace = (Y * Gamma σ X).trace := by
    dsimp [SY, SX, Sq, Sp, Gamma]
    calc
      (((σ.M ^ (1 / (2 * q : ℝ))).mat * Y * (σ.M ^ (1 / (2 * q : ℝ))).mat) *
          ((σ.M ^ (1 / (2 * p : ℝ))).mat * X * (σ.M ^ (1 / (2 * p : ℝ))).mat)).trace
          =
            ((σ.M ^ (1 / (2 * q : ℝ))).mat *
              (Y * (σ.M ^ (1 / (2 * q : ℝ))).mat * (σ.M ^ (1 / (2 * p : ℝ))).mat *
                X * (σ.M ^ (1 / (2 * p : ℝ))).mat)).trace := by
                simp [Matrix.mul_assoc]
      _ =
            (Y * (σ.M ^ (1 / (2 * q : ℝ))).mat * (σ.M ^ (1 / (2 * p : ℝ))).mat *
              X * (σ.M ^ (1 / (2 * p : ℝ))).mat * (σ.M ^ (1 / (2 * q : ℝ))).mat).trace := by
                rw [Matrix.trace_mul_cycle]
                simp [Matrix.mul_assoc]
      _ = (Y * (((σ.M ^ (1 / (2 * q : ℝ))).mat * (σ.M ^ (1 / (2 * p : ℝ))).mat)) *
              X * (((σ.M ^ (1 / (2 * p : ℝ))).mat * (σ.M ^ (1 / (2 * q : ℝ))).mat))).trace := by
            simp [Matrix.mul_assoc]
      _ = (Y * (σ.M ^ (1 / 2 : ℝ)).mat * X * (σ.M ^ (1 / 2 : ℝ)).mat).trace := by
            rw [hleft, hright]
      _ = (Y * Gamma σ X).trace := by
            simp [Gamma, Matrix.mul_assoc, HermitianMat.rpow_eq_cfc]
  calc
    ‖(Y * Gamma σ X).trace‖ = ‖(SY * SX).trace‖ := by rw [htrace]
    _ ≤ (SY * SX).traceNorm := Matrix.abs_trace_le_traceNorm (SY * SX)
    _ = schattenNorm (SY * SX) 1 := by rw [← schattenNorm_one_eq_traceNorm]
    _ ≤ schattenNorm SY q * schattenNorm SX p := by
          have hpq' : 1 / (1 : ℝ) = 1 / q + 1 / p := by simpa using hpq.symm
          exact schattenNorm_mul_le SY SX (by norm_num) hq0 hp0 hpq'
    _ = weighted_norm q σ Y * weighted_norm p σ X := by
          simp [weighted_norm, q, SY, SX, Sq, Sp, Matrix.mul_assoc, HermitianMat.rpow_eq_cfc]
