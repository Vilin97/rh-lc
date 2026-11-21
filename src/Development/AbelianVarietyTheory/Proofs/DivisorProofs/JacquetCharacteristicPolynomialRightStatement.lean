module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetCharacteristicPolynomialRight
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_characteristic_polynomial_right : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.GeometricLemmaFiltration → ∀ (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → ∀ (u v : ℕ) (m : Type) [Fintype m] [DecidableEq m] (e : m ⊕ Fin 1 ≃ Fin (u + v)) (ϖ : kˣ), Polynomial.aeval (jac₂ e (prod₂ (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)) (1, GeneralLinearGroup.scalar (Fin 1) ϖ)) ((Polynomial.X - Polynomial.C (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ)) * (Polynomial.X - Polynomial.C (((χ₂ * absPow k (((v : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ))) = 0 := by
  intro k _ _ _ _ hG χ₁ χ₂ h₁ h₂ u v m _ _ e ϖ
  have hcont : Continuous ((leviTwo k (Fin u) (Fin v)).symm.toMonoidHom) :=
    (continuous_apply false).prodMk (continuous_apply true)
  have hρ' : IsSmooth ((extTensor (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)).comp
      (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom) :=
    isSmooth_comp (isSmooth_extTensor ((isSmooth_ofChar_iff _).2 h₁.detChar)
      ((isSmooth_ofChar_iff _).2 h₂.detChar)) _ hcont
  have hJ : JacquetOfInducedFiltration k := hG k
  obtain ⟨N, b, hb⟩ := hJ Bool Bool (Fin (u + v)) (Two (Fin u) (Fin v)) (Two m (Fin 1))
    (two (stdSum (rfl : u + v = u + v))) (two e)
  have hb' := hb (TensorProduct ℂ ℂ ℂ)
    ((extTensor (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)).comp
      (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom) hρ'
  have h0 := hb'.choose_spec.2.1
  have hN := hb'.choose_spec.2.2.1
  have hS := hb'.choose_spec.2.2.2
  let cv : SizeMatrix (Two (Fin u) (Fin v)) (Two m (Fin 1)) → ℂ := fun B =>
    if B.1 false true = 1 then (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ)
    else (((χ₂ * absPow k (((v : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ)
  have hfil := GlobalTheory.ScalRight.aeval_prod_eq_zero_of_filtration _
    (leviTwo k m (Fin 1) (1, GeneralLinearGroup.scalar (Fin 1) ϖ))
    N hb'.choose h0 hN (fun t => cv (b t))
    (fun t x hx => GlobalTheory.ScalRight.sub_smul_mem_of_equiv _ _
      (hS t (b t).nonempty_rows.some (b t).nonempty_cols.some).some
      (leviTwo k m (Fin 1) (1, GeneralLinearGroup.scalar (Fin 1) ϖ)) (cv (b t))
      (GlobalTheory.ScalRight.cell_scalar χ₁ χ₂ u v m ϖ (b t) _ _) x hx)
  have := Fintype.ofFinite (SizeMatrix (Two (Fin u) (Fin v)) (Two m (Fin 1)))
  rw [show (∏ t, (Polynomial.X - Polynomial.C (cv (b t)))) =
      ∏ B, (Polynomial.X - Polynomial.C (cv B)) from
    Equiv.prod_comp b (fun B => Polynomial.X - Polynomial.C (cv B))] at hfil
  let φB : SizeMatrix (Two (Fin u) (Fin v)) (Two m (Fin 1)) → Bool := fun B => decide (B.1 false true = 1)
  let fB : Bool → Polynomial ℂ := fun x => Polynomial.X - Polynomial.C
    (if x then (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ)
      else (((χ₂ * absPow k (((v : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ))
  have hinj : Function.Injective φB := by
    intro B B' hBB
    have r0 := B.2.1 false
    have r1 := B.2.1 true
    have c1 := B.2.2 true
    have r0' := B'.2.1 false
    have r1' := B'.2.1 true
    have c1' := B'.2.2 true
    simp only [Fintype.sum_bool] at r0 r1 c1 r0' r1' c1'
    have hu : Fintype.card (Two (Fin u) (Fin v) false) = u := Fintype.card_fin u
    have hv : Fintype.card (Two (Fin u) (Fin v) true) = v := Fintype.card_fin v
    have h1 : Fintype.card (Two m (Fin 1) true) = 1 := Fintype.card_fin 1
    rw [hu] at r0 r0'
    rw [hv] at r1 r1'
    rw [h1] at c1 c1'
    have hd : (B.1 false true = 1) ↔ (B'.1 false true = 1) := by simpa [φB] using hBB
    apply Subtype.ext
    funext i j
    cases i <;> cases j <;> omega
  have hdvd : (∏ B, (Polynomial.X - Polynomial.C (cv B))) ∣
      (Polynomial.X - Polynomial.C (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ)) *
        (Polynomial.X - Polynomial.C (((χ₂ * absPow k (((v : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ)) := by
    have e1 : (∏ B, (Polynomial.X - Polynomial.C (cv B))) = ∏ x ∈ Finset.univ.image φB, fB x := by
      rw [Finset.prod_image fun B _ B' _ h => hinj h]
      refine Finset.prod_congr rfl fun B _ => ?_
      by_cases h : B.1 false true = 1 <;> simp [cv, fB, φB, h]
    have e2 : (Polynomial.X - Polynomial.C (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ)) *
        (Polynomial.X - Polynomial.C (((χ₂ * absPow k (((v : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ)) =
          ∏ x, fB x := by
      rw [Fintype.prod_bool]
      simp only [fB, ite_true, Bool.false_eq_true, ite_false]
    rw [e1, e2]
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
  obtain ⟨r, hr⟩ := hdvd
  rw [hr, map_mul]
  exact mul_eq_zero_of_left hfil _
