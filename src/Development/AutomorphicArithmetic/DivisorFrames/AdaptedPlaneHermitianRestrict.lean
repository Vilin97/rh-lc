module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAtOfPiInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleWithArchimedeanComponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartNeZero
public import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBDefs

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open scoped Classical

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem schr_schr' {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (h : w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = schr ψ (w + w') φ := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x w.1 w'.1]
  congr 2
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (⅟(2 : R)) * h - (w.1 ⬝ᵥ w'.2) * h2

private theorem rho_rho' {R : Type} [CommRing R] [Invertible (2 : R)] {V : Type} [AddCommGroup V] [Module R V]
    {Bf : V → V → R} {κ : Type} [Fintype κ] (d : Darboux Bf κ) (ψ : AddChar R ℂ) (w w' : V) (h : Bf w w' = 0)
    (φ : (κ → R) → ℂ) : d.rho ψ w (d.rho ψ w' φ) = d.rho ψ (w + w') φ := by
  simp only [Darboux.rho]
  rw [schr_schr', map_add (f := _)]
  have := d.form w w'
  rw [h] at this
  exact sub_eq_zero.mp this.symm

private theorem om_rho {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ}
    (hψ : IsStd ψ) {χX χW : Chr F E} {om : Rep σ X W} (hW : M.IsWeil ψ χX χW om) {g : UA σ X.J}
    (hex : ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (g, 1)) f f₁)
    (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (f : SInf F (Fin n × Fin d)) :
    locOpInf (M.co.rho ψ (partInf F (mat g * u))) (locOpInf (om (g, 1)) f) =
      locOpInf (om (g, 1)) (locOpInf (M.co.rho ψ (partInf F u)) f) := by
  have hS := IsUWeilPair.isUSplitting hW
  have hact : actAB (cA σ) ((g, 1) : UA σ X.J × UA σ W.J) (partInf F u) = partInf F (mat g * u) := by
    change mat g * (partInf F u) * (mat (1 : UA σ W.J))ᵀ = _
    have h1 : mat (1 : UA σ W.J) = 1 := rfl
    rw [h1, Matrix.transpose_one, Matrix.mul_one, partInf, partInf, Matrix.mul_smul]
  obtain ⟨r, h0, hr⟩ := exists_rest_inf F (Fin n × Fin d)
  refine DFunLike.coe_injective (eq_of_tens_inf h0 (hr f).1 ?_)
  have h2 := hS.impl (g, 1) (partInf F u) _ (hr f).2
  rw [hact, (locOpInf_rho M.co hψ u f).1 r (hr _), acts_locOpInf (hex _) r (hr _), acts_locOpInf (hex _) r (hr _),
    (locOpInf_rho M.co hψ _ _).1 r (hr _)] at h2
  exact h2.symm

private theorem partInf_vec {n d : ℕ} (a : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (w : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    partInf F (Matrix.vecMulVec a w) = Matrix.vecMulVec (realAd F 1 • a) w := by
  rw [partInf, Matrix.smul_vecMulVec]

private theorem rho_add {B : Base F E} {n d d₁ j₀ j₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}
    (M : Model σ X W) {H' : Plane E d d₁} (hH' : H'.IsAdapted σ B W W₁ j₀ j₁) (hψ : IsStd B.ψ)
    (a b : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (f : SInf F (Fin n × Fin d)) :
    locOpInf (M.co.rho B.ψ (partInf F (Matrix.vecMulVec a (incV F H'.x))))
      (locOpInf (M.co.rho B.ψ (partInf F (Matrix.vecMulVec b (incV F H'.x)))) f) =
    locOpInf (M.co.rho B.ψ (partInf F (Matrix.vecMulVec (a + b) (incV F H'.x)))) f := by
  obtain ⟨r, h0, hr⟩ := exists_rest_inf F (Fin n × Fin d)
  refine DFunLike.coe_injective (eq_of_tens_inf h0 (hr f).1 ?_)
  rw [← (locOpInf_rho M.co hψ _ _).1 r (hr _), ← (locOpInf_rho M.co hψ _ _).1 r (hr _),
    ← (locOpInf_rho M.co hψ _ _).1 r (hr _), rho_rho']
  · rw [Matrix.add_vecMulVec, partInf, partInf, partInf, smul_add]
  · rw [partInf_vec, partInf_vec, GlobalTheory.ArchUniq.Coord.vecMulVec_eq_mul, GlobalTheory.ArchUniq.Coord.vecMulVec_eq_mul]
    exact GlobalTheory.ArchUniq.Coord.sympM_eq_zero _ _ (GlobalTheory.ArchUniq.Coord.gram_xx hH') _ _

private theorem ei_inv {B : Base F E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hψ : IsStd B.ψ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ)
    {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E} {I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))}
    {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} (he : IsEv B M M₁ ι ι' I e) {ei} {ev} (hL : IsLocPart M M₁ e ei ev)
    (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (hu : partInf F u ∈ I) (f : SInf F (Fin n × Fin d)) :
    ei (locOpInf (M.co.rho B.ψ (partInf F u)) f) = ei f := by
  have hSB : ∀ v, M.vac v ∈ SB _ := fun v => (hM.vac v).1
  have hei : ∀ f, e (pure f M.vac) = pure (ei f) M₁.vac := fun f => by
    rw [hL.2.2 f _ hSB (Eventually.of_forall fun _ => rfl)]
    exact congrArg _ (funext fun v => (hL.2.1 v).1)
  have hp := GlobalTheory.TensUniq.pure_mem_schA f _ hSB hM.std
  have h1 : M.co.rho B.ψ (partInf F u) (pure f M.vac) = pure (locOpInf (M.co.rho B.ψ (partInf F u)) f) M.vac :=
    (locOpInf_rho M.co hψ u f).1 _ ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add _ x z hz, hp⟩
  refine GlobalTheory.EvZeroInf.eq_of_pure_eq _ (fun v => (hM₁.vac v).2.1) hM₁.std _ _ ?_
  rw [← hei, ← hei, ← h1]
  exact he.inv _ hu _ hp

omit [NumberField E] in
private theorem formA_inc {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    incV F x ⬝ᵥ (incM F J *ᵥ fun i => cA σ (incV F y i)) = inclR (F := F) (AF F) (form σ J x y) := by
  have h : ∀ a : E, cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := fun a => rfl
  simp [incV, incM, form, Matrix.mulVec, dotProduct, h]

private theorem coef_eq {B : Base F E} {n n₁ r s i₀ i₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁}
    (hB : B.IsGood σ) (hS : X.IsHerm σ B r s) (hA : H.IsAdapted σ B X X₁ i₀ i₁) (a t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (u : Fin n₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    cA σ (incV F H.x ⬝ᵥ (incM F X.J *ᵥ fun i => cA σ ((a • incV F H.x + incM F H.ι *ᵥ u + t • incV F H.y) i))) = t := by
  have hσ : ∀ z, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hc : ∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), cA σ (cA σ z) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [cA, hσ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hsym : ∀ x y : Fin n → E, form σ X.J y x = σ (form σ X.J x y) := fun x y => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hS.herm, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hu : incM F H.ι *ᵥ u = ∑ j, u j • incV F (H.ι *ᵥ Pi.single j 1) := by
    funext i
    simp [incV, incM, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
  have e : (fun i => cA σ ((a • incV F H.x + incM F H.ι *ᵥ u + t • incV F H.y) i)) =
      cA σ a • (fun i => cA σ (incV F H.x i)) + ∑ j, cA σ (u j) • (fun i => cA σ (incV F (H.ι *ᵥ Pi.single j 1) i)) +
        cA σ t • fun i => cA σ (incV F H.y i) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hu, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, map_add (f := _), map_mul, map_sum]
  have h0 : ∀ v, form σ X.J H.x (H.ι *ᵥ v) = 0 := fun v => by rw [hsym, (hA.orth v).1, map_zero]
  rw [e]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_add, dotProduct_sum, dotProduct_smul,
    formA_inc, hA.xx, hA.xy, h0, map_zero, map_one, smul_zero, Finset.sum_const_zero, zero_add, smul_eq_mul, mul_one, mul_zero, hc]


end SlopeTestRemainingChoices
