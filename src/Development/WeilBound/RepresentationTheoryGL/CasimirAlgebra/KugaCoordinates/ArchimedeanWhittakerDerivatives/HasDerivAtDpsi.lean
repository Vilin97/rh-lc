module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.ClozelCohomologicalOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ArchimedeanWhittakerDerivatives.ContinuousInfGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCoordinateMatrixEquivariant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardAdelicAddCharStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageOfIsCuspFormStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerLawUpperTriangularUnipotentAdelic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Divisors.Tpr
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ArchimedeanWhittakerDerivatives.ExistsUpperUnitary
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ArchimedeanWhittakerDerivatives.HasDerivAtOfIntRel
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ArchimedeanWhittakerDerivatives.HasDerivAtOfMulHom
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ArchimedeanWhittakerDerivatives.ConjSingleApply

section

@[expose] public section

noncomputable section

namespace PositivityTheory.Rg.Cz

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem law_inf (ψ : AddChar (Ad E) ℂ) (f : GA E a → ℂ)
    (hf : ∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), f (blkU y * g) = ψ (dot (eLast a k) y) * f g)
    (u : GL (Fin a) (Cinf E)) (hl : ∀ i j : Fin a, j < i → u.val i j = 0) (hd : ∀ j, u.val j j = 1) (g : GA E a) :
    f (infGL E a u * g) = ψ (sInf E (sd u.val)) * f g := by
  rw [GlobalTheory.CuspGeneric.tri_law E a ψ f hf (infGL E a u) ?_ ?_ g]
  · congr 2

    rw [sd, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : (p.2 : ℕ) = p.1 + 1 := (Finset.mem_filter.1 hp).2
    have hne : p.1 ≠ p.2 := fun h => by rw [h] at hp'; omega
    rw [infGL_apply, Matrix.one_apply_ne hne, Matrix.one_apply_ne hne, map_zero, sub_zero, zero_add]
  · intro i j hij
    rw [infGL_apply, Matrix.one_apply_ne hij.ne', Matrix.one_apply_ne hij.ne', hl i j hij, map_zero]
    simp
  · intro j
    rw [infGL_apply, hd, Matrix.one_apply_eq, Matrix.one_apply_eq]
    simp

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem inv_upper (b : GL (Fin a) (Cinf E)) (hb : ∀ i j : Fin a, j < i → b.val i j = 0) :
    ∀ i j : Fin a, j < i → (b⁻¹).val i j = 0 := by
  let _ : Invertible b.val := b.invertible
  have h : Matrix.BlockTriangular b.val id := fun i j hij => hb i j hij
  intro i j hij
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular h hij

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem diag_inv (b : GL (Fin a) (Cinf E)) (hb : ∀ i j : Fin a, j < i → b.val i j = 0) (i : Fin a) :
    b.val i i * (b⁻¹).val i i = 1 := by
  have h := congrFun (congrFun (Units.mul_inv b) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i] at h
  · exact h
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h1 | h1
    · rw [hb i k h1, zero_mul]
    · rw [inv_upper b hb k i h1, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem single_sq (p q : Fin a) (h : p ≠ q) (x : Cinf E) : Matrix.single p q x * Matrix.single p q x = 0 := by
  exact Matrix.single_mul_single_of_ne (h := h.symm) ..

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem conj_single_apply (b c : Matrix (Fin a) (Fin a) (Cinf E)) (p q : Fin a) (x : Cinf E) (i j : Fin a) :
    (b * Matrix.single p q x * c) i j = b i p * x * c q j := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, mul_assoc]

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem conj_single_upper (b : GL (Fin a) (Cinf E)) (hb : ∀ i j : Fin a, j < i → b.val i j = 0) (p q : Fin a)
    (hpq : p < q) (x : Cinf E) : ∀ i j : Fin a, j ≤ i → (b.val * Matrix.single p q x * (b⁻¹).val) i j = 0 := by
  intro i j hji
  rw [conj_single_apply]
  rcases lt_or_ge p i with h1 | h1
  · rw [hb i p h1]; simp
  rcases lt_or_ge j q with h2 | h2
  · rw [inv_upper b hb q j h2]; simp
  · exact absurd (lt_of_le_of_lt h1 (lt_of_lt_of_le hpq h2)) (not_lt.2 hji)

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem sd_conj_single (b : GL (Fin a) (Cinf E)) (hb : ∀ i j : Fin a, j < i → b.val i j = 0) (p q : Fin a)
    (hpq : p < q) (x : Cinf E) :
    sd (b.val * Matrix.single p q x * (b⁻¹).val) = if (p : ℕ) + 1 = q then b.val p p * x * (b⁻¹).val q q else 0 := by
  have key : ∀ r : Fin a × Fin a, (r.2 : ℕ) = r.1 + 1 → r ≠ (p, q) →
      (b.val * Matrix.single p q x * (b⁻¹).val) r.1 r.2 = 0 := by
    intro r hr hne
    rw [conj_single_apply]
    rcases lt_or_ge p r.1 with h1 | h1
    · rw [hb _ _ h1]; simp
    rcases lt_or_ge r.2 q with h2 | h2
    · rw [inv_upper b hb _ _ h2]; simp
    · exfalso; apply hne
      have e1 : (r.1 : ℕ) ≤ p := h1
      have e2 : (q : ℕ) ≤ r.2 := h2
      have e3 : (p : ℕ) < q := hpq
      exact Prod.ext (Fin.ext (show (r.1 : ℕ) = p by omega)) (Fin.ext (show (r.2 : ℕ) = q by omega))
  unfold sd
  split_ifs with h
  · rw [Finset.sum_eq_single (p, q)]
    · exact conj_single_apply _ _ _ _ _ _ _
    · intro r hr hne; exact key r (Finset.mem_filter.1 hr).2 hne
    · intro hn; exfalso; apply hn
      exact Finset.mem_filter.2 ⟨Finset.mem_univ (p, q), h.symm⟩
  · apply Finset.sum_eq_zero
    intro r hr
    apply key r (Finset.mem_filter.1 hr).2
    rintro rfl; exact h (Finset.mem_filter.1 hr).2.symm

theorem law_conj (ψ : AddChar (Ad E) ℂ) (f : GA E a → ℂ)
    (hf : ∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), f (blkU y * g) = ψ (dot (eLast a k) y) * f g)
    (b : GL (Fin a) (Cinf E)) (M : Matrix (Fin a) (Fin a) (Cinf E)) (hM : M * M = 0)
    (hMu : ∀ i j : Fin a, j ≤ i → (b.val * M * (b⁻¹).val) i j = 0) (t : ℝ) :
    f (infGL E a b * infGL E a (cu M hM t)) = ψ (sInf E (t • sd (b.val * M * (b⁻¹).val))) * f (infGL E a b) := by
  set N := b.val * M * (b⁻¹).val with hN
  have hu : (b * cu M hM t * b⁻¹).val = 1 + t • N := by
    rw [Units.val_mul, Units.val_mul, cu_val, mul_add, mul_one, add_mul, Units.mul_inv, mul_smul_comm,
      smul_mul_assoc]
  have e : infGL E a b * infGL E a (cu M hM t) = infGL E a (b * cu M hM t * b⁻¹) * infGL E a b := by
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  have hl : ∀ i j : Fin a, j < i → (b * cu M hM t * b⁻¹).val i j = 0 := by
    intro i j hij
    rw [hu, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hij.ne', hMu i j hij.le, smul_zero, add_zero]
  have hd : ∀ j, (b * cu M hM t * b⁻¹).val j j = 1 := by
    intro j
    rw [hu, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, hMu j j le_rfl, smul_zero, add_zero]
  rw [e, law_inf ψ f hf _ hl hd, hu]
  congr 3
  unfold sd
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : (p.2 : ℕ) = p.1 + 1 := (Finset.mem_filter.1 hp).2
  have hne : p.1 ≠ p.2 := fun h => by rw [h] at hp'; omega
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hne, zero_add]

end PositivityTheory.Rg.Cz
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ArchimedeanWhittakerDerivatives.ContinuousAtEmb

section

@[expose] public section

noncomputable section

namespace PositivityTheory.Rg.Cz

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric GlobalTheory.WigAlg

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem atEmb_add (τ : E →+* ℂ) (z w : ℂ) : atEmb τ (z + w) = atEmb τ z + atEmb τ w := by
  rw [atEmb_eq τ (z + w), atEmb_eq τ z, atEmb_eq τ w, Complex.add_re, Complex.add_im, add_smul, add_smul]
  abel

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem atEmb_real_mul (τ : E →+* ℂ) (t : ℝ) (z : ℂ) : atEmb τ (t * z) = t • atEmb τ z := by
  rw [atEmb_eq τ (t * z), atEmb_eq τ z, Complex.re_ofReal_mul, Complex.im_ofReal_mul, smul_add, smul_smul, smul_smul]

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_atEmb (τ : E →+* ℂ) : Continuous (atEmb τ) := by
  have e : atEmb τ = fun z : ℂ => z.re • atEmb τ 1 + z.im • atEmb τ Complex.I := funext fun z => atEmb_eq τ z
  rw [e]
  exact (Complex.continuous_re.smul continuous_const).add (Complex.continuous_im.smul continuous_const)

theorem continuous_sInf' : Continuous (sInf E) :=
  ((continuous_infEq E).prodMk continuous_const : Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))

theorem psi_nontriv {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (τ : E →+* ℂ) : ∃ z : ℂ, ψ (sInf E (atEmb τ z)) ≠ 1 := by
  classical
  haveI : Nontrivial (Af E) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
    let v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) :=
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩
    refine ⟨0, 1, fun h => ?_⟩
    have h2 : (0 : v.adicCompletion E) = 1 := congrArg (fun x : Af E => x v) h
    exact zero_ne_one h2
  by_contra hc
  push Not at hc
  have hpi : ∀ x, pInf E (sInf E x) = x := fun x => (infEq E).symm_apply_apply x
  have hpf : ∀ x, pFin E (sInf E x) = 0 := fun x => rfl
  have key : ∀ c : E, ψ (sInf E (atEmb τ 1) * algebraMap E (Ad E) c) = 1 := fun c => by
    have e : sInf E (atEmb τ 1) * algebraMap E (Ad E) c =
        sInf E (atEmb τ (coord τ (pInf E (algebraMap E (Ad E) c)) * 1)) :=
      ad_ext (by rw [map_mul, hpi, hpi, ← mul_embeddingScalar_eq_coord_mul, mul_comm]) (by rw [map_mul, hpf, hpf, zero_mul])
    rw [e]
    exact hc _
  obtain ⟨d, hd⟩ := hψ.ann _ key
  have hd0 : d = 0 := by
    have h1 := congrArg (pFin E) hd
    rw [hpf] at h1
    have h2 : pFin E (algebraMap E (Ad E) d) = algebraMap E (Af E) d := rfl
    rw [h2] at h1
    exact (algebraMap E (Af E)).injective (h1.symm.trans (map_zero _).symm)
  rw [hd0, map_zero] at hd
  have h3 := congrArg (fun x => pInf E x (InfinitePlace.mk τ)) hd
  simp only [hpi, map_zero, Pi.zero_apply] at h3
  unfold atEmb at h3
  rw [Pi.single_eq_same] at h3
  split_ifs at h3 <;> simp at h3

end PositivityTheory.Rg.Cz
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ArchimedeanWhittakerDerivatives.HasDerivAtDpsi

section

@[expose] public section

noncomputable section

namespace PositivityTheory.Rg.Cz

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric GlobalTheory.CuspRep.Generic GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def dpsi (ψ : AddChar (Ad E) ℂ) (Z : Cinf E) : ℂ := deriv (fun t : ℝ => ψ (sInf E (t • Z))) 0

theorem hasDerivAt_dpsi {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (Z : Cinf E) :
    HasDerivAt (fun t : ℝ => ψ (sInf E (t • Z))) (dpsi ψ Z) 0 := by
  obtain ⟨c, hc⟩ := hasDerivAt_of_mulHom (fun t : ℝ => ψ (sInf E (t • Z)))
    (hψ.cont.comp (continuous_sInf'.comp (continuous_id.smul continuous_const)))
    (by simp only [zero_smul, map_zero, AddChar.map_zero_eq_one])
    (fun s t => by simp only [add_smul, map_add (f := _), AddChar.map_add_eq_mul])
  have h := hc 0
  simp only [zero_smul, map_zero, AddChar.map_zero_eq_one, mul_one] at h
  rw [dpsi, h.deriv]
  exact h

theorem dpsi_zero (ψ : AddChar (Ad E) ℂ) : dpsi ψ (0 : Cinf E) = 0 := by
  simp [dpsi]

theorem whit_lie_eq {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (π : CuspSub E a) (b : GL (Fin a) (Cinf E))
    (M : Matrix (Fin a) (Fin a) (Cinf E)) (hM : M * M = 0)
    (hMu : ∀ i j : Fin a, j ≤ i → (b.val * M * (b⁻¹).val) i j = 0) (φ : π.V) :
    whit ψ (a - 1) (lieOp π (toL M) φ).1.1 (infGL E a b) =
      dpsi ψ (sd (b.val * M * (b⁻¹).val)) * whit ψ (a - 1) φ.1.1 (infGL E a b) := by
  have hg : ∀ φ : π.V, Good ψ (a - 1) φ.1.1 := fun φ => GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ φ.1 (π.cusp _ φ.2)
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  have hrel : IntRel M hM φ.1.1 (lieOp π (toL M) φ).1.1 := intRel_sm M hM φ.1
  have hD := hasDerivAt_of_intRel M hM (whit_good hψ (a - 1) h0 (hg (lieOp π (toL M) φ))).1.cont
    (intRel_whit hψ M hM (a - 1) h0 (hg φ) (hg _) hrel) (infGL E a b)
  have he : (fun t => whit ψ (a - 1) φ.1.1 (infGL E a b * infGL E a (cu M hM t))) =
      fun t : ℝ => ψ (sInf E (t • sd (b.val * M * (b⁻¹).val))) * whit ψ (a - 1) φ.1.1 (infGL E a b) :=
    funext fun t => law_conj ψ _ (whit_good hψ (a - 1) h0 (hg φ)).1.law b M hM hMu t
  rw [he] at hD
  exact hD.unique ((hasDerivAt_dpsi hψ _).mul_const _)

theorem whitLie_holds : WhitLie := by
  intro E _ _ _ a π
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_standardAdelicAddChar E
  have hg : ∀ φ : π.V, Good ψ (a - 1) φ.1.1 := fun φ => GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ φ.1 (π.cusp _ φ.2)
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ : π.V, φ ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
    exact ⟨⟨x, hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩
  have hw0 : whit ψ (a - 1) φ₀.1.1 ≠ 0 :=
    (whit_good hψ (a - 1) h0 (hg φ₀)).2 fun h => hφ₀ (Subtype.ext (Subtype.ext h))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 hw0
  obtain ⟨b, k, hb, hyk⟩ := exists_upper_unitary (GeneralLinearGroup.map (pInf E) g₀)
  let ℓ : π.V →ₗ[ℂ] ℂ :=
    { toFun := fun φ => whit ψ (a - 1) φ.1.1 (infGL E a b)
      map_add' := fun φ φ' => congrFun (whit_add hψ (a - 1) h0 (hg φ) (hg φ')) _
      map_smul' := fun c φ => congrFun (whit_smul (a - 1) c φ.1.1) _ }
  have hℓ : ∀ φ, ℓ φ = whit ψ (a - 1) φ.1.1 (infGL E a b) := fun _ => rfl
  refine ⟨ℓ, fun h => ?_, fun τ => ?_⟩
  · apply hg₀
    rw [Pi.zero_apply]
    have e := LinearMap.congr_fun h (π.op (.cpt k) (π.op (.fin (GeneralLinearGroup.map (pFin E) g₀)) φ₀))
    rw [hℓ, LinearMap.zero_apply] at e
    refine Eq.trans ?_ e
    refine Eq.trans ?_ (whit_rt (a - 1) (fun y => φ₀.1.1 (y * finGL E a (GeneralLinearGroup.map (pFin E) g₀)))
      (infGL E a (Unitary.toUnits k)) (infGL E a b)).symm
    refine Eq.trans ?_ (whit_rt (a - 1) φ₀.1.1 (finGL E a (GeneralLinearGroup.map (pFin E) g₀)) _).symm
    rw [← map_mul, ← hyk, infGL_mul_finGL]
  · set β : Fin a → Fin a → ℂ := fun p q => coord τ (b.val p p * (b⁻¹).val q q) with hβ
    refine ⟨fun p q => if (p : ℕ) + 1 = q then
      (1 / 2 : ℂ) * (dpsi ψ (atEmb τ (β p q)) - Complex.I * dpsi ψ (atEmb τ (β p q * Complex.I))) else 0,
      fun p q hpq => ?_, fun p q hpq => ?_, fun p q hpq => ?_⟩
    · beta_reduce
      rw [if_pos hpq]
      refine mul_ne_zero (by norm_num) ?_
      have hu : IsUnit (b.val p p * (b⁻¹).val q q) :=
        (IsUnit.of_mul_eq_one _ (diag_inv b hb p)).mul (IsUnit.of_mul_eq_one_right _ (diag_inv b hb q))
      have hβ0 : β p q ≠ 0 := (hu.map (coord τ)).ne_zero
      exact wirtinger_ne_zero (fun z => ψ (sInf E (atEmb τ z)))
        (hψ.cont.comp (continuous_sInf'.comp (continuous_atEmb τ)))
        (fun z w => by simp only [atEmb_add, map_add (f := _), AddChar.map_add_eq_mul]) (fun z => hψ.norm _)
        (psi_nontriv hψ τ) (fun z => dpsi ψ (atEmb τ z))
        (fun z => by simpa only [atEmb_real_mul] using hasDerivAt_dpsi hψ (atEmb τ z)) _ hβ0
    · beta_reduce
      rw [if_neg (by omega)]
    · refine LinearMap.ext fun φ => ?_
      have hpq' : p ≠ q := ne_of_lt hpq
      have key : ∀ w : ℂ, ℓ (lieOp π (toL (Matrix.single p q (atEmb τ w))) φ) =
          dpsi ψ (sd (b.val * Matrix.single p q (atEmb τ w) * (b⁻¹).val)) * ℓ φ := fun w =>
        whit_lie_eq hψ π b _ (single_sq p q hpq' _) (conj_single_upper b hb p q hpq _) φ
      have hz : ∀ w, b.val p p * atEmb τ w * (b⁻¹).val q q = atEmb τ (β p q * w) := fun w => by
        rw [mul_right_comm, mul_embeddingScalar_eq_coord_mul]
      rw [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul]
      change ℓ ((1 / 2 : ℂ) • (lieOp π (toL (Matrix.single p q (atEmb τ 1))) φ -
        Complex.I • lieOp π (toL (Matrix.single p q (atEmb τ Complex.I))) φ)) = _
      rw [map_smul, map_sub, map_smul, key, key, sd_conj_single b hb p q hpq, sd_conj_single b hb p q hpq,
        smul_eq_mul, smul_eq_mul]
      by_cases h1 : (p : ℕ) + 1 = q
      · simp only [h1, ↓reduceIte]
        rw [hz, hz, mul_one]; ring
      · simp only [h1, ↓reduceIte]
        rw [dpsi_zero]; ring

end PositivityTheory.Rg.Cz
end
end
end
