module

public import Formalism.PeriodIntegrals.KFinSmooth
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.CoreDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.SmRight
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.Transport
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.CapelliHighestWeightConjugated
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliTransportUnitaryConj
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.HeckeMultiplication
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerivedStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.capelli_operator_on_unitary_coefficient_eq_derived : PI.UnitaryGroupMassFormula.CapelliEig.FunAct := by
  first | exact @GlobalTheory.CapelliCoef.capelli_coef | exact GlobalTheory.CapelliCoef.capelli_coef | (intros; apply GlobalTheory.CapelliCoef.capelli_coef <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorUnitaryGroupLocal

section

@[expose] public section

open Matrix Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.CapelliLocality

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma exp_inUH (H K Y : Matrix (Fin n) (Fin n) ℂ) (hKH : K * H = 1) (hHK : H * K = 1)
    (hY : Yᴴ * H = -(H * Y)) : inUH H (NormedSpace.exp Y) := by
  have h1 : Yᴴ = H * (-Y) * K := by
    calc Yᴴ = Yᴴ * H * K := by rw [Matrix.mul_assoc, hHK, Matrix.mul_one]
      _ = H * (-Y) * K := by rw [hY, Matrix.mul_neg]
  unfold inUH
  rw [← Matrix.exp_conjTranspose, h1, ioh_exp_conj H K (-Y) hKH hHK]
  have h2 : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  calc H * NormedSpace.exp (-Y) * K * H * NormedSpace.exp Y
      = H * (NormedSpace.exp (-Y) * (K * H) * NormedSpace.exp Y) := by simp only [Matrix.mul_assoc]
    _ = H := by rw [hKH, Matrix.mul_one, h2, Matrix.mul_one]

lemma inUH_mul {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hb : inUH H b) : inUH H (a * b) := by
  unfold inUH at *
  calc (a * b)ᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = H := by rw [ha, hb]

lemma rdV_congr (H K X : Matrix (Fin n) (Fin n) ℂ) (hKH : K * H = 1) (hHK : H * K = 1)
    (hX : Xᴴ * H = -(H * X)) {F₁ F₂ : Matrix (Fin n) (Fin n) ℂ → E}
    (hF : ∀ x, inUH H x → F₁ x = F₂ x) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUH H g) :
    RdV X F₁ g = RdV X F₂ g := by
  unfold RdV
  congr 1
  funext t
  refine hF _ (inUH_mul hg (exp_inUH H K _ hKH hHK ?_))
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hX, smul_neg]
  simp

lemma hpart1_mem (H Z : Matrix (Fin n) (Fin n) ℂ) (hKH : H⁻¹ * H = 1) (hHK : H * H⁻¹ = 1)
    (hH : Hᴴ = H) : (hpart1 H Z)ᴴ * H = -(H * hpart1 H Z) := by
  have hi : (H⁻¹)ᴴ = H⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hH]
  have e : H * (H⁻¹ * (Zᴴ * H)) = Zᴴ * H := by rw [← Matrix.mul_assoc, hHK, Matrix.one_mul]
  unfold hpart1
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hi, hH,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_assoc, hKH, e, Matrix.mul_one]
  rw [← smul_neg, neg_sub]
  simp

lemma hpart2_mem (H Z : Matrix (Fin n) (Fin n) ℂ) (hKH : H⁻¹ * H = 1) (hHK : H * H⁻¹ = 1)
    (hH : Hᴴ = H) : (hpart2 H Z)ᴴ * H = -(H * hpart2 H Z) := by
  have hi : (H⁻¹)ᴴ = H⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hH]
  have e : H * (H⁻¹ * (Zᴴ * H)) = Zᴴ * H := by rw [← Matrix.mul_assoc, hHK, Matrix.one_mul]
  have hs : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    simp
  unfold hpart2
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hi, hH,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, hKH, e, Matrix.mul_one]
  rw [hs, neg_smul, add_comm]

lemma foldr_congr (H : Matrix (Fin n) (Fin n) ℂ) (hKH : H⁻¹ * H = 1) (hHK : H * H⁻¹ = 1)
    (hH : Hᴴ = H) (l : List (ℂ × Fin n × Fin n)) {F₁ F₂ : Matrix (Fin n) (Fin n) ℂ → E}
    (hF : ∀ x, inUH H x → F₁ x = F₂ x) :
    ∀ x, inUH H x →
      (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₁ x =
      (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₂ x := by
  induction l with
  | nil => simpa using hF
  | cons p l ih =>
    intro x hx
    simp only [List.map_cons, List.foldr_cons]
    generalize (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₁ = G₁ at ih ⊢
    generalize (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₂ = G₂ at ih ⊢
    unfold Formalism.QuantumDeterminants.Top EabH
    rw [ih x hx, rdV_congr H H⁻¹ _ hKH hHK (hpart1_mem H _ hKH hHK hH) ih hx,
      rdV_congr H H⁻¹ _ hKH hHK (hpart2_mem H _ hKH hHK hH) ih hx]

theorem capelliH_local : PI.UnitaryGroupMassFormula.CapelliEig.Loc := by
  apply CompanionTheory.CapEig.capelli_localization <;> assumption

end GlobalTheory.CapelliLocality

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorUnitaryGroupLocalStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.capelli_operator_unitaryGroup_local : PI.UnitaryGroupMassFormula.CapelliEig.Loc := by
  first | exact @GlobalTheory.CapelliLocality.capelliH_local | exact GlobalTheory.CapelliLocality.capelliH_local | (intros; apply GlobalTheory.CapelliLocality.capelliH_local <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliTransportUnitaryConjStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.capelli_transport_unitary_conj : PI.UnitaryGroupMassFormula.CapelliEig.CapTransport := by
  first | exact @GlobalTheory.capelli_transport_conj | exact GlobalTheory.capelli_transport_conj | (intros; apply GlobalTheory.capelli_transport_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliEigenvalueKFiniteDiscreteSeriesCoeff

section

@[expose] public section

open Matrix PI.UpqRep

namespace GlobalTheory.CapelliEigenvalue

open PI.UnitaryGroupMassFormula.CapelliEig

theorem coefSm_of (hT : CapTransport) (hF : FunAct) (hD : PI.DSInfCharCap.DSInfCharCap) : CoefSm := by
  intro k r ε lam Hs _ _ _ σ Wp Wq _ _ _ _ _ _ hlam hds P Q hQ Y g hg
  obtain ⟨P₀, hcayU, hDS⟩ := hds
  obtain ⟨⟨hunit, hcay⟩, hPu⟩ := hcayU
  have hdet : IsUnit P₀.det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hleft : P₀⁻¹ * P₀ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hright : P₀ * P₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hH : Formalism.QuantumDeterminants.Hpk k r = P₀ᴴ * Formalism.REAL.Jm ε * P₀ := hcay.symm

  obtain ⟨hvec, hsm⟩ := smooth_translation k r ε Hs σ Wp Wq P₀ ⟨⟨hunit, hcay⟩, hPu⟩ P Q hQ

  have hgJ : Formalism.REAL.inUJ ε (P₀ * g * P₀⁻¹) := by
    have hg0 : gᴴ * (P₀ᴴ * Formalism.REAL.Jm ε * P₀) * g = P₀ᴴ * Formalism.REAL.Jm ε * P₀ := by
      rw [← hH]; exact hg
    show (P₀ * g * P₀⁻¹)ᴴ * Formalism.REAL.Jm ε * (P₀ * g * P₀⁻¹) = Formalism.REAL.Jm ε
    calc (P₀ * g * P₀⁻¹)ᴴ * Formalism.REAL.Jm ε * (P₀ * g * P₀⁻¹)
        = (P₀⁻¹)ᴴ * (gᴴ * (P₀ᴴ * Formalism.REAL.Jm ε * P₀) * g) * P₀⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (P₀⁻¹)ᴴ * (P₀ᴴ * Formalism.REAL.Jm ε * P₀) * P₀⁻¹ := by rw [hg0]
      _ = (P₀ * P₀⁻¹)ᴴ * Formalism.REAL.Jm ε * (P₀ * P₀⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by
          rw [hright, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hback : P₀⁻¹ * (P₀ * g * P₀⁻¹) * P₀ = g := by
    calc P₀⁻¹ * (P₀ * g * P₀⁻¹) * P₀ = (P₀⁻¹ * P₀) * g * (P₀⁻¹ * P₀) := by
          simp only [Matrix.mul_assoc]
      _ = g := by rw [hleft, Matrix.one_mul, Matrix.mul_one]

  have hu : Y + (((2 * r + k : ℕ) : ℂ)) / 2 = Y + (((2 * r + k + 1 : ℕ) : ℂ) - 1) / 2 := by
    push_cast; ring

  have htr : Formalism.QuantumDeterminants.capelliH (Formalism.QuantumDeterminants.Hpk k r) (Y + (((2 * r + k : ℕ) : ℂ)) / 2)
      (fun x => P.comp ((σ x).comp Q)) g =
      Formalism.QuantumDeterminants.capelli ε (Y + (((2 * r + k : ℕ) : ℂ)) / 2)
        (fun x => P.comp ((σ (P₀⁻¹ * x * P₀)).comp Q)) (P₀ * g * P₀⁻¹) :=
    hT (2 * r + k + 1) ε (Wq →L[ℂ] Wp) (Formalism.QuantumDeterminants.Hpk k r) P₀ P₀⁻¹
      (fun x => P.comp ((σ x).comp Q)) _ g hleft hright hH hsm hg
  show Formalism.QuantumDeterminants.capelliH (Formalism.QuantumDeterminants.Hpk k r) (Y + (((2 * r + k : ℕ) : ℂ)) / 2)
      (fun x => P.comp ((σ x).comp Q)) g = _
  rw [htr]
  ext w
  rw [hF (2 * r + k + 1) ε lam Hs (fun x => σ (P₀⁻¹ * x * P₀)) Wp Wq hDS P Q hvec _ _ hgJ w]
  simp only [hback]
  rw [hu, hD (2 * r + k + 1) ε lam Hs (fun x => σ (P₀⁻¹ * x * P₀)) hlam hDS (Q w) (hvec w) Y]
  simp only [map_smul, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]

theorem capEig_of_coefSm (hL : Loc) (hC : CoefSm) (hK : PI.KFinSmooth) : PI.CapelliEig.CapEig := by
  intro k r ε lam Hs _ _ _ σ Wp Wq _ _ _ _ _ _ hlam hds f hf Y g hg
  obtain ⟨a, ha, b, hb, P, Q, hQ, -, hfab⟩ := hf
  obtain ⟨hau, hainv, -⟩ := unitary_Hecke_group k r a ha
  obtain ⟨hbu, hbinv, -⟩ := unitary_Hecke_group k r b hb
  have hM := Hecke_multiplication k r ε lam Hs σ hds

  have hrep : ∀ x, Formalism.QuantumDeterminants.inUH (Formalism.QuantumDeterminants.Hpk k r) x →
      f x = (P.comp (σ a⁻¹)).comp ((σ x).comp ((σ b⁻¹).comp Q)) := by
    intro x hx
    have hxm : x ∈ UH (Hpk k r) := hx
    have hax : a⁻¹ * x ∈ UH (Hpk k r) := (unitary_Hecke_group k r a⁻¹ hainv).2.2 x hxm
    have hexp : a * (a⁻¹ * x * b⁻¹) * b = x := by
      calc a * (a⁻¹ * x * b⁻¹) * b = (a * a⁻¹) * x * (b⁻¹ * b) := by
            simp only [Matrix.mul_assoc]
        _ = x := by
            rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hau),
              Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hbu),
              Matrix.one_mul, Matrix.mul_one]
    have h1 : f (a * (a⁻¹ * x * b⁻¹) * b) = P.comp ((σ (a⁻¹ * x * b⁻¹)).comp Q) := hfab _
    rw [hexp, hM _ hax _ hbinv, hM _ hainv _ hxm] at h1
    rw [h1]
    ext v
    simp only [ContinuousLinearMap.comp_apply]

  have hQ' : ∀ w, ((σ b⁻¹).comp Q) w ∈ smoothVecs (k := k) (r := r) σ := fun w =>
    smooth_right_action k r ε lam Hs σ hds (Q w) (hK k r ε lam Hs σ hlam hds (Q w) (hQ w)) b⁻¹ hbinv
  obtain ⟨P₀, ⟨⟨hunit, hcay⟩, -⟩, -⟩ := id hds
  have hdet : IsUnit P₀.det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hH : Formalism.QuantumDeterminants.Hpk k r = P₀ᴴ * Formalism.REAL.Jm ε * P₀ := hcay.symm
  calc PI.CapelliEig.capC (k := k) (r := r) Y f g
      = PI.CapelliEig.capC (k := k) (r := r) Y
          (fun x => (P.comp (σ a⁻¹)).comp ((σ x).comp ((σ b⁻¹).comp Q))) g :=
        hL (2 * r + k + 1) ε (Wq →L[ℂ] Wp) (Formalism.QuantumDeterminants.Hpk k r) P₀ P₀⁻¹ f _
          (Y + (((2 * r + k : ℕ) : ℂ)) / 2) g (Matrix.nonsing_inv_mul _ hdet)
          (Matrix.mul_nonsing_inv _ hdet) hH hrep hg
    _ = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y •
          (P.comp (σ a⁻¹)).comp ((σ g).comp ((σ b⁻¹).comp Q)) :=
        hC k r ε lam Hs σ Wp Wq hlam hds (P.comp (σ a⁻¹)) ((σ b⁻¹).comp Q) hQ' Y g hg
    _ = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • f g := by rw [hrep g hg]

theorem capEig (hK : PI.KFinSmooth) (hD : PI.DSInfCharCap.DSInfCharCap) : PI.CapelliEig.CapEig := by
  have hCoef : CoefSm := coefSm_of GlobalTheory.T.capelli_transport_unitary_conj GlobalTheory.T.capelli_operator_on_unitary_coefficient_eq_derived hD
  exact capEig_of_coefSm GlobalTheory.T.capelli_operator_unitaryGroup_local hCoef hK

end GlobalTheory.CapelliEigenvalue
end
end
