module

public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Etale.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot
public import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSectionLiftOfEtaleOfHenselian

section

@[expose] public section

noncomputable section
open IsLocalRing UpperTheory.Et

theorem UpperTheory.exists_section_lift_of_etale_of_henselian :
    ∀ (A E : Type) [CommRing A] [HenselianLocalRing A] [CommRing E] [Algebra A E] [Algebra.Etale A E] (π : E →ₐ[A] ResidueField A), ∃ σ : E →ₐ[A] A, ∀ x, residue A (σ x) = π x := by
  intro A E _ _ _ _ _ π
  classical
  let Q : Ideal E := RingHom.ker π
  haveI : Q.IsPrime := RingHom.ker_isPrime π
  obtain ⟨f, hfQ, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) Q
  obtain ⟨P⟩ := hstd.nonempty_standardEtalePresentation
  have hunit : ∀ y : Submonoid.powers f, IsUnit (π y) := by
    rintro ⟨_, n, rfl⟩
    simp only [map_pow]
    exact (isUnit_iff_ne_zero.mpr fun h => hfQ (RingHom.mem_ker.mpr h)).pow n
  let πf : Localization.Away f →ₐ[A] ResidueField A := IsLocalization.liftAlgHom (M := Submonoid.powers f) hunit
  let ι : E →ₐ[A] Localization.Away f := IsScalarTower.toAlgHom A E _
  have hπ : ∀ x, πf (ι x) = π x := fun x => by
    simp [πf, ι]
  let τ : P.Ring →ₐ[A] ResidueField A := πf.comp P.equivRing.symm.toAlgHom
  have hx : P.HasMap (τ P.X) := StandardEtalePair.hasMap_X.map τ
  have key : ∀ b : A, residue A b = τ P.X → ∀ p : Polynomial A, residue A (p.eval b) = Polynomial.aeval (τ P.X) p := by
    intro b hb p
    rw [← hb, ← ResidueField.algebraMap_eq, Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval]
  obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective (τ P.X)
  have h1 : P.f.eval a₀ ∈ maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, key a₀ ha₀]
    exact hx.1
  have h2 : IsUnit (P.f.derivative.eval a₀) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, key a₀ ha₀]
    exact hx.isUnit_derivative_f.ne_zero
  obtain ⟨a, ha, ham⟩ := HenselianLocalRing.is_henselian P.f P.monic_f a₀ h1 h2
  have hra : residue A a = τ P.X := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at ham
    rw [ham, ha₀]
  have hA : P.HasMap a := by
    refine ⟨by rw [Polynomial.coe_aeval_eq_eval]; exact ha, ?_⟩
    rw [Polynomial.coe_aeval_eq_eval, ← IsLocalRing.residue_ne_zero_iff_isUnit, key a hra]
    exact hx.2.ne_zero
  let ρ : A →ₐ[A] ResidueField A := IsScalarTower.toAlgHom A A (ResidueField A)
  have hρ : ρ.comp (P.lift a hA) = τ := by
    apply StandardEtalePair.hom_ext
    simp [ρ, hra, ResidueField.algebraMap_eq]
  refine ⟨(P.lift a hA).comp (P.equivRing.toAlgHom.comp ι), fun x => ?_⟩
  have := congrArg (fun φ => φ (P.equivRing (ι x))) hρ
  simp only [AlgHom.comp_apply, ρ, IsScalarTower.coe_toAlgHom', ResidueField.algebraMap_eq, τ, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe, AlgEquiv.symm_apply_apply] at this
  simpa [hπ] using this

end
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsCommonZeroOfJacobianIsUnitHenselian

section

@[expose] public section

noncomputable section
open IsLocalRing UpperTheory.Et

private theorem etale_away_jacobian (A : Type) [CommRing A] (n : ℕ)
    (F : Fin n → MvPolynomial (Fin n) A) :
    Algebra.Etale A (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F))
      (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det)) := by
  classical
  let I := Ideal.span (Set.range F)
  let d := Ideal.Quotient.mk I (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det
  let P1 := Algebra.PreSubmersivePresentation.naive (v := F) (id : Fin n → Fin n)
    Function.injective_id
  let P2 := Algebra.PreSubmersivePresentation.localizationAway (Localization.Away d) d
  have hJ : P1.jacobian = d := by
    rw [P1.jacobian_eq_jacobiMatrix_det]
    have hM : P1.jacobiMatrix = Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t) := by
      ext i j
      simp [P1]
    rw [hM, Algebra.Generators.algebraMap_apply]
    have hE : MvPolynomial.aeval P1.val = Ideal.Quotient.mkₐ A I :=
      MvPolynomial.algHom_ext fun i => by simp [P1, I, Algebra.Generators.naive]
    exact congrFun (congrArg DFunLike.coe hE) _
  let P : Algebra.SubmersivePresentation A (Localization.Away d) (Unit ⊕ Fin n) (Unit ⊕ Fin n) :=
    { P2.comp P1 with
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.smul_def, Algebra.PreSubmersivePresentation.localizationAway_jacobian, hJ]
        exact (IsLocalization.Away.algebraMap_isUnit d).mul
          (IsLocalization.Away.algebraMap_isUnit d) }
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 A (Localization.Away d) :=
    P.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])
  infer_instance

theorem UpperTheory.exists_common_zero_of_jacobian_isUnit_henselian :
    ∀ (A : Type) [CommRing A] [HenselianLocalRing A] (n : ℕ) (F : Fin n → MvPolynomial (Fin n) A),
      (∀ i, MvPolynomial.eval 0 (F i) ∈ maximalIdeal A) → IsUnit (Matrix.det (Matrix.of fun i j => MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i)))) →
      ∃ x : Fin n → A, (∀ i, MvPolynomial.eval x (F i) = 0) ∧ ∀ j, x j ∈ maximalIdeal A := by
  intro A _ _ n F hF hU
  classical
  let I := Ideal.span (Set.range F)
  let d := Ideal.Quotient.mk I (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det
  haveI := etale_away_jacobian A n F
  let ψ : MvPolynomial (Fin n) A →ₐ[A] ResidueField A :=
    (Algebra.ofId A (ResidueField A)).comp (MvPolynomial.aeval (0 : Fin n → A))
  have hψ : ∀ p, ψ p = residue A (MvPolynomial.eval 0 p) := fun p => by
    simp [ψ, MvPolynomial.coe_aeval_eq_eval, IsLocalRing.ResidueField.algebraMap_eq]
  have hI : ∀ a ∈ I, ψ a = 0 := by
    intro a ha
    have hle : I ≤ RingHom.ker ψ := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, hψ, residue_eq_zero_iff]
      exact hF i
    exact hle ha
  let π0 : (MvPolynomial (Fin n) A ⧸ I) →ₐ[A] ResidueField A := Ideal.Quotient.liftₐ I ψ hI
  have hπ0 : ∀ p, π0 (Ideal.Quotient.mk I p) = residue A (MvPolynomial.eval 0 p) := fun p => by
    rw [← hψ]
    rfl
  have hd : IsUnit (π0 d) := by
    rw [hπ0]
    have hdet : MvPolynomial.eval 0 (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det =
        (Matrix.of fun i j => MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i))).det := by
      rw [RingHom.map_det, ← Matrix.det_transpose]
      congr 1
    rw [hdet]
    exact hU.map (residue A)
  let π : Localization.Away d →ₐ[A] ResidueField A :=
    IsLocalization.liftAlgHom (M := Submonoid.powers d) (f := π0) (by
      rintro ⟨y, k, rfl⟩
      simpa using hd.pow k)
  obtain ⟨σ, hσ⟩ := UpperTheory.exists_section_lift_of_etale_of_henselian A (Localization.Away d) π
  let φ : MvPolynomial (Fin n) A →ₐ[A] A :=
    (σ.comp (IsScalarTower.toAlgHom A _ (Localization.Away d))).comp (Ideal.Quotient.mkₐ A I)
  have hφ : ∀ p, φ p = MvPolynomial.eval (fun j => φ (MvPolynomial.X j)) p := by
    intro p
    rw [← MvPolynomial.coe_aeval_eq_eval]
    exact congrFun (congrArg DFunLike.coe
      (MvPolynomial.algHom_ext (fun j => by simp) : φ = MvPolynomial.aeval _)) p
  refine ⟨fun j => φ (MvPolynomial.X j), fun i => ?_, fun j => ?_⟩
  · rw [← hφ]
    have h0 : Ideal.Quotient.mk I (F i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
    simp [φ, h0]
  · rw [← residue_eq_zero_iff]
    show residue A (σ (algebraMap _ (Localization.Away d)
      (Ideal.Quotient.mk I (MvPolynomial.X j)))) = 0
    rw [hσ]
    simp [π, hπ0]

end
end
end
