module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ConjStable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DimZ1fCrystallineDeformation
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryLocusIdealLeKerOfIsBasePointStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SaturatedOrdinaryIdealCutsOutCrystallineLocusStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.UnivEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.UnramifiedLiftDeformation
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DualCr
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsTypeAndIsLocallyCrystallineRz
public import Mathlib.RingTheory.DualNumber
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DefCoc
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OnOrdinaryComponentIffContinuousCrystallineLift

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc.OrdinaryEmbeddings

open nonZeroDivisors

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ))

omit [IsAdicComplete (maximalIdeal O) O] [IsDiscreteValuationRing O] [CharZero O] in
theorem inj_OE (E : Type) [Field E] [Algebra ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E]
    [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] : Function.Injective (algebraMap O E) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_under_eq_bot (R := ℤ_[l]) ?_
  rw [Ideal.under_def, RingHom.comap_ker, ← IsScalarTower.algebraMap_eq, ← RingHom.injective_iff_ker_eq_bot,
    IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
  exact (algebraMap ℚ_[l] E).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])

omit [IsAdicComplete (maximalIdeal O) O] [CharZero O] in
theorem inj_ZO : Function.Injective (algebraMap ℤ_[l] O) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra h
  have hp : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsPrime := inferInstance
  have hm : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsMaximal := hp.isMaximal h
  have h2 : (⊥ : Ideal O).IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := ℤ_[l]) _ hm
  exact IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal h2).symm

theorem cont_push (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B]
    [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f : U.R →ₐ[O] B) (a b : Fin 3) :
    QCont l fun g => (push f U.r.hom g).mat a b :=
  (ptCont (l := l) U.R B f).1 (GQ l) (fun g => (U.r.hom g).mat a b) (U.r.cont a b)

omit [CharZero O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] in
theorem push_base (E : Type) [Field E] [Algebra O E] {x : U.R →ₐ[O] O} (hx : IsBase D.η D.Ψ U.r.hom x) :
    push ((Algebra.ofId O E).comp x) U.r.hom = D.rz E := by
  unfold Dat3.rz
  rw [← show push x U.r.hom = r0 D.η D.Ψ from hx]
  rfl


omit [CharZero O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] in
theorem IY_le_It : GlobalTheory.OrdLoc.IY D U ≤ GlobalTheory.OrdLoc.It D U :=
  Ideal.le_radical.trans (le_sInf fun _ hP => hP.1.1.2)

theorem reg (hP : LocalPublishedTheorems) {x : U.R →ₐ[O] O} (hx : IsBase D.η D.Ψ U.r.hom x) :
    ∃ y, x y ≠ 0 ∧ ∀ a ∈ GlobalTheory.OrdLoc.It D U, y * a ∈ GlobalTheory.OrdLoc.IY D U := by
  have hi := inj_ZO (l := l) (O := O)
  haveI : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hi2 : Function.Injective (algebraMap ℤ_[l] (FractionRing O)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] O (FractionRing O)]
    exact (IsFractionRing.injective O _).comp hi
  letI : Algebra ℚ_[l] (FractionRing O) := (IsFractionRing.lift hi2).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] (FractionRing O) :=
    IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hi2 x).symm
  haveI : IsLocalization (Algebra.algebraMapSubmonoid O ℤ_[l]⁰) (FractionRing O) := inferInstance
  haveI : Module.Finite ℚ_[l] (FractionRing O) := Module.Finite.of_isLocalization ℤ_[l] O ℤ_[l]⁰
  obtain ⟨-, n, P, φ, -, -, ⟨y, hy, hyP⟩, hPt, -⟩ := GlobalTheory.T.exists_unique_ordinaryPrime_dim_succ_near_base hP D U (FractionRing O) x hx
  exact ⟨y, hy, fun a ha => hyP a (hPt ▸ ha)⟩

end GlobalTheory.OrdLoc.OrdinaryEmbeddings


open GlobalTheory.OrdLoc.OrdinaryEmbeddings in
theorem GlobalTheory.OrdLoc.on_iff_inDcr : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (r : GQ l →* UpperTheory.V.U3.GG (m := 3) (R := B)), (UpperTheory.V.U3.GG.map (π : B →+* E)).comp r = D.rz E → (GlobalTheory.OrdLoc.On D U r ↔ D.InDcr (π : B →+* E) r) := by
  intro hP l _ O _ _ _ _ _ _ _ D U E _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ r hr
  obtain ⟨hPts, hCr⟩ := GlobalTheory.T.saturatedOrdinaryIdeal_cuts_out_crystalline_locus hP D U
  constructor
  · rintro ⟨f, rfl, hf⟩
    exact ⟨fun g => U.r.hasMult g, hr, cont_push D U B f, hPts B f ((IY_le_It D U).trans hf)⟩
  · intro hd
    obtain ⟨x, hx, -⟩ := univEx D U
    obtain ⟨f, hf, -⟩ := unramified_lift_deformation D U E B π hπ ((Algebra.ofId O E).comp x) r hd.mult
      (hd.red.trans (push_base D U E hx).symm) hd.cont
    have hfY : GlobalTheory.OrdLoc.IY D U ≤ RingHom.ker f := hCr E B π hπ f (hf ▸ hd)
    have hfx : ∀ a, π (f a) = algebraMap O E (x a) := by
      intro a
      obtain ⟨g, -, hu⟩ := unramified_lift_deformation D U E E (AlgHom.id E E) (fun a ha => by simpa using ha)
        ((π.restrictScalars O).comp f) (push ((π.restrictScalars O).comp f) U.r.hom)
        (fun g => U.r.hasMult g) rfl (cont_push D U E _)
      have h1 : push ((π.restrictScalars O).comp f) U.r.hom = D.rz E := by
        rw [← hd.red, ← hf]; rfl
      have h := (hu ((π.restrictScalars O).comp f) rfl).trans
        (hu ((Algebra.ofId O E).comp x) ((push_base D U E hx).trans h1.symm)).symm
      exact congrArg (fun φ : U.R →ₐ[O] E => φ a) h
    obtain ⟨y, hy, hya⟩ := reg D U hP hx
    refine ⟨f, hf, fun a ha => ?_⟩
    have hne : algebraMap O E (x y) ≠ 0 := (map_ne_zero_iff _ (inj_OE (l := l) E)).2 hy
    have hnil : IsNilpotent (f y - algebraMap E B (algebraMap O E (x y))) := hπ _ (by
      rw [map_sub, hfx, AlgHom.commutes]
      exact sub_self _)
    have hu : IsUnit (f y) := by
      have := hnil.isUnit_add_right_of_commute (hne.isUnit.map (algebraMap E B)) (Commute.all _ _)
      simpa using this
    have h0 : f y * f a = 0 := by
      rw [← map_mul]
      exact hfY (hya a ha)
    exact (hu.mul_right_eq_zero).1 h0
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OnOrdinaryComponentIffContinuousCrystallineLiftStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.onOrdinaryComponent_iff_continuous_crystalline_lift : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (r : GQ l →* UpperTheory.V.U3.GG (m := 3) (R := B)), (UpperTheory.V.U3.GG.map (π : B →+* E)).comp r = D.rz E → (D.On U r ↔ D.InDcr (π : B →+* E) r) := by
  first | exact @GlobalTheory.OrdLoc.on_iff_inDcr | exact GlobalTheory.OrdLoc.on_iff_inDcr | (intros; apply GlobalTheory.OrdLoc.on_iff_inDcr <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.QcontDual

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc.TangentDual

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ))

omit [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] in
theorem push_base (E : Type) [Field E] [Algebra O E] {x : U.R →ₐ[O] O} (hx : IsBase D.η D.Ψ U.r.hom x) :
    push ((Algebra.ofId O E).comp x) U.r.hom = D.rz E := by
  unfold Dat3.rz
  rw [← show push x U.r.hom = r0 D.η D.Ψ from hx]
  rfl

theorem cont_push (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B]
    [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f : U.R →ₐ[O] B) (a b : Fin 3) :
    QCont l fun g => (push f U.r.hom g).mat a b :=
  (ptCont (l := l) U.R B f).1 (GQ l) (fun g => (U.r.hom g).mat a b) (U.r.cont a b)

omit [IsDomain O] in
theorem qcont_dual {X E : Type} [TopologicalSpace X] [Field E] [Algebra ℚ_[l] E]
    [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] (f : X → DualNumber E) (h1 : Continuous fun x => (f x).fst)
    (h2 : Continuous fun x => (f x).snd) : QCont l f := by
  have e : f = fun x => ((TrivSqZeroExt.inlAlgHom ℚ_[l] E E).toLinearMap (f x).fst) +
      (((TrivSqZeroExt.inrHom E E).restrictScalars ℚ_[l]) (f x).snd) :=
    funext fun x => (TrivSqZeroExt.inl_fst_add_inr_snd_eq _).symm
  unfold QCont
  letI : TopologicalSpace (DualNumber E) := moduleTopology ℚ_[l] _
  haveI : IsModuleTopology ℚ_[l] (DualNumber E) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd ℚ_[l] (DualNumber E)
  rw [e]
  exact ((IsModuleTopology.continuous_of_linearMap _).comp h1).add
    ((IsModuleTopology.continuous_of_linearMap _).comp h2)

end GlobalTheory.OrdLoc.TangentDual


open GlobalTheory.OrdLoc.TangentDual in
theorem GlobalTheory.OrdLoc.rtTangent :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E], ∀ γ ∈ Z1 (adRep (D.rz E)), ∀ r' : GQ l →* GG (m := 3) (R := DualNumber E), DualDef (D.rz E) γ r' → (D.On U r' ↔ γ ∈ finiteCocycles (MonoidHom.id _) (adRep (D.rz E))) := by
  intro hP l _ O _ _ _ _ _ _ _ D U E _ _ _ _ _ _ _ _ _ _ γ hγ r' hr'
  obtain ⟨x, hx, -⟩ := univEx D U
  have hc : Continuous fun g => (D.rz E g).mat := by
    refine continuous_matrix fun a b => ?_
    have h := cont_push D U E ((Algebra.ofId O E).comp x) a b
    rw [push_base D U E hx] at h
    unfold QCont at h
    rwa [← eq_moduleTopology ℚ_[l] E] at h
  have hm : HasMult D.η (D.rz E) := fun g => rfl
  have hdc := dualCr D E (D.rz E) hm hc γ hγ r' hr'
  haveI : Module.Finite E (DualNumber E) := inferInstanceAs (Module.Finite E (E × E))
  haveI : Module.Finite ℚ_[l] (DualNumber E) := inferInstanceAs (Module.Finite ℚ_[l] (E × E))
  have hred : (GG.map (TrivSqZeroExt.fstHom E E E : DualNumber E →+* E)).comp r' = D.rz E := by
    refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext (Matrix.ext fun a b => ?_)) (hr' g).1
    exact congrArg TrivSqZeroExt.fst ((hr' g).2 a b)
  rw [GlobalTheory.T.onOrdinaryComponent_iff_continuous_crystalline_lift hP D U E (DualNumber E) (TrivSqZeroExt.fstHom E E E)
    (fun a ha => TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst.2 (by rw [show a.fst = 0 from ha]; exact IsNilpotent.zero))
    r' hred]
  refine ⟨fun h => (hdc.1 h.cr).2, fun h => ⟨fun g => (hr' g).1, hred, fun a b => ?_, hdc.2 ⟨(isType_and_isLocallyCrystalline_rz D E).2, h⟩⟩⟩
  refine qcont_dual _ ?_ ?_
  · simp only [(hr' _).2]
    exact hc.matrix_elem a b
  · simp only [(hr' _).2]
    exact (hγ.1.matrix_mul hc).matrix_elem a b
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RtTangent

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

theorem UpperTheory.V.Loc.rtTangent :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E], ∀ γ ∈ Z1 (adRep (D.rz E)), ∀ r' : GQ l →* GG (m := 3) (R := DualNumber E), DualDef (D.rz E) γ r' → (D.On U r' ↔ γ ∈ finiteCocycles (MonoidHom.id _) (adRep (D.rz E))) :=
  fun hP => @GlobalTheory.OrdLoc.rtTangent hP
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ChartCount

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

private noncomputable def jet {σ E : Type} [Field E] (i : σ) : MvPowerSeries σ E →ₐ[E] DualNumber E where
  toFun f := ⟨MvPowerSeries.constantCoeff f, MvPowerSeries.coeff (Finsupp.single i 1) f⟩
  map_one' := by
    classical
    ext
    · simp
    · simp [MvPowerSeries.coeff_one]
  map_mul' f g := by
    classical
    refine TrivSqZeroExt.ext (map_mul MvPowerSeries.constantCoeff f g) ?_
    refine Eq.trans ?_ (DualNumber.snd_mul _ _).symm
    show MvPowerSeries.coeff (Finsupp.single i 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single i 1) g +
        MvPowerSeries.coeff (Finsupp.single i 1) f * MvPowerSeries.constantCoeff g
    simp [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.Nat.antidiagonal_succ, mul_comm]
  map_zero' := by ext <;> simp
  map_add' f g := TrivSqZeroExt.ext (map_add MvPowerSeries.constantCoeff f g) (map_add (MvPowerSeries.coeff _) f g)
  commutes' c := by
    classical
    ext <;> simp [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C, TrivSqZeroExt.algebraMap_eq_inl]

private theorem snd_mul_left {E : Type} [CommRing E] (A : Matrix (Fin 3) (Fin 3) E)
    (X : Matrix (Fin 3) (Fin 3) (DualNumber E)) :
    (A.map (algebraMap E (DualNumber E)) * X).map TrivSqZeroExt.snd = A * X.map TrivSqZeroExt.snd := by
  ext a b
  simp [Matrix.mul_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_sum]

private theorem snd_mul_right {E : Type} [CommRing E] (A : Matrix (Fin 3) (Fin 3) E)
    (X : Matrix (Fin 3) (Fin 3) (DualNumber E)) :
    (X * A.map (algebraMap E (DualNumber E))).map TrivSqZeroExt.snd = X.map TrivSqZeroExt.snd * A := by
  ext a b
  simp [Matrix.mul_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_sum, mul_comm]

private theorem exists_coc {G E : Type} [Group G] [CommRing E]
    (r : G →* GG (m := 3) (R := E)) (r' : G →* GG (m := 3) (R := DualNumber E))
    (h1 : ∀ g, (r' g).right = (r g).right) (h2 : ∀ g a b, ((r' g).mat a b).fst = (r g).mat a b) :
    ∃ γ, IsCoc r γ ∧ DualDef r γ r' := by
  obtain ⟨γ, -, hc, hd⟩ := exists_isCoc (RingHom.ker (TrivSqZeroExt.fstHom E E E))
    ((GG.map (algebraMap E (DualNumber E))).comp r) r' (by
      rw [eq_bot_iff, Ideal.mul_le]
      intro x hx y hy
      have hx' : x.fst = 0 := hx
      have hy' : y.fst = 0 := hy
      rw [Ideal.mem_bot]
      ext <;> simp [hx', hy']) (MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext (Matrix.ext fun a b => by
      refine Ideal.Quotient.eq.2 ?_
      show ((r' g).mat a b - algebraMap E (DualNumber E) ((r g).mat a b)).fst = 0
      simp [h2, TrivSqZeroExt.algebraMap_eq_inl])) (h1 g))
  refine ⟨fun g => (γ g).map TrivSqZeroExt.snd, fun g h => ?_, fun g => ⟨h1 g, fun a b => ?_⟩⟩
  · have e : adRep ((GG.map (algebraMap E (DualNumber E))).comp r) g (γ h) =
        (r g).mat.map (algebraMap E (DualNumber E)) * (if (r g).right = 1 then γ h else thetaLie (γ h)) *
          (((r g).left⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).map (algebraMap E (DualNumber E)) := rfl
    have e' : ∀ X, adRep r g X = (r g).mat * (if (r g).right = 1 then X else thetaLie X) *
          (((r g).left⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) := fun X => rfl
    show (γ (g * h)).map _ = _
    rw [hc g h, Matrix.map_add _ TrivSqZeroExt.snd_add, e, e', snd_mul_right, snd_mul_left]
    split_ifs
    · rfl
    · unfold thetaLie
      rw [Matrix.map_neg _ TrivSqZeroExt.snd_neg, ← Jmat_map (algebraMap E (DualNumber E)), snd_mul_right, snd_mul_left]
      rfl
  · refine TrivSqZeroExt.ext (h2 g a b) ?_
    have e : (r' g).mat = (1 + γ g) * (r g).mat.map (algebraMap E (DualNumber E)) := (hd g).2
    have e2 := congrArg (fun X : Matrix (Fin 3) (Fin 3) (DualNumber E) => X.map TrivSqZeroExt.snd a b) e
    simp only [snd_mul_right] at e2
    refine e2.trans ?_
    show _ = ((γ g).map TrivSqZeroExt.snd * (r g).mat) a b
    refine congrArg (fun X : Matrix (Fin 3) (Fin 3) E => (X * (r g).mat) a b) ?_
    ext c d
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem UpperTheory.V.Loc.chartCount :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (x : U.R →ₐ[O] O), IsBase D.η D.Ψ U.r.hom x → ∀ (n : ℕ) (w : Fin n → ℤ) (φ : U.R →ₐ[O] MvPowerSeries (Fin n) E) (u : Fin n → GQ l × Fin 3 × Fin 3), UpperTheory.V.Loc.IsCompl (D.It U) x φ → (∀ g a b, φ ((U.r.hom g).mat a b) ∈ wtPart E w (wt a b)) → (∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (φ ((U.r.hom (u i).1).mat (u i).2.1 (u i).2.2)) = if i = j then 1 else 0) → ∀ j, Nat.card {i // w i = j} ≤ locDims j := by
  intro hP l _ O _ _ _ _ _ _ _ D U E _ _ _ _ _ _ _ _ x hx n w φ u hφ hg hu j
  letI : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E
  have hxe : ∀ g a b, algebraMap O E (x ((U.r.hom g).mat a b)) = (D.rz E g).mat a b := fun g a b =>
    congrArg (fun r : GQ l →* GG (m := 3) (R := O) => algebraMap O E ((r g).mat a b)) hx
  let d : GQ l → Fin 3 → E := fun g b => algebraMap O E ((D.Ψ g ^ wt1 b : Oˣ) : O)
  have hd : ∀ g, (D.rz E g).mat = Matrix.diagonal (d g) := fun g =>
    Matrix.diagonal_map (map_zero (algebraMap O E))
  have hdd : ∀ g b, d g b * d g⁻¹ b = 1 := fun g b => by
    simp only [d]
    rw [← map_mul, ← Units.val_mul, ← mul_zpow, ← map_mul]
    simp
  have hdc : ∀ b, Continuous fun g => d g b := fun b => by
    have := (ptCont (l := l) U.R E ((Algebra.ofId O E).comp x)).1 _ _ (U.r.cont b b)
    refine Continuous.congr this fun g => (hxe g b b).trans ?_
    rw [hd, Matrix.diagonal_apply_eq]
  have key : ∀ i, ∃ γ ∈ finiteCocycles (MonoidHom.id _) (adRep (D.rz E)), ∀ g a b,
      γ g a b = MvPowerSeries.coeff (Finsupp.single i 1) (φ ((U.r.hom g).mat a b)) * d g⁻¹ b := fun i => by
    let F : U.R →ₐ[O] DualNumber E := ((jet i).restrictScalars O).comp φ
    obtain ⟨γ, hc, hγ⟩ := exists_coc (D.rz E) (push F U.r.hom) (fun g => U.r.hasMult g)
      (fun g a b => (hφ.const _).trans (hxe g a b))
    have he : ∀ g a b, γ g a b = (F ((U.r.hom g).mat a b)).snd * d g⁻¹ b := fun g a b => by
      have : (F ((U.r.hom g).mat a b)).snd = (γ g * (D.rz E g).mat) a b :=
        congrArg TrivSqZeroExt.snd ((hγ g).2 a b)
      rw [this, hd, Matrix.mul_diagonal, mul_assoc, hdd, mul_one]
    refine ⟨γ, (rtTangent hP D U E γ ⟨?_, hc⟩ _ hγ).1 ⟨F, rfl, fun y hy => ?_⟩, he⟩
    · refine continuous_pi fun a => continuous_pi fun b => ?_
      simp only [he]
      refine Continuous.mul ?_ ((hdc b).comp continuous_inv)
      haveI : Module.Finite ℚ_[l] (DualNumber E) := inferInstanceAs (Module.Finite ℚ_[l] (E × E))
      have hq := (ptCont (l := l) U.R (DualNumber E) F).1 _ _ (U.r.cont a b)
      letI : TopologicalSpace (DualNumber E) := moduleTopology ℚ_[l] _
      haveI : IsModuleTopology ℚ_[l] (DualNumber E) := ⟨rfl⟩
      exact (IsModuleTopology.continuous_of_linearMap
        ((TrivSqZeroExt.sndHom E E).restrictScalars ℚ_[l])).comp hq
    · rw [← hφ.ker, RingHom.mem_ker] at hy
      show jet i (φ y) = 0
      rw [hy, map_zero]
  choose γ hγ he using key
  obtain ⟨hfin, hdim, -⟩ := dim_Z1f_crystalline_deformation hP D E j
  haveI : Module.Finite E ↥(finiteCocycles (MonoidHom.id _) (adRep (D.rz E)) ⊓ Submodule.pi Set.univ fun _ => gw E j) :=
    Module.Finite.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)
  let v : {i // w i = j} → ↥(finiteCocycles (MonoidHom.id _) (adRep (D.rz E)) ⊓ Submodule.pi Set.univ fun _ => gw E j) :=
    fun i => ⟨γ i, hγ i, fun g _ a b hab => by
      rw [he, hg g a b _ (by
        rw [Finsupp.weight_single, one_smul, i.2]
        exact hab.symm), zero_mul]⟩
  have hv : LinearIndependent E v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h1 := congrArg (fun y : ↥(finiteCocycles (MonoidHom.id _) (adRep (D.rz E)) ⊓ Submodule.pi Set.univ fun _ => gw E j) =>
      y.1 (u k).1 (u k).2.1 (u k).2.2 * d (u k).1 (u k).2.2) hc
    simp only [v, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply,
      Matrix.smul_apply, he, hu, smul_eq_mul, Subtype.val_inj] at h1
    simpa [mul_assoc, mul_comm (d (u k).1⁻¹ _), hdd] using h1
  rw [← hdim, Nat.card_eq_fintype_card]
  exact hv.fintype_card_le_finrank
end
end
