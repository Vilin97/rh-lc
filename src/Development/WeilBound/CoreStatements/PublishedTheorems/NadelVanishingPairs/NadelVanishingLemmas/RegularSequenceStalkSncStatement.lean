module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FinrankKaehlerAffineChartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineOpenFinitePresentationStalkKaehlerFr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinimalLocalGenerators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSqLocalizationOfPderivMem
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKaehlerResidueField

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LogPair
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.SmoothStalk

theorem finrank_baseChange_kaehler_of_formallyEtale {k B A K : Type} [Field k] [CommRing B] [CommRing A] [Field K]
    [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A] [Algebra A K] [Algebra B K]
    [IsScalarTower B A K] [Algebra.FormallyEtale B A] [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]] [Nontrivial A] :
    Module.finrank K (K ⊗[B] Ω[B⁄k]) = Module.finrank A Ω[A⁄k] := by
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale k B A
  have hbc2 := TensorProduct.isBaseChange A Ω[A⁄k] K
  have hcomp := hbc.comp hbc2
  rw [hcomp.equiv.finrank_eq, Module.finrank_baseChange]

theorem finrank_residue_kaehler : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d f] (U : X.Opens) (x : X) (hxU : x ∈ U), IsAffineOpen U → letI : Algebra k Γ(X, U) := (cstOn f U).toAlgebra; letI : Algebra Γ(X, U) (IsLocalRing.ResidueField (X.presheaf.stalk x)) := ((IsLocalRing.residue (X.presheaf.stalk x)).comp (X.presheaf.germ U x hxU).hom).toAlgebra; Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x)) (IsLocalRing.ResidueField (X.presheaf.stalk x) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄k]) = d := by
  intro k _ X f d _ U x hxU hU
  letI iB : Algebra k Γ(X, U) := (cstOn f U).toAlgebra
  letI iBK : Algebra Γ(X, U) (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    ((IsLocalRing.residue (X.presheaf.stalk x)).comp (X.presheaf.germ U x hxU).hom).toAlgebra
  letI iBA : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  letI iA : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra
  obtain ⟨-, hfree, hfin, hrank⟩ := GlobalTheory.SmoothStalk.smooth_stalk k X f d ⟨U, hU⟩ x hxU
  haveI : Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] := hfree
  haveI : Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] := hfin
  have hrank' : Module.finrank (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] = d := hrank
  haveI : IsScalarTower k Γ(X, U) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' rfl
  haveI hsc : @IsScalarTower Γ(X, U) (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x)) _ _
      iBK.toSMul := IsScalarTower.of_algebraMap_eq' rfl
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  haveI : Algebra.FormallyEtale Γ(X, U) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  rw [← hrank']
  exact @finrank_baseChange_kaehler_of_formallyEtale k Γ(X, U) (X.presheaf.stalk x)
    (IsLocalRing.ResidueField (X.presheaf.stalk x)) _ _ _ _ iB iA iBA _ _ iBK hsc _ _ _ _

end GlobalTheory.SmoothStalk
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FinrankKaehlerResidueField

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.finrank_kaehler_residue_field : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d f] (U : X.Opens) (x : X) (hxU : x ∈ U), IsAffineOpen U → letI : Algebra k Γ(X, U) := (cstOn f U).toAlgebra; letI : Algebra Γ(X, U) (IsLocalRing.ResidueField (X.presheaf.stalk x)) := ((IsLocalRing.residue (X.presheaf.stalk x)).comp (X.presheaf.germ U x hxU).hom).toAlgebra; Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x)) (IsLocalRing.ResidueField (X.presheaf.stalk x) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄k]) = d := by
  first | exact @_root_.GlobalTheory.SmoothStalk.finrank_residue_kaehler | exact _root_.GlobalTheory.SmoothStalk.finrank_residue_kaehler | (intros; apply _root_.GlobalTheory.SmoothStalk.finrank_residue_kaehler <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularLocalDifferentialsBasis

section

@[expose] public section

open scoped TensorProduct Polynomial
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem linearIndependent_tmul_D_of_regular_system :
    ∀ (k A : Type) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A] [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)] (n : ℕ) (t : Fin n → A), Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A → (n : WithBot ℕ∞) = ringKrullDim A → LinearIndependent (IsLocalRing.ResidueField A) (fun a => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t a)) := by
  intro k A _ _ _ _ _ _ n t hspan hdim
  classical
  have htm : ∀ i, t i ∈ maximalIdeal A := fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  have hn : n = (maximalIdeal A).spanFinrank := by
    apply le_antisymm
    · have h := ringKrullDim_le_spanFinrank_maximalIdeal A
      rw [← hdim] at h
      exact_mod_cast h
    · rw [← hspan]
      refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range t)).trans ?_
      rw [← Set.image_univ]
      refine (Set.ncard_image_le Set.finite_univ).trans ?_
      simp
  have hker : RingHom.ker (algebraMap A (ResidueField A)) = maximalIdeal A := ker_residue
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  choose b hb using fun j => residue_surjective (R := A) (g j)
  have hx : ∑ j, b j * t j ∈ RingHom.ker (algebraMap A (ResidueField A)) := by
    rw [hker]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (htm j)
  have htk : ∀ j, algebraMap A (ResidueField A) (t j) = 0 := fun j => by
    rw [← RingHom.mem_ker, hker]; exact htm j
  have h0 : KaehlerDifferential.kerCotangentToTensor k A (ResidueField A)
      ((RingHom.ker (algebraMap A (ResidueField A))).toCotangent ⟨_, hx⟩) = 0 := by

    rw [KaehlerDifferential.kerCotangentToTensor_toCotangent, map_sum, tmul_sum, ← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Derivation.leibniz, tmul_add, ← smul_tmul, ← smul_tmul, Algebra.smul_def, mul_one,
      Algebra.smul_def, mul_one, htk, zero_tmul, add_zero, smul_tmul', smul_eq_mul, mul_one]
    rw [← hb j]; rfl
  have hinj := kerCotangentToTensor_injective_of_formallySmooth k A (ResidueField A)
    residue_surjective
  have h2 : ∑ j, b j * t j ∈ RingHom.ker (algebraMap A (ResidueField A)) ^ 2 :=
    (Ideal.toCotangent_eq_zero _ _).mp (hinj (h0.trans (map_zero _).symm))
  rw [hker] at h2
  have := coeffs_mem_maximalIdeal_of_sum_mem_sq t hspan hn b h2 i
  rw [← hb i]
  exact (residue_eq_zero_iff _).2 this

end GlobalTheory
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RegularLocalDifferentialsLinearIndependent

section

@[expose] public section

open scoped TensorProduct Polynomial
theorem _root_.GlobalTheory.T.regular_local_differentials_linearIndependent : ∀ (k A : Type) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A] [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)] (n : ℕ) (t : Fin n → A), Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A → (n : WithBot ℕ∞) = ringKrullDim A → LinearIndependent (IsLocalRing.ResidueField A) (fun a => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t a)) := by
  first | exact @_root_.GlobalTheory.linearIndependent_tmul_D_of_regular_system | exact _root_.GlobalTheory.linearIndependent_tmul_D_of_regular_system | (intros; apply _root_.GlobalTheory.linearIndependent_tmul_D_of_regular_system <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ResidueFieldFormallySmooth

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.residue_field_formally_smooth :
    ∀ (k : Type) [Field k] [PerfectField k] (X : Scheme.{0}) (f : X ⟶ Sp k)
      [LocallyOfFiniteType f] (U : X.Opens) (x : X) (hxU : x ∈ U),
      IsClosed ({x} : Set X) →
        (letI : Algebra k (X.presheaf.stalk x) :=
          ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra
         Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x))) := by
  intro k _ _ X f _ U x hxU _
  let : Algebra k (X.presheaf.stalk x) :=
    ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra
  have hgerm : f.appLE ⊤ U le_top ≫ X.presheaf.germ U x hxU =
      (Sp k).presheaf.germ ⊤ (f x) trivial ≫ f.stalkMap x := by
    rw [Scheme.Hom.germ_stalkMap f ⊤ x trivial]
    simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  have hstalk : algebraMap k (X.presheaf.stalk x) =
      (f.stalkMap x).hom.comp (StructureSheaf.toStalk k (f x)).hom := by
    change (X.presheaf.germ U x hxU).hom.comp (cstOn f U) = _
    rw [cstOn, ← CommRingCat.hom_comp, Category.assoc, hgerm, ← Category.assoc,
      Scheme.ΓSpecIso_inv]
    rfl
  have hbase (p : PrimeSpectrum k) : (StructureSheaf.toStalk k p).hom.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.mpr (Algebra.EssFiniteType.of_isLocalization _ p.asIdeal.primeCompl)
  have hresidue : (IsLocalRing.residue (X.presheaf.stalk x)).FiniteType :=
    RingHom.FiniteType.of_surjective _ IsLocalRing.residue_surjective
  have : Algebra.EssFiniteType k (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by
    apply RingHom.essFiniteType_algebraMap.mp
    change ((IsLocalRing.residue (X.presheaf.stalk x)).comp
      (algebraMap k (X.presheaf.stalk x))).EssFiniteType
    rw [hstalk]
    exact ((hbase (f x)).comp (LocallyOfFiniteType.stalkMap f x)).comp hresidue.essFiniteType
  exact Algebra.FormallySmooth.of_perfectField
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RegularSequenceStalkSnc

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.RegParams

theorem exists_closed_specialization : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) [LocallyOfFiniteType f] (x : X), ∃ y : X, IsClosed ({y} : Set X) ∧ ∀ U : X.Opens, y ∈ U → x ∈ U := by
  intro k _ X f _ x
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Set.singleton_nonempty x).closure isClosed_closure.isLocallyClosed
  exact ⟨y, hyc, fun U hU => (specializes_iff_mem_closure.2 hy).mem_open U.isOpen hU⟩

theorem linearIndependent_fibre_of_stalk : ∀ (k B A K : Type) [CommRing k] [CommRing B] [CommRing A] [Field K] [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A] [Algebra A K] [Algebra B K] [IsScalarTower B A K] (ι : Type) (b : ι → B), LinearIndependent K (fun i => (1 : K) ⊗ₜ[A] KaehlerDifferential.D k A (algebraMap B A (b i))) → LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D k B (b i)) := by
  intro k B A K _ _ _ _ _ _ _ _ _ _ _ ι b h
  let g : Ω[B⁄k] →ₗ[B] K ⊗[A] Ω[A⁄k] :=
    ((TensorProduct.mk A K Ω[A⁄k] 1).restrictScalars B).comp (KaehlerDifferential.map k k B A)
  let φ : K ⊗[B] Ω[B⁄k] →ₗ[K] K ⊗[A] Ω[A⁄k] := g.liftBaseChange K
  refine LinearIndependent.of_comp φ ?_
  convert h using 1
  funext i
  simp [φ, g, KaehlerDifferential.map_D]

theorem linearIndependent_fibre_of_associated : ∀ (k A : Type) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A] (n s : ℕ) (t : Fin n → A) (g : Fin s → A) (e : Fin s → Option (Fin n)), (∀ a, t a ∈ IsLocalRing.maximalIdeal A) → (∀ i j a, e i = some a → e j = some a → i = j) → (∀ i, Associated (g i) ((e i).elim 1 t)) → LinearIndependent (IsLocalRing.ResidueField A) (fun a => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t a)) → LinearIndependent (IsLocalRing.ResidueField A) (fun i : {i : Fin s // IsLocalRing.residue A (g i) = 0} => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (g i)) := by
  intro k A _ _ _ _ n s t g e htm hinj hass hli
  classical
  have hsome : ∀ i : {i : Fin s // IsLocalRing.residue A (g i) = 0}, (e i.1).isSome := by
    rintro ⟨i, hi⟩
    cases he : e i with
    | none =>
      exfalso
      have h1 := hass i
      rw [he] at h1
      have hu : IsUnit (g i) := h1.symm.isUnit isUnit_one
      exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu hi
    | some a => rfl
  let a : {i : Fin s // IsLocalRing.residue A (g i) = 0} → Fin n := fun i => (e i.1).get (hsome i)
  have hea : ∀ i, e i.1 = some (a i) := fun i => (Option.some_get _).symm
  have ha : Function.Injective a := fun i j h => Subtype.ext (hinj i.1 j.1 (a i) (hea i) (h ▸ hea j))
  have hass' : ∀ i : {i : Fin s // IsLocalRing.residue A (g i) = 0}, Associated (g i.1) (t (a i)) := by
    intro i
    have := hass i.1
    rw [hea i] at this
    exact this
  choose u hu using hass'
  let w : {i : Fin s // IsLocalRing.residue A (g i) = 0} → (IsLocalRing.ResidueField A)ˣ :=
    fun i => Units.map (IsLocalRing.residue A).toMonoidHom (u i)⁻¹
  have key : ∀ i, (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (g i.1) =
      (w i : IsLocalRing.ResidueField A) • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t (a i))) := by
    intro i
    have hg : g i.1 = t (a i) * (((u i)⁻¹ : Aˣ) : A) := by rw [← hu i, Units.mul_inv_cancel_right]
    have ht0 : IsLocalRing.residue A (t (a i)) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 (htm _)
    rw [hg, Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
      ← algebraMap_smul (IsLocalRing.ResidueField A) (t (a i)), ← algebraMap_smul (IsLocalRing.ResidueField A) (((u i)⁻¹ : Aˣ) : A)]
    simp only [IsLocalRing.ResidueField.algebraMap_eq, ht0, zero_smul, zero_add, w]
    rfl
  have := (hli.comp a ha).units_smul w
  convert this using 1
  funext i
  exact key i

theorem relSnc_of_regular_params : ∀ (k : Type) [Field k] [PerfectField k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d f] (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), (∀ i, (L i).IsLB) → (∀ x : X, IsClosed ({x} : Set X) → ∃ (n : ℕ) (t : Fin n → X.presheaf.stalk x) (c : ∀ i, (L i).ι) (hc : ∀ i, x ∈ (L i).U (c i)) (e : Fin s → Option (Fin n)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp (X.presheaf.stalk x) n t ∧ (∀ i j a, e i = some a → e j = some a → i = j) ∧ ∀ i, Associated ((X.presheaf.germ _ x (hc i)).hom ((σ i).f (c i))) ((e i).elim 1 t)) → RelSnc f d L σ := by
  intro k _ _ X f d _ s L σ hL H
  haveI : Smooth f := SmoothOfRelativeDimension.smooth d f
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine ⟨hL, fun x => ?_⟩
  suffices hcl : ∀ y : X, IsClosed ({y} : Set X) → ∃ C : SncChart f d L σ, y ∈ C.U by
    obtain ⟨y, hy, hxy⟩ := exists_closed_specialization k X f x
    obtain ⟨C, hC⟩ := hcl y hy
    exact ⟨C, hxy _ hC⟩
  intro x hx
  obtain ⟨n, t, c, hc, e, hrsp, hinj, hass⟩ := H x hx
  obtain ⟨U, hUa, hxU, hUc⟩ : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ i, U ≤ (L i).U (c i) := by
    have hxW : x ∈ ⋂ i, ((L i).U (c i) : Set X) := Set.mem_iInter.2 fun i => hc i
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxW
      (isOpen_iInter_of_finite fun i => ((L i).U (c i)).isOpen)
    exact ⟨V, hV, hxV, fun i y hy => Set.mem_iInter.1 (hVW hy) i⟩
  letI iBK : Algebra Γ(X, U) (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    ((IsLocalRing.residue (X.presheaf.stalk x)).comp (X.presheaf.germ U x hxU).hom).toAlgebra
  refine GlobalTheory.T.finrank_kaehler_affine_chart k X f d s L σ U c hUc x (IsLocalRing.ResidueField (X.presheaf.stalk x)) hUa hxU ?_ ?_
  · intro a
    rw [X.mem_basicOpen a x hxU]
    change ¬ IsLocalRing.residue _ ((X.presheaf.germ U x hxU).hom a) = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  letI iB : Algebra k Γ(X, U) := (cstOn f U).toAlgebra
  refine ⟨GlobalTheory.T.finrank_kaehler_residue_field k X f d U x hxU hUa, ?_⟩
  letI iBA : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  letI iA : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra
  haveI : IsScalarTower k Γ(X, U) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x)) := IsScalarTower.of_algebraMap_eq' rfl
  haveI := GlobalTheory.T.residue_field_formally_smooth k X f U x hxU hx
  have hli := GlobalTheory.T.regular_local_differentials_linearIndependent k (X.presheaf.stalk x) n t hrsp.1 hrsp.2
  have htm : ∀ a, t a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := fun a => hrsp.1 ▸ Ideal.subset_span ⟨a, rfl⟩
  let g : Fin s → X.presheaf.stalk x := fun i => X.presheaf.germ U x hxU (resG X (hUc i) ((σ i).f (c i)))
  have hg : ∀ i, g i = (X.presheaf.germ _ x (hc i)).hom ((σ i).f (c i)) := by
    intro i
    simp only [g, resG]
    exact X.presheaf.germ_res_apply (homOfLE (hUc i)) x hxU _
  have hass' : ∀ i, Associated (g i) ((e i).elim 1 t) := fun i => (hg i) ▸ hass i
  have h2 := linearIndependent_fibre_of_associated k (X.presheaf.stalk x) n s t g e htm hinj hass' hli
  exact linearIndependent_fibre_of_stalk k Γ(X, U) (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x))
    {i : Fin s // IsLocalRing.residue _ (g i) = 0} (fun i => resG X (hUc i.1) ((σ i.1).f (c i.1))) h2

end GlobalTheory.RegParams
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RegularSequenceStalkSncStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.regular_sequence_stalk_snc : ∀ (k : Type) [Field k] [PerfectField k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d f] (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), (∀ i, (L i).IsLB) → (∀ x : X, IsClosed ({x} : Set X) → ∃ (n : ℕ) (t : Fin n → X.presheaf.stalk x) (c : ∀ i, (L i).ι) (hc : ∀ i, x ∈ (L i).U (c i)) (e : Fin s → Option (Fin n)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp (X.presheaf.stalk x) n t ∧ (∀ i j a, e i = some a → e j = some a → i = j) ∧ ∀ i, Associated ((X.presheaf.germ _ x (hc i)).hom ((σ i).f (c i))) ((e i).elim 1 t)) → RelSnc f d L σ := by
  first | exact @_root_.GlobalTheory.RegParams.relSnc_of_regular_params | exact _root_.GlobalTheory.RegParams.relSnc_of_regular_params | (intros; apply _root_.GlobalTheory.RegParams.relSnc_of_regular_params <;> assumption)
end
end
