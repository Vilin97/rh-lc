module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientInclusionsEtaleOpenImmersionStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoprimeLevelStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsActionModelOfExt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCompactModelAboveFullLevelStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleSurjectiveLevelMapStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientModelByTameFiniteGroup
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
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteOrderAutomorphismFixingLevelTrivialOnFixedStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GoodPullback
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IterateEqIdOfTrivialOnFixedFibreStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelChangeExtendsBaseModelStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliLevelQuotientByFiniteGroup
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushforwardPolarisationBundleInvertibleOnModelStatement
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientModelByTameFiniteGroupStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.exists_quotient_model_by_tame_finite_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (Γ : Type) [Group Γ] [Finite Γ] (C : Cpt c t β) (b : O' →+* O) (k : F' →+* F) (r : U ⟶ U') (ν : SABMap t t' r) (ρ₀ : Γ →* Aut U) (τ₀ : Γ →* Aut t.G.left) (ρ : Γ →* Aut C.X) (τ : Γ →* Aut C.t.G.left) (mu : ∀ g, SABMap C.t C.t (ρ g).asIso.hom), IsDedFrac β → IsDedFrac β' → β.comp b = k.comp β' → IsFinite (spMap b) → r ≫ c' = c ≫ spMap k → (IsAffineHom r ∧ (∀ g, (ρ₀ g).asIso.hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ₀ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ₀ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) → IsProper t.G.hom → (∀ g, (mu g).φ = (τ g).asIso.hom ∧ C.j ≫ (ρ g).asIso.hom = (ρ₀ g).asIso.hom ≫ C.j ∧ C.m.φ ≫ (τ g).asIso.hom = (τ₀ g).asIso.hom ≫ C.m.φ ∧ (τ₀ g).asIso.hom ≫ ν.φ = ν.φ) → IsQProjOver (C.t.G.hom ≫ C.s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X) g, x ≫ (ρ g).asIso.hom = x → pullback.fst C.t.G.hom x ≫ (τ g).asIso.hom = pullback.fst C.t.G.hom x) → Good C.t → PushInvertible C.t.G C.t.PP.L → ∃ C' : Cpt c' t' β', Good C'.t ∧ Nonempty (C.Above C' b r ν) := by
  first | exact @GlobalTheory.Models.exists_quotient_model | exact GlobalTheory.Models.exists_quotient_model | (intros; apply GlobalTheory.Models.exists_quotient_model <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsDominantPullbackFstOfFlatOfInjective

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem isDominant_pullback_fst_of_flat_of_injective {O F : Type} [CommRing O] [Field F] (β : O →+* F)
    (hβ : Function.Injective β) {X : Scheme.{0}} (s : X ⟶ Sp O) [Flat s] :
    IsDominant (pullback.fst s (spMap β)) := by
  constructor
  intro x
  have hη : (spMap β) (IsLocalRing.closedPoint F) ⤳ s x := by
    refine (PrimeSpectrum.le_iff_specializes (R := O)
      (PrimeSpectrum.comap β (IsLocalRing.closedPoint F)) (s x)).mp ?_
    intro a ha
    have ha' : β a ∈ IsLocalRing.maximalIdeal F := ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at ha'
    have : a = 0 := hβ (by rw [ha', map_zero])
    rw [this]; exact Ideal.zero_mem _
  obtain ⟨y, hy, hy'⟩ := Flat.generalizingMap s hη
  refine closure_mono (Set.singleton_subset_iff.mpr ?_) hy.mem_closure
  rw [Scheme.Pullback.range_fst]
  exact ⟨_, hy'.symm⟩

theorem isPrimitiveRoot_map_of_isUnit {O k : Type} [CommRing O] [IsDomain O] [Field k] (ψ : O →+* k)
    {z : O} {A : ℕ} (hA : 0 < A) (hz : IsPrimitiveRoot z A) (hu : IsUnit (A : O)) :
    IsPrimitiveRoot (ψ z) A := by
  have : NeZero (A : k) := ⟨by simpa using (hu.map ψ).ne_zero⟩
  rw [← (Polynomial.isRoot_cyclotomic_iff (R := k) (n := A)), ← Polynomial.map_cyclotomic A ψ]
  exact Polynomial.IsRoot.map ψ (hz.isRoot_cyclotomic hA)

theorem galoisPart_eq_refl_of_fixes_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (S : ℕ) (β : RZ H S l.A →+* KA l) (C : Cpt Xo.s Xo.univ.t β) (r : Xo.X ≅ Xo.X) (ρ : C.X ≅ C.X) (σ : KA l ≃+* KA l), IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β → 0 < S → (∃ e, l.A ∣ S ^ e) → C.j ≫ ρ.hom = r.hom ≫ C.j → σ (baseKA l).ρ = (baseKA l).ρ → r.hom ≫ Xo.s = Xo.s ≫ spMap σ.toRingHom → ∀ (k : Type) [Field k] (x : Sp k ⟶ C.X), x ≫ ρ.hom = x → σ = RingEquiv.refl _ := by
  intro E _ _ _ H D l Xo S β C r ρ σ hinc hS ⟨e, he⟩ hj hρ hr k _ x hx
  have hA := l.A_pos
  have : NeZero l.A := ⟨hA.ne'⟩
  have hβ : Function.Injective β := fun a b h => Subtype.ext (by
    have h1 := hinc a
    rw [h, hinc b] at h1
    exact h1.symm)
  let z : RZ H S l.A := ⟨zeta l.A, Subring.subset_closure (by simp)⟩
  let t : RZ H S l.A := ⟨(S : ℂ)⁻¹, Subring.subset_closure (by simp)⟩
  have hβz : β z = (baseKA l).ζ := Subtype.ext (hinc z)
  have hζ : IsPrimitiveRoot (baseKA l).ζ l.A := (baseKA l).ζ_prim
  have hz : IsPrimitiveRoot z l.A := IsPrimitiveRoot.of_map_of_injective (hβz ▸ hζ) hβ
  have hSu : IsUnit (S : RZ H S l.A) := IsUnit.of_mul_eq_one t (Subtype.ext (by
    have : (S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
    simp [t, this]))
  have hAu : IsUnit (l.A : RZ H S l.A) := by
    refine isUnit_of_dvd_unit (Nat.cast_dvd_cast he) ?_
    rw [Nat.cast_pow]
    exact hSu.pow e
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ (baseKA l).ζ)
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have := C.flat
  have hd₁ := isDominant_pullback_fst_of_flat_of_injective β hβ C.s
  have hd₂ : IsDominant C.jQ := ⟨C.jQ_dense⟩
  have hd : IsDominant C.j := by unfold Cpt.j; infer_instance
  have hred : IsReduced C.X := by
    have := fun y => (C.normal y).1
    exact isReduced_of_isReduced_stalk _
  have hjs : C.j ≫ C.s = Xo.s ≫ spMap β := by
    rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]
  let ev : RZ H S l.A → (Polynomial ℤ →+* RZ H S l.A) := fun y => (Polynomial.aeval y).toRingHom
  have hev : σ.toRingHom.comp (β.comp (ev z)) = β.comp (ev (z ^ a)) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [ev, hβz, ha]
  have key : ρ.hom ≫ C.s ≫ spMap (ev z) = C.s ≫ spMap (ev (z ^ a)) := by
    refine ext_of_isDominant C.j ?_
    rw [reassoc_of% hj, reassoc_of% hjs, reassoc_of% hjs, reassoc_of% hr]
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← hev]
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (x ≫ C.s)
  have key₂ : CommRingCat.ofHom (ev z) ≫ ψ = CommRingCat.ofHom (ev (z ^ a)) ≫ ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hψ, Category.assoc, Category.assoc, ← key, reassoc_of% hx]
  have key₃ : ψ.hom z = ψ.hom z ^ a := by
    have := congrArg (fun f => f.hom Polynomial.X) key₂
    simpa [ev] using this
  have hp : IsPrimitiveRoot (ψ.hom z) l.A := isPrimitiveRoot_map_of_isUnit ψ.hom hA hz hAu
  have hmod : a ≡ 1 [MOD l.A] := by
    have hfin : IsOfFinOrder (ψ.hom z) := hp.isOfFinOrder hA.ne'
    rw [hp.eq_orderOf, ← hfin.pow_eq_pow_iff_modEq, pow_one]
    exact key₃.symm
  have hσζ : σ (baseKA l).ζ = (baseKA l).ζ := by
    rw [← ha]
    have hfin : IsOfFinOrder (baseKA l).ζ := hζ.isOfFinOrder hA.ne'
    rw [hζ.eq_orderOf, ← hfin.pow_eq_pow_iff_modEq, pow_one] at hmod
    exact hmod
  have hfinal : σ.toRingHom.toRatAlgHom = AlgHom.id ℚ (KA l) := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := KA l) (s := {H.rt0, zeta l.A}) rfl ?_
    rintro y (rfl | rfl)
    · exact hρ
    · exact hσζ
  ext1 y
  exact DFunLike.congr_fun hfinal y

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliLevelQuotientByFiniteGroupStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.moduli_level_quotient_by_finite_group : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₁ : Level H) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (k : KA l₀ →+* KA l₁), l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k → r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k → LevComp (Xo l₁).univ (Xo l₀).univ r ν → ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (ρ : Γ →* Aut (Xo l₁).X) (τ : Γ →* Aut (Xo l₁).univ.t.G.left) (mu : ∀ g, SABMap (Xo l₁).univ.t (Xo l₁).univ.t (ρ g).asIso.hom), Function.Injective ρ ∧ (IsAffineHom r ∧ (∀ g, (ρ g).asIso.hom ≫ r = r) ∧ ∀ V : (Xo l₀).X.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ((Xo l₁).X, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) ∧ ∀ ω, (mu ω).φ = (τ ω).asIso.hom ∧ (τ ω).asIso.hom ≫ ν.φ = ν.φ ∧ (∀ x, ((Xo l₁).univ.eta x).left ≫ (τ ω).asIso.hom = (ρ ω).asIso.hom ≫ ((Xo l₁).univ.eta x).left) ∧ ∃ (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁), σ (baseKA l₁).ρ = (baseKA l₁).ρ ∧ (ρ ω).asIso.hom ≫ (Xo l₁).s = (Xo l₁).s ≫ spMap σ.toRingHom ∧ ∀ x, ((Xo l₁).univ.etaA (g x)).left ≫ (τ ω).asIso.hom = (ρ ω).asIso.hom ≫ ((Xo l₁).univ.etaA x).left :=
  GlobalTheory.LevQuot.exists_level_quotient
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBaseModelSemiAbelian

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.BaseModelEx

theorem natCast_ne_zero_of_pt {R k : Type} [CommRing R] [Field k] (y : Sp k ⟶ Sp R) {S : ℕ} (h : IsUnit (S : R)) :
    (S : k) ≠ 0 := by
  have := h.map (Spec.preimage y).hom
  rw [map_natCast] at this
  exact this.ne_zero

theorem natCast_notMem {X : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (f : X ⟶ Sp R) (g : X ⟶ Sp R')
    {S : ℕ} (h : IsUnit (S : R')) (x : X) : (S : R) ∉ (f x).asIdeal := by
  have h1 : (S : X.residueField x) ≠ 0 := natCast_ne_zero_of_pt (X.fromSpecResidueField x ≫ g) h
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ f)
  have h2 : f x = (Spec.map φ) (IsLocalRing.closedPoint _) := by
    rw [hφ]
    exact (congrArg f (Scheme.fromSpecResidueField_apply x (IsLocalRing.closedPoint _))).symm
  rw [h2]
  intro hS
  have h3 : φ.hom (S : R) ∈ IsLocalRing.maximalIdeal (X.residueField x) := hS
  rw [map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero] at h3
  exact h3 h1

theorem isUnit_RZ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {S : ℕ} (A : ℕ) (hS : 0 < S) :
    IsUnit (S : RZ H S A) := by
  refine IsUnit.of_mul_eq_one ⟨(S : ℂ)⁻¹, Subring.subset_closure (by simp)⟩ (Subtype.ext ?_)
  have : (S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
  simp [this]

theorem exists_restrict {Z : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (s : Z ⟶ Sp R) (b : R →+* R') {S : ℕ}
    [IsOpenImmersion (spMap b)] (hS : IsUnit (S : R'))
    (hr : ∀ x : Sp R, x ∈ Set.range (spMap b) ↔ (S : R) ∉ x.asIdeal) (ρ : Z ⟶ Z) :
    ∃ ρ' : pullback s (spMap b) ⟶ pullback s (spMap b), ρ' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ ρ := by
  refine ⟨IsOpenImmersion.lift (pullback.fst s (spMap b)) (pullback.fst _ _ ≫ ρ) ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Pullback.range_fst]
  have := natCast_notMem (pullback.fst s (spMap b) ≫ ρ ≫ s) (pullback.snd s (spMap b)) hS w
  rw [Set.mem_preimage, hr]
  simpa using this

theorem pow_hom_eq_iterate {X : Scheme.{0}} (r : Aut X) (m : ℕ) :
    (r ^ m).asIso.hom = (fun f : X ⟶ X => f ≫ r.asIso.hom)^[m] (𝟙 _) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ← ih, pow_succ']; rfl

theorem card_stab_ne_zero {X Y : Scheme.{0}} {Γ : Type} [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (x : Y ⟶ X) {n J : ℕ}
    (hn : n.Prime) (h : ∀ g, x ≫ (ρ g).asIso.hom = x → g ^ n ^ J = 1) {k : Type} [Field k] (hk : (n : k) ≠ 0) :
    (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0 := by
  let P : Subgroup Γ :=
    { carrier := {g | x ≫ (ρ g).asIso.hom = x}
      one_mem' := by
        show x ≫ (ρ 1).asIso.hom = x
        rw [map_one]; exact Category.comp_id x
      mul_mem' := by
        intro a b ha hb
        show x ≫ (ρ (a * b)).asIso.hom = x
        rw [map_mul]
        show x ≫ (ρ b).asIso.hom ≫ (ρ a).asIso.hom = x
        rw [← Category.assoc, show x ≫ (ρ b).asIso.hom = x from hb]; exact ha
      inv_mem' := by
        intro a ha
        show x ≫ (ρ a⁻¹).asIso.hom = x
        rw [map_inv]
        show x ≫ (ρ a).asIso.inv = x
        exact (Iso.comp_inv_eq (ρ a).asIso).mpr (show x ≫ (ρ a).asIso.hom = x from ha).symm }
  haveI : Fact n.Prime := ⟨hn⟩
  have hP : IsPGroup n P := fun g => ⟨J, Subtype.ext (h g.1 g.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
  have : Nat.card {g // x ≫ (ρ g).asIso.hom = x} = n ^ m := hm
  rw [this, Nat.cast_pow]
  exact pow_ne_zero _ hk

theorem exists_baseModel : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (n J : ℕ) (T : Top Xo n (n ^ J)) (l₀ : Level H), AuxiliaryInertOddPrime H n → 1 ≤ J → l₀.A = 1 → Nonempty (BaseModel T l₀) := by
  intro hext L1 L2 L3 E _ _ _ H D Xo hD hN1 n J T l₀ hn hJ hA
  have hnp : n.Prime := hn.1
  have hM : 0 < l₀.M := by have := l₀.three_le; omega
  have hS : 0 < n * l₀.M := Nat.mul_pos hnp.pos hM
  have hN : 0 < n ^ J := pow_pos hnp.pos _
  have hdiv : n ^ J ∣ (n * l₀.M) ^ J := pow_dvd_pow_of_dvd (dvd_mul_right _ _) _
  let l₁ : Level H := { l₀ with A := n ^ J, A_pos := hN }
  have h₁ : l₁.A = n ^ J := rfl
  have R₀ := GlobalTheory.BaseRing.isDedFrac_RZ E H l₀ (n * l₀.M) 0 hS (by simp [hA])
  rw [hA] at R₀
  obtain ⟨⟨β, hβ⟩, ft₀, ded₀⟩ := R₀
  obtain ⟨⟨β₁, hβ₁⟩, ft₁, ded₁⟩ := GlobalTheory.BaseRing.isDedFrac_RZ E H l₁ (n * l₀.M) J hS hdiv
  obtain ⟨⟨b, hb⟩, hb2⟩ := GlobalTheory.T.cmModelCoefficient_inclusions_etale_openImmersion E H (n * l₀.M) (n * l₀.M) 1 (n ^ J) J hS hN dvd_rfl (one_dvd _)
  obtain ⟨bfin, -, -⟩ := (hb2 b hb).1 rfl hdiv
  obtain ⟨⟨b', hb'⟩, hb2'⟩ := GlobalTheory.T.cmModelCoefficient_inclusions_etale_openImmersion E H n (n * l₀.M) (n ^ J) (n ^ J) J hS hN (dvd_mul_right _ _) dvd_rfl
  obtain ⟨bop, brange⟩ := (hb2' b' hb').2 rfl
  obtain ⟨C₁, q, hq, qm, qfin, qj, qφ, qp⟩ := GlobalTheory.T.exists_compactModel_above_fullLevel E H D Xo n (n ^ J) T l₁ h₁ (n * l₀.M) J β₁ b' hS
    (dvd_mul_right _ _) hdiv hβ₁ hb'
  obtain ⟨k, r, ν, hr, hk, lev, -, -, -, -, -, rsurj⟩ := GlobalTheory.T.exists_finite_etale_surjective_levelMap E H D Xo hN1 l₀ l₁
    ⟨dvd_rfl, le_rfl, by rw [hA]; exact one_dvd _⟩
  obtain ⟨Γ, _, _, ρ₀, τ₀, ν₀, inj, quot, hω⟩ := GlobalTheory.T.moduli_level_quotient_by_finite_group L1 L2 L3 E H D Xo hD hN1 l₀ l₁ r ν k hA rfl rfl hk hr lev
  have hU : IsUnit ((n * l₀.M : ℕ) : RZ H (n * l₀.M) (n ^ J)) := isUnit_RZ H _ hS
  obtain ⟨ρ, τ, mu, hact⟩ := GlobalTheory.exists_action_model hext E H _ _ _ (Xo l₁).s (Xo l₁).univ.t β₁ C₁ _
    (pullback.lift q C₁.s hq) Γ ρ₀ τ₀ ν₀ (ded₁ β₁ hβ₁) ft₁ (Xo l₁).univ.proper inferInstance (fun g => (hω g).1) (by
      intro ω
      obtain ⟨h1, -, -, g, σ, h4, h5, h6⟩ := hω ω
      obtain ⟨ρZ, hρZ⟩ := T.sym l₁ h₁ (ρ₀ ω).asIso (ν₀ ω) g σ h4 h5 (by rw [h1]; exact h6)
      obtain ⟨ρ', hρ'⟩ := exists_restrict T.s b' hU brange ρZ.hom
      refine ⟨ρ', ?_⟩
      rw [← cancel_mono (pullback.fst T.s (spMap b'))]
      simp only [Category.assoc, hρ', pullback.lift_fst, pullback.lift_fst_assoc]
      rw [← Category.assoc, qj, hρZ])
  have hover : ∀ (κ : Type) [Field κ] (x : Sp κ ⟶ C₁.X) (ω : Γ), x ≫ (ρ ω).asIso.hom = x →
      (ρ₀ ω).asIso.hom ≫ (Xo l₁).s = (Xo l₁).s := by
    intro κ _ x ω hx
    obtain ⟨-, -, -, g, σ, h4, h5, -⟩ := hω ω
    have := GlobalTheory.galoisPart_eq_refl_of_fixes_point E H D l₁ (Xo l₁) (n * l₀.M) β₁ C₁ (ρ₀ ω).asIso (ρ ω).asIso σ hβ₁ hS ⟨J, hdiv⟩
      (hact ω).2.1 h4 h5 κ x hx
    subst this
    rw [h5]
    exact (congrArg _ (Spec.map_id _)).trans (Category.comp_id _)
  have hφ : ∀ ω, C₁.m.φ ≫ (mu ω).φ = (ν₀ ω).φ ≫ C₁.m.φ := fun ω => by
    rw [(hact ω).1, (hω ω).1]; exact (hact ω).2.2
  have htriv : ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ C₁.X) (ω : Γ), x ≫ (ρ ω).asIso.hom = x →
      pullback.fst C₁.t.G.hom x ≫ (mu ω).φ = pullback.fst C₁.t.G.hom x := by
    intro κ _ _ x ω hx
    exact GlobalTheory.T.finiteOrderAutomorphism_fixing_level_trivial_on_fixedFibre L1 L2 L3 E H D l₁ (Xo l₁) (n * l₀.M) β₁ C₁ (ρ₀ ω).asIso (ν₀ ω) (ρ ω).asIso (mu ω) hβ₁ hS ⟨J, hdiv⟩
      (hact ω).2.1 (hφ ω) (dvd_mul_left _ _) (hover κ x ω hx) (by rw [(hω ω).1]; exact (hω ω).2.2.1)
      ⟨τ ω, Nat.card Γ, Nat.card_pos, by rw [← map_pow, pow_card_eq_one', map_one], (hact ω).1.symm⟩ κ x hx
  have hcard : ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ C₁.X),
      (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : κ) ≠ 0 := by
    intro κ _ _ x
    refine card_stab_ne_zero ρ x (J := J) hnp (fun ω hx => ?_) ?_
    · obtain ⟨h1, -, h3, g, σ, -, -, h6⟩ := hω ω
      have := GlobalTheory.T.iterate_eq_id_of_trivial_on_fixed_fibre L1 L2 L3 E H D l₁ (Xo l₁) (n * l₀.M) β₁ C₁ (ρ₀ ω).asIso (ν₀ ω) (ρ ω).asIso (mu ω) hβ₁ hS ⟨J, hdiv⟩
        (hact ω).2.1 (hφ ω) (hover κ x ω hx) (by rw [h1]; exact h3) g (by rw [h1]; exact h6) κ x hx (htriv κ x ω hx)
      apply inj
      rw [map_pow, map_one]
      exact Aut.ext (Iso.ext ((pow_hom_eq_iterate _ _).trans this))
    · have := natCast_ne_zero_of_pt (x ≫ C₁.s) hU
      rw [Nat.cast_mul] at this
      exact left_ne_zero_of_mul this
  have good₁ : Good C₁.t := good_pullback L3.gtBaseChange E H _ _ T.t C₁.t q qm T.good
  have push := GlobalTheory.T.pushforward_polarisationBundle_invertible_on_model L1 L2 L3 E H D l₁ _ _ _ (baseKA l₁) _ (Xo l₁).s (Xo l₁).univ (Xo l₁).s β₁ C₁
    (ded₁ β₁ hβ₁) good₁.2.2
  have hcomm : β₁.comp b = k.comp β := by
    ext x
    exact (hβ₁ (b x)).trans ((hb x).trans ((hβ x).symm.trans (hk (β x)).symm))
  obtain ⟨C, good, ⟨above⟩⟩ := GlobalTheory.T.exists_quotient_model_by_tame_finite_group E H _ _ _ (Xo l₁).s (Xo l₁).univ.t β₁ _ _ _ (Xo l₀).s (Xo l₀).univ.t β Γ C₁
    b k r ν ρ₀ τ₀ ρ τ mu (ded₁ β₁ hβ₁) (ded₀ β hβ) hcomm bfin hr quot (Xo l₁).univ.proper
    (fun g => ⟨(hact g).1, (hact g).2.1, (hact g).2.2, (hω g).2.1⟩) qp hcard
    (fun κ _ _ x g hx => by rw [← (hact g).1]; exact htriv κ x g hx) good₁ push
  have hcop : (n ^ J).Coprime l₁.M := ((GlobalTheory.T.exists_two_inert_odd_primes_coprime_level E H).2 n hn l₁).pow_left J
  exact ⟨⟨hA, β, hβ, C, good,
    GlobalTheory.T.levelChange_extends_base_model hext L1 L2 L3 E H D Xo n (n ^ J) T hD l₀ l₁ h₁ _ _ β β₁ C C₁ b r ν above b' q hq (ded₀ β hβ)
      (ded₁ β₁ hβ₁) ft₀ bfin qfin qj hA rfl rfl hcop lev rsurj ⟨k, hk, hr, hcomm⟩,
    l₁, rfl, rfl, h₁, β₁, hβ₁, C₁, b, hb, r, ν, lev, rsurj, above, b', hb', q, hq, qfin, qm, qj, qφ⟩⟩

end GlobalTheory.BaseModelEx

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBaseModelSemiAbelianStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.exists_base_model_semiAbelian : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (n J : ℕ) (T : Top Xo n (n ^ J)) (l₀ : Level H), AuxiliaryInertOddPrime H n → 1 ≤ J → l₀.A = 1 → Nonempty (BaseModel T l₀) := by
  first | exact @GlobalTheory.BaseModelEx.exists_baseModel | exact GlobalTheory.BaseModelEx.exists_baseModel | (intros; apply GlobalTheory.BaseModelEx.exists_baseModel <;> assumption)
end
end
