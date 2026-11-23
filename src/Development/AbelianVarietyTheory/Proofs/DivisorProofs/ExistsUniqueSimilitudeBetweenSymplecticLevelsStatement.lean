module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaAwayPowSelf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCycAwayHomComplex
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Lift
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
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.AlphaPair
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelOnFibreUniqueTwist

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.UPel.TensorTorsionNsmul

open scoped TensorProduct

variable {L : Type} [AddCommGroup L]

theorem tmul_surjective (n : ℕ) (x : ZMod n ⊗[ℤ] L) : ∃ a : L, (1 : ZMod n) ⊗ₜ[ℤ] a = x := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul r a =>
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective r
    refine ⟨m • a, ?_⟩
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', zsmul_eq_mul, _root_.mul_one]
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, TensorProduct.tmul_add _ _ _⟩

theorem eq_nsmul_of_tmul_eq_zero {n : ℕ} {a : L} (h : (1 : ZMod n) ⊗ₜ[ℤ] a = 0) : ∃ d, a = n • d := by
  let e : ZMod n ≃ₗ[ℤ] (ℤ ⧸ Ideal.span {(n : ℤ)}) :=
    (Int.quotientSpanNatEquivZMod n).symm.toAddEquiv.toIntLinearEquiv
  have he : e 1 = 1 := map_one (Int.quotientSpanNatEquivZMod n).symm
  have h1 := congrArg (fun y => TensorProduct.quotTensorEquivQuotSMul L (Ideal.span {(n : ℤ)})
    (LinearMap.rTensor L e.toLinearMap y)) h
  simp only [LinearMap.rTensor_tmul, map_zero, LinearEquiv.coe_coe, he,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero] at h1
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨d, -, hd⟩ := h1
  exact ⟨d, by rw [← hd, natCast_zsmul]⟩

theorem tmul_nsmul_eq_zero (n : ℕ) (d : L) : (1 : ZMod n) ⊗ₜ[ℤ] (n • d) = 0 := by
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', nsmul_eq_mul, _root_.mul_one, ZMod.natCast_self,
    TensorProduct.zero_tmul]

variable {G : Type} [Group G]

theorem map_nsmul_of_add {φ : L → G} (hφ : ∀ a c, φ (a + c) = φ a * φ c) (m : ℕ) (a : L) :
    φ (m • a) = φ a ^ m := by
  have h0 : φ 0 = 1 := by
    have := hφ 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  induction m with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ m ih => rw [succ_nsmul, hφ, ih, pow_succ]

theorem tmul_eq_tmul_iff {n : ℕ} {φ : L → G} (hφ : ∀ a c, φ (a + c) = φ a * φ c)
    (hk : ∀ a, φ a = 1 ↔ ∃ b, a = n • b) (a c : L) :
    (1 : ZMod n) ⊗ₜ[ℤ] a = 1 ⊗ₜ c ↔ φ a = φ c := by
  have e : φ a = φ (a - c) * φ c := by rw [← hφ, sub_add_cancel]
  rw [e, mul_eq_right, hk, ← sub_eq_zero, ← TensorProduct.tmul_sub]
  constructor
  · exact eq_nsmul_of_tmul_eq_zero
  · rintro ⟨d, hd⟩
    rw [hd]
    exact tmul_nsmul_eq_zero n d

def matchMap (n : ℕ) (φ φ' : L → G) (hφ : ∀ a c, φ (a + c) = φ a * φ c)
    (hφ' : ∀ a c, φ' (a + c) = φ' a * φ' c) (hk : ∀ a, φ a = 1 ↔ ∃ b, a = n • b)
    (hr : ∀ b, ∃ c, φ c = φ' b) : (ZMod n ⊗[ℤ] L) →ₗ[ZMod n] (ZMod n ⊗[ℤ] L) :=
  LinearMap.liftBaseChange (ZMod n)
    (AddMonoidHom.mk' (fun b => (1 : ZMod n) ⊗ₜ[ℤ] Classical.choose (hr b)) (fun b b' => by
      rw [← TensorProduct.tmul_add, tmul_eq_tmul_iff hφ hk, hφ, Classical.choose_spec (hr _),
        Classical.choose_spec (hr _), Classical.choose_spec (hr _), hφ']) : L →+ ZMod n ⊗[ℤ] L).toIntLinearMap

theorem matchMap_tmul (n : ℕ) (φ φ' : L → G) (hφ : ∀ a c, φ (a + c) = φ a * φ c)
    (hφ' : ∀ a c, φ' (a + c) = φ' a * φ' c) (hk : ∀ a, φ a = 1 ↔ ∃ b, a = n • b)
    (hr : ∀ b, ∃ c, φ c = φ' b) (b c : L) :
    matchMap n φ φ' hφ hφ' hk hr ((1 : ZMod n) ⊗ₜ b) = 1 ⊗ₜ c ↔ φ c = φ' b := by
  rw [matchMap, LinearMap.liftBaseChange_tmul, one_smul]
  change (1 : ZMod n) ⊗ₜ[ℤ] Classical.choose (hr b) = _ ↔ _
  rw [tmul_eq_tmul_iff hφ hk, Classical.choose_spec (hr b), eq_comm]

theorem exists_equiv (n : ℕ) (φ φ' : L → G) (hφ : ∀ a c, φ (a + c) = φ a * φ c)
    (hφ' : ∀ a c, φ' (a + c) = φ' a * φ' c) (hk : ∀ a, φ a = 1 ↔ ∃ b, a = n • b)
    (hk' : ∀ a, φ' a = 1 ↔ ∃ b, a = n • b) (hr : ∀ b, ∃ c, φ c = φ' b) (hr' : ∀ c, ∃ b, φ' b = φ c) :
    ∃ e : (ZMod n ⊗[ℤ] L) ≃ₗ[ZMod n] (ZMod n ⊗[ℤ] L), ∀ b c, e (1 ⊗ₜ b) = 1 ⊗ₜ c ↔ φ c = φ' b := by
  let f := matchMap n φ φ' hφ hφ' hk hr
  let g := matchMap n φ' φ hφ' hφ hk' hr'
  have hfg : ∀ x, g (f x) = x := by
    intro x
    obtain ⟨b, rfl⟩ := tmul_surjective n x
    obtain ⟨c, hc⟩ := hr b
    obtain ⟨d, hd⟩ := hr' c
    rw [(matchMap_tmul n φ φ' hφ hφ' hk hr b c).2 hc, (matchMap_tmul n φ' φ hφ' hφ hk' hr' c d).2 hd,
      tmul_eq_tmul_iff hφ' hk', hd, hc]
  have hgf : ∀ x, f (g x) = x := by
    intro x
    obtain ⟨b, rfl⟩ := tmul_surjective n x
    obtain ⟨c, hc⟩ := hr' b
    obtain ⟨d, hd⟩ := hr c
    rw [(matchMap_tmul n φ' φ hφ' hφ hk' hr' b c).2 hc, (matchMap_tmul n φ φ' hφ hφ' hk hr c d).2 hd,
      tmul_eq_tmul_iff hφ hk, hd, hc]
  refine ⟨LinearEquiv.ofLinear f g (LinearMap.ext hgf) (LinearMap.ext hfg), fun b c => ?_⟩
  exact matchMap_tmul n φ φ' hφ hφ' hk hr b c

end GlobalTheory.UPel.TensorTorsionNsmul

namespace GlobalTheory.UPel

open scoped TensorProduct

end GlobalTheory.UPel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueSimilitudeBetweenSymplecticLevels

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.HTSympCover

open scoped TensorProduct

theorem piScalarRight_tmul_one {h M : ℕ} (a : Fin h ⊕ Fin h → ℤ) :
    TensorProduct.piScalarRight ℤ (ZMod M) (ZMod M) (Fin h ⊕ Fin h) ((1 : ZMod M) ⊗ₜ[ℤ] a) = reduceMod M a := by
  funext i
  simp [TensorProduct.piScalarRight_apply, reduceMod]

theorem omegaMod_reduceMod {h M : ℕ} (a c : Fin h ⊕ Fin h → ℤ) :
    omegaMod M (reduceMod M a) (reduceMod M c) = ((omegaStd a c : ℤ) : ZMod M) := by
  simp [omegaMod, omegaStd, reduceMod]

theorem sp_exists_spMap {A B : Type} [CommRing A] [CommRing B] (g : Sp B ⟶ Sp A) : ∃ f : A →+* B, g = spMap f :=
  ⟨(Spec.preimage g).hom, by simp [spMap]⟩

theorem sympCond_fibre_existsUnique : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  Odd M → 1 ≤ h → ∀ (σ : sympSimGrp h M → (cycAway M →+* cycAway M)),
  (∀ a, ∃ n : ℕ, IsMultOf a n ∧ σ a (zetaAway M) = zetaAway M ^ n) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S)
    (t₁ t₁' : Sp K ⟶ Sp (cycAway M)) (lv lv' : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ o.A)),
    SympCond o h M (Over.mk x) t₁ lv → SympCond o h M (Over.mk x) t₁' lv' →
    ∃! a : sympSimGrp h M, t₁ ≫ spMap (σ a) = t₁' ∧ ∀ c, sympTwist a lv c = lv' c := by
  intro p _ D R _ b N h M hM hodd hh σ hσ S t o K _ _ x t₁ t₁' lv lv' H H'
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨hadd, -, hgeo⟩ := H
  obtain ⟨hadd', -, hgeo'⟩ := H'
  obtain ⟨β, hβ⟩ := sp_exists_spMap t₁
  obtain ⟨β', hβ'⟩ := sp_exists_spMap t₁'
  have hζ : ∀ g₀ : cycAway M →+* K, g₀ (zetaAway M) ^ M = 1 := fun g₀ => by
    rw [← map_pow, zetaAway_pow_self M hM.ne', map_one]
  let z : Kˣ := Units.ofPowEqOne _ M (hζ β) hM.ne'
  let z' : Kˣ := Units.ofPowEqOne _ M (hζ β') hM.ne'
  obtain ⟨hk, hon, hW⟩ := hgeo K (𝟙 _) β z (by rw [Category.id_comp, hβ]) rfl
  obtain ⟨hk', hon', hW'⟩ := hgeo' K (𝟙 _) β' z' (by rw [Category.id_comp, hβ']) rfl
  let jx : Over.mk (𝟙 (Sp K) ≫ x) ⟶ Over.mk x := Over.homMk (𝟙 _) rfl
  have canc : ∀ f g : Over.mk x ⟶ o.A, jx ≫ f = jx ≫ g → f = g := by
    intro f g e
    apply Over.OverMorphism.ext
    have := congrArg CommaMorphism.left e
    simpa [jx] using this
  let φ : (Fin h ⊕ Fin h → ℤ) → (Over.mk (𝟙 (Sp K) ≫ x) ⟶ o.A) := fun a => jx ≫ lv a
  let φ' : (Fin h ⊕ Fin h → ℤ) → (Over.mk (𝟙 (Sp K) ≫ x) ⟶ o.A) := fun a => jx ≫ lv' a
  have hφ : ∀ a c, φ (a + c) = φ a * φ c := fun a c => by simp only [φ, hadd, MonObj.comp_mul]
  have hφ' : ∀ a c, φ' (a + c) = φ' a * φ' c := fun a c => by simp only [φ', hadd', MonObj.comp_mul]
  have hkφ : ∀ a, φ a = 1 ↔ ∃ c, a = M • c := fun a => hk a
  have hkφ' : ∀ a, φ' a = 1 ↔ ∃ c, a = M • c := fun a => hk' a
  have hr : ∀ b, ∃ c, φ c = φ' b := fun b => hon (φ' b) (by
    rw [← GlobalTheory.UPel.TensorTorsionNsmul.map_nsmul_of_add hφ', (hkφ' _).2 ⟨b, rfl⟩])
  have hr' : ∀ c, ∃ b, φ' b = φ c := fun c => hon' (φ c) (by
    rw [← GlobalTheory.UPel.TensorTorsionNsmul.map_nsmul_of_add hφ, (hkφ _).2 ⟨c, rfl⟩])
  obtain ⟨e, he⟩ := GlobalTheory.UPel.TensorTorsionNsmul.exists_equiv M φ φ' hφ hφ' hkφ hkφ' hr hr'
  let E := TensorProduct.piScalarRight ℤ (ZMod M) (ZMod M) (Fin h ⊕ Fin h)
  let e' := E.symm.trans (e.trans E)
  have he' : ∀ b c, e' (reduceMod M b) = reduceMod M c ↔ φ c = φ' b := by
    intro b c
    rw [← he, ← piScalarRight_tmul_one, ← piScalarRight_tmul_one]
    show E (e (E.symm (E _))) = E _ ↔ _
    rw [LinearEquiv.symm_apply_apply, E.injective.eq_iff]
  have hz : IsPrimitiveRoot z M := IsPrimitiveRoot.coe_units_iff.1 (isPrimitiveRoot_map hM.ne' β)
  obtain ⟨i, hcop, he_i⟩ := exists_pow_of_isLocalRing hM.ne' β β'
  have hzi : z ^ i = z' := Units.ext (by
    rw [Units.val_pow_eq_pow_val]
    exact he_i.symm)
  have h2u : IsUnit (2 : ZMod M) := by
    have := (ZMod.isUnit_iff_coprime 2 M).2 (Nat.coprime_two_left.2 hodd)
    exact_mod_cast this
  have hval : ∀ a b c d, φ c = φ' a → φ d = φ' b →
      ((omegaStd c d : ℤ) : ZMod M) = (i : ZMod M) * ((omegaStd a b : ℤ) : ZMod M) := by
    intro a b c d hc hd
    have w₁ := hW c d
    have w₂ := hW' a b
    change Out.WeilIs _ _ _ (φ' a) (φ' b) _ at w₂
    change Out.WeilIs _ _ _ (φ c) (φ d) _ at w₁
    rw [← hc, ← hd] at w₂
    have e₁ := H1.unitOn_injective
      (GlobalTheory.CommutatorPairing.weilIs_unique GlobalTheory.globalFns_holds o.ab (pull_isLB o.isLB _) w₂ w₁)
    rw [← hzi, ← zpow_natCast, ← zpow_mul] at e₁
    have h2 : z ^ ((i : ℤ) * (2 * omegaStd a b) - 2 * omegaStd c d) = 1 := by
      rw [zpow_sub, e₁, mul_inv_cancel]
    rw [hz.zpow_eq_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
    push_cast at h2
    have h3 : (2 : ZMod M) * ((i : ZMod M) * ((omegaStd a b : ℤ) : ZMod M) - ((omegaStd c d : ℤ) : ZMod M)) = 0 := by
      linear_combination h2
    have h4 := h2u.mul_right_eq_zero.1 h3
    linear_combination -h4
  have hmul : ∀ X Y, omegaMod M (e' X) (e' Y) = (i : ZMod M) * omegaMod M X Y := by
    intro X Y
    obtain ⟨a, rfl⟩ : ∃ a, reduceMod M a = X := ⟨liftMod X, reduceMod_liftMod X⟩
    obtain ⟨b, rfl⟩ : ∃ b, reduceMod M b = Y := ⟨liftMod Y, reduceMod_liftMod Y⟩
    obtain ⟨c, hc⟩ := hr a
    obtain ⟨d, hd⟩ := hr b
    rw [(he' a c).2 hc, (he' b d).2 hd, omegaMod_reduceMod, omegaMod_reduceMod]
    exact hval a b c d hc hd
  have hsim : e' ∈ sympSimGrp h M :=
    ⟨ZMod.unitOfCoprime i hcop, fun X Y => by rw [ZMod.coe_unitOfCoprime]; exact hmul X Y⟩
  let a₀ : sympSimGrp h M := ⟨e', hsim⟩
  have hmul₀ : IsMultOf a₀ i := hmul
  refine ⟨a₀, ⟨?_, fun c => canc _ _ ?_⟩, ?_⟩
  · obtain ⟨n, hn, hσn⟩ := hσ a₀
    have hni : (n : ZMod M) = i := isMultOf_unique hh hn hmul₀
    have hc : β.comp (σ a₀) = β' := cycAway_hom_ext hM.ne' (by
      rw [RingHom.comp_apply, hσn, zetaAway_pow_eq M hM.ne' hni, map_pow, he_i])
    rw [hβ, hβ', spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  · change φ (liftMod (e' (reduceMod M c))) = φ' c
    exact (he' c _).1 (reduceMod_liftMod _).symm
  · rintro a ⟨-, ha⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro X
    obtain ⟨b', rfl⟩ : ∃ b', reduceMod M b' = X := ⟨liftMod X, reduceMod_liftMod X⟩
    have h1 : φ (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M b'))) = φ' b' :=
      congrArg (jx ≫ ·) (ha b')
    rw [← reduceMod_liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M b'))]
    exact ((he' b' _).2 h1).symm

end GlobalTheory.HTSympCover
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueSimilitudeBetweenSymplecticLevelsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

theorem _root_.GlobalTheory.T.existsUnique_similitude_between_symplecticLevels : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  Odd M → 1 ≤ h → ∀ (σ : sympSimGrp h M → (cycAway M →+* cycAway M)),
  (∀ a, ∃ n : ℕ, IsMultOf a n ∧ σ a (zetaAway M) = zetaAway M ^ n) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S)
    (t₁ t₁' : Sp K ⟶ Sp (cycAway M)) (lv lv' : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ o.A)),
    SympCond o h M (Over.mk x) t₁ lv → SympCond o h M (Over.mk x) t₁' lv' →
    ∃! a : sympSimGrp h M, t₁ ≫ spMap (σ a) = t₁' ∧ ∀ c, sympTwist a lv c = lv' c := by
  first | exact @GlobalTheory.HTSympCover.sympCond_fibre_existsUnique | exact GlobalTheory.HTSympCover.sympCond_fibre_existsUnique | (intros; apply GlobalTheory.HTSympCover.sympCond_fibre_existsUnique <;> assumption)
end
end
