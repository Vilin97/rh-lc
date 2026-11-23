module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSubgroupOfFinite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompEqIdOfTwists
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjTwistBySimilitude
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliRepOfBase
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompEqIdOfTwists
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleSurjectiveLevelMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapToUniversalObjectUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteDimensionalField

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.LevQuot

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem finiteDimensional_field (l : Level H) : FiniteDimensional ℚ (KA l) := by
  have hr : IsIntegral ℚ H.rt0 := by
    refine IsIntegral.of_pow two_pos ?_
    rw [H.sqrt_neg_disc_sq]
    have : IsIntegral ℚ (algebraMap ℚ ℂ (-(H.d : ℚ))) := isIntegral_algebraMap
    simpa using this
  have hz : IsIntegral ℚ (zeta l.A) :=
    ((Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').isIntegral l.A_pos).tower_top
  show FiniteDimensional ℚ (IntermediateField.adjoin ℚ {H.rt0, zeta l.A})
  refine IntermediateField.finiteDimensional_adjoin ?_
  rintro x (rfl | rfl)
  · exact hr
  · exact hz

theorem field_hom_ext (l : Level H) {k : Type} [Field k] (β β' : KA l →+* k)
    (h₁ : β (baseKA l).ρ = β' (baseKA l).ρ) (h₂ : β (baseKA l).ζ = β' (baseKA l).ζ) : β = β' := by
  have : CharZero k := (RingHom.charZero_iff β.injective).1 inferInstance
  have key : β.toRatAlgHom = β'.toRatAlgHom := by
    refine IntermediateField.adjoin_algHom_ext ℚ (s := {H.rt0, zeta l.A}) ?_
    rintro x (rfl | rfl)
    · exact h₁
    · exact h₂
  refine RingHom.ext fun x => ?_
  exact DFunLike.congr_fun key x

theorem finite_fieldAut (l : Level H) : Finite (KA l ≃+* KA l) := by
  have := finiteDimensional_field l
  refine Finite.of_injective (fun σ : KA l ≃+* KA l => (σ : KA l →+* KA l).toRatAlgHom) ?_
  intro a b hab
  refine RingEquiv.ext fun x => ?_
  exact DFunLike.congr_fun hab x

theorem exists_fieldAut (l : Level H) {k : Type} [Field k] (β β' : KA l →+* k)
    (h₁ : β (baseKA l).ρ = β' (baseKA l).ρ) :
    ∃ σ : KA l ≃+* KA l, σ (baseKA l).ρ = (baseKA l).ρ ∧ β.comp σ.toRingHom = β' := by
  have := finiteDimensional_field l
  have : CharZero k := (RingHom.charZero_iff β.injective).1 inferInstance
  have : NeZero l.A := ⟨l.A_pos.ne'⟩
  have hp : IsPrimitiveRoot (β (baseKA l).ζ) l.A := (baseKA l).ζ_prim.map_of_injective β.injective
  have hA : β' (baseKA l).ζ ^ l.A = 1 := by rw [← map_pow, (baseKA l).ζ_prim.pow_eq_one, map_one]
  obtain ⟨i, -, hi⟩ := hp.eq_pow_of_pow_eq_one hA
  let βQ := β.toRatAlgHom
  let β'Q := β'.toRatAlgHom
  have hle : IntermediateField.adjoin ℚ ({H.rt0, zeta l.A} : Set ℂ) ≤
      (βQ.fieldRange.comap β'Q).map (KA l).val := by
    rw [IntermediateField.adjoin_le_iff]
    rintro y (rfl | rfl)
    · exact ⟨(baseKA l).ρ, ⟨(baseKA l).ρ, h₁⟩, rfl⟩
    · exact ⟨(baseKA l).ζ, ⟨(baseKA l).ζ ^ i, by simpa [βQ, β'Q] using hi⟩, rfl⟩
  have hmem : ∀ x, β'Q x ∈ βQ.fieldRange := by
    intro x
    obtain ⟨z, hz, hzx⟩ := hle x.2
    obtain rfl : z = x := Subtype.ext hzx
    exact hz
  let e := AlgEquiv.ofInjectiveField βQ
  let τ : KA l →ₐ[ℚ] βQ.fieldRange := β'Q.codRestrict βQ.fieldRange.toSubalgebra hmem
  let σQ : KA l →ₐ[ℚ] KA l := e.symm.toAlgHom.comp τ
  have hσ : ∀ x, β (σQ x) = β' x := by
    intro x
    have := congrArg Subtype.val (e.apply_symm_apply (τ x))
    exact this
  let σ := (AlgEquiv.ofBijective σQ (AlgHom.bijective σQ)).toRingEquiv
  refine ⟨σ, ?_, ?_⟩
  · apply β.injective
    exact (hσ _).trans h₁.symm
  · refine RingHom.ext fun x => ?_
    exact hσ x

variable {l : Level H}

theorem isReduced_moduli (Xo : Moduli D l) : IsReduced Xo.X := by
  have : SmoothOfRelativeDimension D.dim Xo.s := Xo.smooth
  exact (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field (KA l) Xo.X Xo.s
    (SmoothOfRelativeDimension.smooth D.dim Xo.s)).1

def SemiTwist (Xo : Moduli D l) (f : Xo.X ⟶ Xo.X) (φ : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left) (g : D.La → D.La)
    (σ : KA l →+* KA l) : Prop :=
  f ≫ Xo.s = Xo.s ≫ spMap σ ∧ (∀ a, (Xo.univ.eta a).left ≫ φ = f ≫ (Xo.univ.eta a).left) ∧
    ∀ a, (Xo.univ.etaA (g a)).left ≫ φ = f ≫ (Xo.univ.etaA a).left

theorem SemiTwist.comp {Xo : Moduli D l} {f f' φ φ' g g' σ σ'} (h : SemiTwist Xo f φ g σ)
    (h' : SemiTwist Xo f' φ' g' σ') : SemiTwist Xo (f ≫ f') (φ ≫ φ') (g ∘ g') (σ.comp σ') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨?_, fun a => ?_, fun a => ?_⟩
  · rw [Category.assoc, h1', ← Category.assoc, h1, Category.assoc, GlobalTheory.LevCover.spMap_comp'']
  · rw [← Category.assoc, h2, Category.assoc, h2', Category.assoc]
  · rw [Function.comp_apply, ← Category.assoc, h3, Category.assoc, h3', Category.assoc]

theorem SemiTwist.eq_id {Xo : Moduli D l} {f g σ} (m : SABMap Xo.univ.t Xo.univ.t f) (h : SemiTwist Xo f m.φ g σ)
    (hσ : σ = RingHom.id _) (hg : ∀ a, Xo.univ.etaA (g a) = Xo.univ.etaA a) : f = 𝟙 _ := by
  obtain ⟨h1, h2, h3⟩ := h
  subst hσ
  have hs : f ≫ Xo.s = Xo.s := by rw [h1, GlobalTheory.LevelCover.spMap_id', Category.comp_id]
  obtain ⟨u, -, hu⟩ := Xo.rep Xo.X Xo.s (isReduced_moduli Xo) Xo.univ
  have hid : (GlobalTheory.LevelTwist.sabMapId Xo.univ.t).φ = 𝟙 _ := GlobalTheory.LevelTwist.sabMapId_φ _
  have e1 := hu f ⟨hs, ⟨⟨m, fun a => h2 a, fun a => by
    have := h3 a
    rwa [hg a] at this⟩⟩⟩
  have e2 := hu (𝟙 _) ⟨Category.id_comp _, ⟨⟨GlobalTheory.LevelTwist.sabMapId Xo.univ.t, fun a => by
      change _ ≫ (GlobalTheory.LevelTwist.sabMapId Xo.univ.t).φ = _
      rw [hid, Category.comp_id, Category.id_comp], fun a => by
      change _ ≫ (GlobalTheory.LevelTwist.sabMapId Xo.univ.t).φ = _
      rw [hid, Category.comp_id, Category.id_comp]⟩⟩⟩
  exact e1.trans e2.symm

theorem exists_semiTwist (hpq : 1 ≤ D.p + D.q) (Xo : Moduli D l) (σ : KA l →+* KA l) (g : Sim D)
    (hρ : σ (baseKA l).ρ = (baseKA l).ρ) (hζ : σ (baseKA l).ζ = (baseKA l).ζ ^ g.ν l.A)
    (hg : ∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) :
    ∃ (f : Xo.X ⟶ Xo.X) (m : SABMap Xo.univ.t Xo.univ.t f), SemiTwist Xo f m.φ (g.f l.A) σ := by
  obtain ⟨a₀, b₀, hab⟩ := GlobalTheory.SimAlg.exists_form_eq_one hpq
  have hν : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ) := by
    intro n m hn hm
    refine ⟨GlobalTheory.SimAlg.dvd_mult_tower g hn hm hab, ?_⟩
    obtain ⟨h, hh⟩ := g.inv n hn
    obtain ⟨c, hc⟩ := GlobalTheory.SimAlg.dvd_mult_inv g hn hab h (fun x => (hh x).2)
    exact ⟨D.EF (h a₀) (h b₀), -c, by linear_combination hc⟩
  let b' : Base l (KA l) :=
    { unit := (baseKA l).unit
      ρ := (baseKA l).ρ
      ρ_sq := (baseKA l).ρ_sq
      ζ := σ (baseKA l).ζ
      ζ_prim := (baseKA l).ζ_prim.map_of_injective σ.injective }
  let o' : Obj D l b' Xo.s :=
    { t := Xo.univ.t
      proper := Xo.univ.proper
      ample := Xo.univ.ample
      ktriv := Xo.univ.ktriv
      eta := fun a => Xo.univ.eta (g.f l.M a)
      eta_add := fun a c => by simp only [map_add (f := _), Xo.univ.eta_add]
      eta_ker := fun a ha => Xo.univ.eta_ker _ (GlobalTheory.LevelTwist.map_mem_smul_top _ _ ha)
      etaA := fun a => Xo.univ.etaA (g.f l.A a)
      etaA_add := fun a c => by simp only [map_add (f := _), Xo.univ.etaA_add]
      etaA_ker := fun a => by simp only [map_nsmul, Xo.univ.etaA_ker]
      geom := fun k _ _ x β hx => by
        obtain ⟨hdet, I, hI1, hI2, hI3⟩ := Xo.univ.geom k x β hx
        refine ⟨hdet, GlobalTheory.LevelTwist.twist I g hν, ?_, fun a => ?_, fun a ha => ?_⟩
        · rw [GlobalTheory.LevelTwist.twist_ζ, Units.val_zpow_eq_zpow_val, hI1, ← map_zpow₀]
          exact congrArg β hζ.symm
        · rw [GlobalTheory.LevelTwist.twist_ev]
          exact hI2 _
        · rw [GlobalTheory.LevelTwist.twist_ev]
          exact hI3 _ (GlobalTheory.LevelTwist.map_mem_smul_top _ _ ha) }
  let o := GlobalTheory.objRestrictBase σ o' hρ rfl
  obtain ⟨f, ⟨hf, ⟨p⟩⟩, -⟩ := Xo.rep Xo.X (Xo.s ≫ spMap σ) (isReduced_moduli Xo) o
  refine ⟨f, p.toSABMap, hf, fun a => ?_, fun a => p.etaA a⟩
  have e := GlobalTheory.Moduli.LevelAction.eta_congr Xo.univ (hg a)
  have := p.eta a
  change (Xo.univ.eta (g.f l.M a)).left ≫ _ = _ at this
  rw [e] at this
  exact this

theorem exists_semiTwist_iso (hpq : 1 ≤ D.p + D.q) (l₀ : Level H) (hA : l₀.A = 1) (hM : l.M = l₀.M)
    (hMb : l.Mb = l₀.Mb) (Xo : Moduli D l) (σ : KA l ≃+* KA l) (hρ : σ (baseKA l).ρ = (baseKA l).ρ) :
    ∃ (ρ : Xo.X ≅ Xo.X) (m : SABMap Xo.univ.t Xo.univ.t ρ.hom) (g : D.La →ₗ[𝓞 E] D.La),
      SemiTwist Xo ρ.hom m.φ g σ.toRingHom := by
  obtain ⟨a₀, b₀, hab⟩ := GlobalTheory.SimAlg.exists_form_eq_one hpq
  have hA0 : NeZero l.A := ⟨l.A_pos.ne'⟩
  have hprim := (baseKA l).ζ_prim
  have hz : (baseKA l).ζ ≠ 0 := hprim.ne_zero l.A_pos.ne'
  have hcong : ∀ a b : ℤ, (l.A : ℤ) ∣ a - b → (baseKA l).ζ ^ a = (baseKA l).ζ ^ b := by
    rintro a b ⟨k, hk⟩
    rw [show a = b + l.A * k by linarith, zpow_add₀ hz, zpow_mul, zpow_natCast, hprim.pow_eq_one, one_zpow,
      _root_.mul_one]
  have hσp : IsPrimitiveRoot (σ (baseKA l).ζ) l.A := hprim.map_of_injective σ.injective
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hσp.pow_eq_one
  have hcop : i.Coprime l.A := (hprim.pow_iff_coprime l.A_pos i).1 (hi ▸ hσp)
  have hMpos : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hN : 0 < l.M * l.A := Nat.mul_pos hMpos l.A_pos
  have hN0 : NeZero (l.M * l.A) := ⟨hN.ne'⟩
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective (m := l.M * l.A) (n := l.A) (dvd_mul_left _ _)
    (ZMod.unitOfCoprime i hcop)
  obtain ⟨ν, hνdef⟩ : ∃ ν : ℤ, ν = ((v : ZMod (l.M * l.A)).val : ℤ) := ⟨_, rfl⟩
  have hνN : IsCoprime ν ((l.M * l.A : ℕ) : ℤ) := by
    rw [hνdef]
    exact Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime v)
  have hνi : (l.A : ℤ) ∣ ν - i := by
    have h2 := congrArg (fun w : (ZMod l.A)ˣ => (w : ZMod l.A)) hv
    simp only [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_eq_val] at h2
    have h3 : ((i : ℤ) : ZMod l.A) = ((ν : ℤ) : ZMod l.A) := by
      rw [hνdef]
      push_cast
      exact h2.symm
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h3
  obtain ⟨c, hcN, hcM, -⟩ := GlobalTheory.SimMult.exists_scalar H l₀ (l.M * l.A) hN
    (by rw [← hM]; exact dvd_mul_right _ _) (by rw [hA]; exact one_dvd _) ν hνN
    (by rw [hA, Nat.cast_one]; exact one_dvd _)
  let fc : D.La →ₗ[𝓞 E] D.La := c • LinearMap.id
  have hfc : ∀ a b, ((l.M * l.A : ℕ) : ℤ) ∣ D.EF (fc a) (fc b) - ν * D.EF a b := by
    intro a b
    obtain ⟨t, ht⟩ := hcN
    have hc' : H.bar c * c = (ν : 𝓞 E) + ((l.M * l.A : ℕ) : 𝓞 E) * t := by linear_combination ht
    refine ⟨D.EF a (t • b), ?_⟩
    simp only [fc, LinearMap.smul_apply, LinearMap.id_apply]
    rw [D.adj, smul_smul, hc', add_smul, mul_smul]
    simp only [map_add (f := _), Int.cast_smul_eq_zsmul, Nat.cast_smul_eq_nsmul, map_zsmul, map_nsmul, zsmul_eq_mul,
      nsmul_eq_mul]
    push_cast
    ring
  obtain ⟨g, hgl⟩ := GlobalTheory.exists_sim_lift E H D (l.M * l.A) fc ν hN hνN hfc
  have hgA : (l.A : ℤ) ∣ g.ν l.A - i := by
    have t1 := GlobalTheory.SimAlg.dvd_mult_tower g l.A_pos hMpos hab
    rw [Nat.mul_comm] at t1
    have t2 : (l.A : ℤ) ∣ g.ν (l.M * l.A) - ν :=
      (Int.natCast_dvd_natCast.2 (Nat.dvd_mul_left l.A l.M)).trans hgl.2
    have := dvd_add (dvd_add (dvd_neg.2 t1) t2) hνi
    rw [show g.ν l.A - (i : ℤ) = -(g.ν (l.M * l.A) - g.ν l.A) + (g.ν (l.M * l.A) - ν) + (ν - i) by ring]
    exact this
  have hζ : σ.toRingHom (baseKA l).ζ = (baseKA l).ζ ^ g.ν l.A := by
    show σ (baseKA l).ζ = _
    rw [← hi, ← zpow_natCast]
    exact hcong _ _ (by rw [← neg_sub]; exact dvd_neg.2 hgA)
  have hgM : ∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
    intro a
    have t1 := GlobalTheory.Moduli.LevelAction.mem_of_modN (D := D) l
      (GlobalTheory.SimAlg.modN_neg (g.tower l.M l.A hMpos l.A_pos a))
    have t2 := GlobalTheory.Moduli.LevelAction.mem_of_modN (D := D) l (GlobalTheory.SimAlg.modN_of_mul (hgl.1 a))
    have t3 : (c - 1) • a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) :=
      Submodule.smul_mem_smul (by rw [hMb]; exact hcM) Submodule.mem_top
    have := add_mem (add_mem t1 t2) t3
    convert this using 1
    simp only [fc, LinearMap.smul_apply, LinearMap.id_apply, sub_smul, one_smul]
    abel
  obtain ⟨f, m, h⟩ := exists_semiTwist hpq Xo σ.toRingHom g hρ hζ hgM
  obtain ⟨g', hg'⟩ := GlobalTheory.SimAlg.exists_inv g hab
  have hρ' : σ.symm.toRingHom (baseKA l).ρ = (baseKA l).ρ :=
    σ.injective (by rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, hρ])
  have hζ' : σ.symm.toRingHom (baseKA l).ζ = (baseKA l).ζ ^ g'.ν l.A := by
    apply σ.injective
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, map_zpow₀,
      ← RingEquiv.coe_toRingHom, ← RingEquiv.toRingHom_eq_coe, hζ, ← zpow_mul, ← zpow_one (baseKA l).ζ,
      ← zpow_mul, _root_.one_mul]
    exact hcong _ _ (by rw [← neg_sub]; exact dvd_neg.2 (hg' l.A l.A_pos).2)
  have hg'M : ∀ a, g'.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
    intro a
    have := sub_mem (GlobalTheory.Moduli.LevelAction.mem_of_modN (D := D) l ((hg' l.M hMpos).1 a).2)
      (hgM (g'.f l.M a))
    rwa [sub_sub_sub_cancel_left] at this
  obtain ⟨f', m', h'⟩ := exists_semiTwist hpq Xo σ.symm.toRingHom g' hρ' hζ' hg'M
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.Moduli.LevelAction.exists_comp_sabMap m m' (rfl : f ≫ f' = f ≫ f')
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.Moduli.LevelAction.exists_comp_sabMap m' m (rfl : f' ≫ f = f' ≫ f)
  have e₁ : f ≫ f' = 𝟙 _ := by
    refine SemiTwist.eq_id n₁ (by rw [hn₁]; exact SemiTwist.comp h h') ?_ fun a => ?_
    · exact RingHom.ext fun x => by simp
    · exact GlobalTheory.Moduli.LevelAction.etaA_congr Xo.univ ((hg' l.A l.A_pos).1 a).2
  have e₂ : f' ≫ f = 𝟙 _ := by
    refine SemiTwist.eq_id n₂ (by rw [hn₂]; exact SemiTwist.comp h' h) ?_ fun a => ?_
    · exact RingHom.ext fun x => by simp
    · exact GlobalTheory.Moduli.LevelAction.etaA_congr Xo.univ ((hg' l.A l.A_pos).1 a).1
  exact ⟨⟨f, f', e₁, e₂⟩, m, g.f l.A, h⟩

end GlobalTheory.LevQuot
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliLevelQuotientByFiniteGroup

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.LevQuot

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem over_of_fix (hL : Out.Laws) (hL2 : Out.Laws2) (hL3 : Out.Laws3) {l₀ l₁ : Level H} {X₀ : Moduli D l₀}
    {X₁ : Moduli D l₁} {r : X₁.X ⟶ X₀.X} {ν : SABMap X₁.univ.t X₀.univ.t r} (hA : l₀.A = 1)
    (hc : LevComp X₁.univ X₀.univ r ν) {f : X₁.X ⟶ X₁.X} (m : SABMap X₁.univ.t X₁.univ.t f)
    (hm : ∀ a, (X₁.univ.eta a).left ≫ m.φ = f ≫ (X₁.univ.eta a).left) (hs : (f ≫ r) ≫ X₀.s = r ≫ X₀.s) :
    f ≫ r = r ∧ m.φ ≫ ν.φ = ν.φ := by
  obtain ⟨n, hn⟩ := LevelCover.sab_comp m ν rfl
  rw [← hn]
  refine LevUniq.map_to_univ_unique hL hL2 hL3 E H D l₀ l₁ X₀ _ _ _ _ X₁.univ _ _ n ν (isReduced_moduli X₁) hs
    ⟨fun a => ?_, fun a => ?_⟩ hc
  · rw [hn, ← Category.assoc, LevelCover.sec_pow m _ _ (hm a), Category.assoc, hc.1, Category.assoc]
  · have e : X₁.univ.etaA a ^ (l₁.A / l₀.A) = X₁.univ.eta 0 ^ 0 := by
      rw [hA, Nat.div_one, pow_zero, ← Moduli.LevelAction.map_nsmul_of_add X₁.univ.etaA_add, X₁.univ.etaA_ker]
    rw [hn, Category.assoc, ← hc.2, e, ← Category.assoc, LevelCover.sec_pow m _ _ (hm 0), Category.assoc]

theorem exists_twist_of_fibre (hL : Out.Laws) (hL2 : Out.Laws2) (hL3 : Out.Laws3) (hN : ToroidalLevelCompatibility (H := H) (D := D))
    {l₀ l₁ : Level H} {X₀ : Moduli D l₀} {X₁ : Moduli D l₁} {r : X₁.X ⟶ X₀.X} {ν : SABMap X₁.univ.t X₀.univ.t r}
    {j : KA l₀ →+* KA l₁} (hd : l₀.Dvd l₁) (hM : l₁.M = l₀.M) (hMb : l₁.Mb = l₀.Mb)
    (hj : IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom j) (hr : r ≫ X₀.s = X₁.s ≫ spMap j)
    (hc : LevComp X₁.univ X₀.univ r ν) {k : Type} [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ X₁.X)
    (h₁ : y ≫ r = y' ≫ r) (h₂ : y ≫ X₁.s = y' ≫ X₁.s) :
    ∃ (ρ : X₁.X ≅ X₁.X) (m : SABMap X₁.univ.t X₁.univ.t ρ.hom) (g : D.La →ₗ[𝓞 E] D.La),
      SemiTwist X₁ ρ.hom m.φ g (RingHom.id _) ∧ y' = y ≫ ρ.hom := by
  let c := LevelExist.minCoeff l₁
  have hM' : 0 < l₁.M' := LevelExist.M'_pos l₁
  have hz : ∀ a, a ∣ l₁.M' → zeta a ∈ c.F := fun a ha => by
    rw [LevelCover.zeta_dvd hM' ha]
    exact pow_mem c.zeta_mem _
  have hle : KA l₀ ≤ c.F := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro x (rfl | rfl)
    · exact c.le (baseKA l₁).ρ.2
    · exact hz _ (hd.2.2.trans (Nat.dvd_lcm_right _ _))
  let c₀ : Coeff l₀ := ⟨c.F, c.fin, c.conj, hz _ (Nat.lcm_dvd (hd.1.trans (Nat.dvd_lcm_left _ _))
    (hd.2.2.trans (Nat.dvd_lcm_right _ _))), hle⟩
  obtain ⟨r', j', ν', hj', hr', e₁, e₂, -, hF⟩ := hN l₀ l₁ X₀ X₁ hd
  obtain rfl : j = j' := RingHom.ext fun x => Subtype.ext ((hj x).trans (hj' x).symm)
  obtain rfl : r = r' := (LevUniq.map_to_univ_unique hL hL2 hL3 E H D l₀ l₁ X₀ _ _ _ _ X₁.univ _ _ ν ν'
    (isReduced_moduli X₁) (hr.trans hr'.symm) hc ⟨e₁, e₂⟩).1
  obtain ⟨rF, a₁, a₂, -, -, -, htr⟩ := hF c₀ c rfl
  obtain ⟨β, hβ⟩ := LevCover.exists_spMap (y ≫ X₁.s)
  obtain ⟨θ, hθ⟩ : ∃ θ : c.F →+* k, θ.comp (IntermediateField.inclusion c.le).toRingHom = β := by
    letI : Algebra (KA l₁) k := β.toAlgebra
    letI : Algebra (KA l₁) c.F := (IntermediateField.inclusion c.le).toRingHom.toAlgebra
    haveI := c.fin
    haveI : IsScalarTower ℚ (KA l₁) c.F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    haveI : Algebra.IsAlgebraic (KA l₁) c.F := Algebra.IsAlgebraic.tower_top (K := ℚ) (KA l₁)
    exact ⟨(IsAlgClosed.lift (R := KA l₁) (S := c.F) (M := k)).toRingHom,
      (IsAlgClosed.lift (R := KA l₁) (S := c.F) (M := k)).comp_algebraMap⟩
  have w : y ≫ X₁.s = spMap θ ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [LevCover.spMap_comp'', hθ, hβ]
  obtain ⟨⟨g, ρ, hg, ⟨hs, m, b₁, b₂⟩, -, hy⟩, -⟩ := htr k (pullback.lift y (spMap θ) w)
    (pullback.lift y' (spMap θ) (h₂ ▸ w)) (by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, a₁, pullback.lift_fst_assoc, pullback.lift_fst_assoc, h₁]
      · rw [Category.assoc, Category.assoc, a₂, pullback.lift_snd_assoc, pullback.lift_snd_assoc])
  rw [pullback.lift_fst, pullback.lift_fst_assoc] at hy
  refine ⟨ρ, m, g.f l₁.A, ⟨by rw [hs, LevelCover.spMap_id', Category.comp_id], fun a => ?_, b₂⟩, hy⟩
  rw [← b₁, Moduli.LevelAction.eta_congr X₁.univ (x := g.f l₁.M a) (y := a) (by rw [hM, hMb]; exact hg.2.1 a)]

theorem exists_finite_invariant {l : Level H} (Xo : Moduli D l) :
    ∃ (κ : Type) (_ : Finite κ) (q : (D.La →ₗ[𝓞 E] D.La) → κ), ∀ g g', q g = q g' →
      ∀ x, Xo.univ.etaA (g x) = Xo.univ.etaA (g' x) := by
  obtain ⟨_, _⟩ := LevCover.datum_free D
  obtain ⟨κ, _, q, hq⟩ := LevCover.exists_finite_mod D.La l.A_pos
  haveI : Nonempty D.La := ⟨0⟩
  refine ⟨κ → κ, inferInstance, fun g c => q (g (Function.invFun q c)), fun g g' h x => ?_⟩
  obtain ⟨c, hc⟩ := hq _ _ (Function.invFun_eq (f := q) ⟨x, rfl⟩)
  obtain ⟨c', hc'⟩ := hq _ _ (congrFun h (q x))
  generalize Function.invFun q (q x) = y at hc hc'
  subst hc
  simp only [map_add (f := _), map_nsmul, hc', Xo.univ.etaA_add, Xo.univ.etaA_ker, _root_.mul_one]

section

variable {l₀ l₁ : Level H} {X₀ : Moduli D l₀} {X₁ : Moduli D l₁} {r : X₁.X ⟶ X₀.X}

def twistMonoid (τ : autOver r →* Aut X₁.univ.t.G.left) : Submonoid (autOver r) :=
  { carrier := {ω | ∃ (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁), σ (baseKA l₁).ρ = (baseKA l₁).ρ ∧
      SemiTwist X₁ ω.1.asIso.hom (τ ω).asIso.hom g σ.toRingHom}
    mul_mem' := by
      rintro a b ⟨g, σ, h₁, h₂⟩ ⟨g', σ', h₁', h₂'⟩
      refine ⟨g' ∘ₗ g, σ.trans σ', by rw [RingEquiv.trans_apply, h₁, h₁'], ?_⟩
      have e₁ : (a * b).1.asIso.hom = b.1.asIso.hom ≫ a.1.asIso.hom := rfl
      have e₂ : (τ (a * b)).asIso.hom = (τ b).asIso.hom ≫ (τ a).asIso.hom := by rw [map_mul]; rfl
      have e₃ : (σ.trans σ').toRingHom = σ'.toRingHom.comp σ.toRingHom := RingHom.ext fun _ => rfl
      rw [e₁, e₂, e₃, LinearMap.coe_comp]
      exact h₂'.comp h₂
    one_mem' := by
      refine ⟨LinearMap.id, RingEquiv.refl _, rfl, ?_⟩
      rw [map_one]
      exact ⟨(Category.id_comp _).trans ((Category.comp_id _).symm.trans
          (congrArg _ (LevelCover.spMap_id' _).symm)),
        fun a => (Category.comp_id _).trans (Category.id_comp _).symm,
        fun a => (Category.comp_id _).trans (Category.id_comp _).symm⟩ }

theorem inv_comp_square {X P : Scheme.{0}} (a : X ≅ X) (t : P ≅ P) {b : X ⟶ X} {u : P ⟶ P} {x y : X ⟶ P}
    (p₁ : y ≫ t.hom = a.hom ≫ x) (p₂ : y ≫ u = b ≫ x) : x ≫ t.inv ≫ u = (a.inv ≫ b) ≫ x := by
  rw [Category.assoc, ← p₂, Iso.eq_inv_comp, ← Category.assoc, ← p₁, Category.assoc, Iso.hom_inv_id_assoc]

theorem finite_twistMonoid (τ : autOver r →* Aut X₁.univ.t.G.left)
    (mu : ∀ ω : autOver r, SABMap X₁.univ.t X₁.univ.t ω.1.asIso.hom) (hmu : ∀ ω, (mu ω).φ = (τ ω).asIso.hom) :
    Finite (twistMonoid τ) := by
  obtain ⟨κ, _, q, hq⟩ := exists_finite_invariant X₁
  haveI := finite_fieldAut l₁
  have hch : ∀ ω : twistMonoid τ, ∃ (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁),
      SemiTwist X₁ ω.1.1.asIso.hom (τ ω.1).asIso.hom g σ.toRingHom := fun ω => by
    obtain ⟨g, σ, -, h⟩ := ω.2
    exact ⟨g, σ, h⟩
  choose g σ hg using hch
  refine Finite.of_injective (fun ω => (q (g ω), σ ω)) fun a b hab => ?_
  have h₁ := hq _ _ (congrArg Prod.fst hab)
  have h₂ : σ a = σ b := congrArg Prod.snd hab
  have e₀ : (b.1 * a.1⁻¹).1.asIso.hom = a.1.1.asIso.inv ≫ b.1.1.asIso.hom := rfl
  have e₁ : (τ (b.1 * a.1⁻¹)).asIso.hom = (τ a.1).asIso.inv ≫ (τ b.1).asIso.hom := by rw [map_mul, map_inv]; rfl
  have key : ∀ {x y : X₁.X ⟶ X₁.univ.t.G.left}, y ≫ (τ a.1).asIso.hom = a.1.1.asIso.hom ≫ x →
      y ≫ (τ b.1).asIso.hom = b.1.1.asIso.hom ≫ x → x ≫ (mu (b.1 * a.1⁻¹)).φ = (b.1 * a.1⁻¹).1.asIso.hom ≫ x := by
    intro x y p₁ p₂
    rw [hmu, e₀, e₁]
    exact inv_comp_square a.1.1.asIso (τ a.1).asIso p₁ p₂
  have hid : (b.1 * a.1⁻¹).1.asIso.hom = 𝟙 _ :=
    SemiTwist.eq_id (g := id) (σ := RingHom.id _) (mu (b.1 * a.1⁻¹)) ⟨by
      rw [e₀, Category.assoc, (hg b).1, ← h₂, ← (hg a).1, LevelCover.spMap_id', Category.comp_id]
      exact Iso.inv_hom_id_assoc a.1.1.asIso _,
      fun x => key ((hg a).2.1 x) ((hg b).2.1 x),
      fun x => key ((hg a).2.2 x) (h₁ x ▸ (hg b).2.2 x)⟩ rfl fun _ => rfl
  have : b.1 * a.1⁻¹ = 1 := Subtype.ext (Aut.ext (Iso.ext hid))
  exact Subtype.ext (mul_inv_eq_one.1 this).symm

theorem exists_mem_twistMonoid (hL : Out.Laws) (hL2 : Out.Laws2) (hL3 : Out.Laws3)
    {ν : SABMap X₁.univ.t X₀.univ.t r} {k : KA l₀ →+* KA l₁} (hA : l₀.A = 1)
    (hk : IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k) (hr : r ≫ X₀.s = X₁.s ≫ spMap k)
    (hc : LevComp X₁.univ X₀.univ r ν) (τ : autOver r →* Aut X₁.univ.t.G.left)
    (hτ : ∀ ω, (τ ω).asIso.hom ≫ ν.φ = ν.φ ∧ (τ ω).asIso.hom ≫ X₁.univ.t.G.hom = X₁.univ.t.G.hom ≫ ω.1.asIso.hom)
    (ρ : X₁.X ≅ X₁.X) (m : SABMap X₁.univ.t X₁.univ.t ρ.hom) (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁)
    (h₁ : σ (baseKA l₁).ρ = (baseKA l₁).ρ) (h₂ : SemiTwist X₁ ρ.hom m.φ g σ.toRingHom) :
    ∃ ω ∈ twistMonoid τ, ω.1.asIso.hom = ρ.hom := by
  have hkρ : k (baseKA l₀).ρ = (baseKA l₁).ρ := Subtype.ext (hk _)
  have hz : (baseKA l₀).ζ = 1 := by
    have := (baseKA l₀).ζ_prim.pow_eq_one
    rwa [hA, pow_one] at this
  have hσ : σ.toRingHom.comp k = k := field_hom_ext l₀ _ _ (by rw [RingHom.comp_apply, hkρ]; exact h₁)
    (by rw [hz, map_one, map_one])
  obtain ⟨o₁, o₂⟩ := over_of_fix hL hL2 hL3 hA hc m h₂.2.1 (by
    rw [Category.assoc, hr, ← Category.assoc, h₂.1, Category.assoc, LevCover.spMap_comp'', hσ])
  have e : m.φ = (τ ⟨Aut.of ρ, o₁⟩).asIso.hom :=
    ν.cart.1.hom_ext (o₂.trans (hτ _).1.symm) (m.cart.1.w.trans (hτ ⟨Aut.of ρ, o₁⟩).2.symm)
  exact ⟨⟨Aut.of ρ, o₁⟩, ⟨g, σ, h₁, e ▸ h₂⟩, rfl⟩

end

theorem exists_level_quotient : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₁ : Level H) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (k : KA l₀ →+* KA l₁), l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k → r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k → LevComp (Xo l₁).univ (Xo l₀).univ r ν → ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (ρ : Γ →* Aut (Xo l₁).X) (τ : Γ →* Aut (Xo l₁).univ.t.G.left) (mu : ∀ g, SABMap (Xo l₁).univ.t (Xo l₁).univ.t (ρ g).asIso.hom), Function.Injective ρ ∧ (IsAffineHom r ∧ (∀ g, (ρ g).asIso.hom ≫ r = r) ∧ ∀ V : (Xo l₀).X.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ((Xo l₁).X, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) ∧ ∀ ω, (mu ω).φ = (τ ω).asIso.hom ∧ (τ ω).asIso.hom ≫ ν.φ = ν.φ ∧ (∀ x, ((Xo l₁).univ.eta x).left ≫ (τ ω).asIso.hom = (ρ ω).asIso.hom ≫ ((Xo l₁).univ.eta x).left) ∧ ∃ (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁), σ (baseKA l₁).ρ = (baseKA l₁).ρ ∧ (ρ ω).asIso.hom ≫ (Xo l₁).s = (Xo l₁).s ≫ spMap σ.toRingHom ∧ ∀ x, ((Xo l₁).univ.etaA (g x)).left ≫ (τ ω).asIso.hom = (ρ ω).asIso.hom ≫ ((Xo l₁).univ.etaA x).left := by
  intro hL hL2 hL3 E _ _ _ H D Xo hpq hN l₀ l₁ r ν k hA hM hMb hk hr hc
  have hd : l₀.Dvd l₁ := ⟨hM ▸ dvd_rfl, hMb.le, hA ▸ one_dvd _⟩
  obtain ⟨hfin, het, hsur⟩ : IsFinite r ∧ Etale r ∧ Surjective r := by
    obtain ⟨k', r', ν', hr', hk', hc', -, -, -, h⟩ := LevelMap.exists_levelMap E H D Xo hN l₀ l₁ hd
    obtain rfl : k = k' := RingHom.ext fun x => Subtype.ext ((hk x).trans (hk' x).symm)
    obtain rfl : r = r' := (LevUniq.map_to_univ_unique hL hL2 hL3 E H D l₀ l₁ _ _ _ _ _ (Xo l₁).univ _ _ ν ν'
      (isReduced_moduli _) (hr.trans hr'.symm) hc hc').1
    exact h
  obtain ⟨τ, hτ⟩ := exists_liftAut ν.cart.1
  have hmu : ∀ ω : autOver r, ∃ m : SABMap (Xo l₁).univ.t (Xo l₁).univ.t ω.1.asIso.hom, m.φ = (τ ω).asIso.hom := fun ω => by
    obtain ⟨m, hm⟩ := LevelCover.sab_cancel ν ν ω.1.asIso.hom ω.2
    exact ⟨m, ν.cart.1.hom_ext (hm.trans (hτ ω).1.symm) (m.cart.1.w.trans (hτ ω).2.symm)⟩
  choose mu hmu using hmu
  let S := twistMonoid τ
  have hS := exists_mem_twistMonoid hL hL2 hL3 hA hk hr hc τ hτ
  haveI : Finite S := finite_twistMonoid τ mu hmu
  obtain ⟨T, hT⟩ := exists_subgroup_of_finite S
  refine ⟨T, inferInstance, Finite.of_injective (fun t : T => (⟨t.1, (hT _).1 t.2⟩ : S))
      fun a b h => Subtype.ext (congrArg (fun s : S => s.1) h),
    (autOver r).subtype.comp T.subtype, τ.comp T.subtype, fun t => mu t.1,
    Subtype.val_injective.comp Subtype.val_injective, ⟨inferInstance, fun t => t.1.2, ?_⟩, fun t => ?_⟩
  · refine invariant_descends r (fun t : T => t.1.1.asIso.hom) (fun t => t.1.2) fun F _ _ y y' hy => ?_
    obtain ⟨β, hβ⟩ := LevCover.exists_spMap (y ≫ (Xo l₁).s)
    obtain ⟨β', hβ'⟩ := LevCover.exists_spMap (y' ≫ (Xo l₁).s)
    have hkρ : k (baseKA l₀).ρ = (baseKA l₁).ρ := Subtype.ext (hk _)
    have hb : β.comp k = β'.comp k := LevCover.spMap_inj' (by
      rw [← LevCover.spMap_comp'', ← LevCover.spMap_comp'', ← hβ, ← hβ', Category.assoc, Category.assoc, ← hr,
        ← Category.assoc, hy, Category.assoc])
    obtain ⟨σ, h₁, h₂⟩ := exists_fieldAut l₁ β β' (hkρ ▸ DFunLike.congr_fun hb (baseKA l₀).ρ)
    obtain ⟨ρ, m, g, h₃⟩ := exists_semiTwist_iso hpq l₀ hA hM hMb (Xo l₁) σ h₁
    obtain ⟨a, ha, ea⟩ := hS ρ m g σ h₁ h₃
    obtain ⟨ρ', m', g', h₄, h₅⟩ := exists_twist_of_fibre hL hL2 hL3 hN hd hM hMb hk hr hc (y ≫ ρ.hom) y'
      (by rw [Category.assoc, ← ea, show a.1.asIso.hom ≫ r = r from a.2, hy])
      (by rw [Category.assoc, h₃.1, ← Category.assoc, hβ, hβ', LevCover.spMap_comp'', h₂])
    obtain ⟨b, hb', eb⟩ := hS ρ' m' g' (RingEquiv.refl _) rfl h₄
    refine ⟨⟨b * a, (hT _).2 (S.mul_mem hb' ha)⟩, ?_⟩
    rw [h₅, Category.assoc, ← ea, ← eb]
    rfl
  · obtain ⟨g, σ, h₁, h₂⟩ := (hT _).1 t.2
    exact ⟨hmu _, (hτ _).1, h₂.2.1, g, σ, h₁, h₂.1, h₂.2.2⟩

end GlobalTheory.LevQuot
end
end
end
