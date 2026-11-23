module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Mathlib.RingTheory.Localization.AtPrime.Basic
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
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.OreLocalization.Ring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackSpreadsToIntermediateSubringStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsetMemRangeLocalizationAwayOfDvd

section

@[expose] public section

namespace GlobalTheory

theorem finset_mem_range_of_away_dvd (R : Type) [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime]
    (F : Finset (Localization.AtPrime 𝔭)) :
    ∃ s ∉ 𝔭, ∀ (c : R), s ∣ c → ∀ κ : Localization.Away c →+* Localization.AtPrime 𝔭,
      κ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.AtPrime 𝔭) →
        ∀ x ∈ F, x ∈ κ.range := by
  classical
  choose p hp using fun x : Localization.AtPrime 𝔭 =>
    IsLocalization.mk'_surjective 𝔭.primeCompl x
  let sx : Localization.AtPrime 𝔭 → 𝔭.primeCompl := fun x => (p x).2
  refine ⟨((∏ x ∈ F, sx x : 𝔭.primeCompl) : R), (∏ x ∈ F, sx x).2, ?_⟩
  intro c hc κ hκ x hx
  have hdvd : ((sx x : 𝔭.primeCompl) : R) ∣ c := by
    refine dvd_trans ?_ hc
    rw [Submonoid.coe_finsetProd]
    exact Finset.dvd_prod_of_mem (fun y => ((sx y : 𝔭.primeCompl) : R)) hx
  obtain ⟨m, hm⟩ := hdvd
  have hκa : ∀ r : R, κ (algebraMap R (Localization.Away c) r) =
      algebraMap R (Localization.AtPrime 𝔭) r := fun r => by
    rw [← RingHom.comp_apply, hκ]
  refine ⟨algebraMap R _ (p x).1 * algebraMap R _ m * IsLocalization.Away.invSelf c, ?_⟩
  have hinv : algebraMap R (Localization.AtPrime 𝔭) c *
      κ (IsLocalization.Away.invSelf (S := Localization.Away c) c) = 1 := by
    rw [← hκa, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  refine (?_ : _ = IsLocalization.mk' (Localization.AtPrime 𝔭) (p x).1 (p x).2).trans (hp x)
  rw [IsLocalization.eq_mk'_iff_mul_eq, map_mul, map_mul, hκa, hκa]
  calc algebraMap R (Localization.AtPrime 𝔭) (p x).1 * algebraMap R _ m *
        κ (IsLocalization.Away.invSelf c) * algebraMap R _ ((p x).2 : R)
      = algebraMap R (Localization.AtPrime 𝔭) (p x).1 *
        (algebraMap R _ (((p x).2 : R) * m) * κ (IsLocalization.Away.invSelf c)) := by
        rw [map_mul]; ring
    _ = algebraMap R (Localization.AtPrime 𝔭) (p x).1 := by
        rw [← hm, hinv, mul_one]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsetMemRangeLocalizationAwayOfDvdStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.finset_mem_range_localization_away_of_dvd : ∀ (R : Type) [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime] (F : Finset (Localization.AtPrime 𝔭)), ∃ s ∉ 𝔭, ∀ (c : R), s ∣ c → ∀ κ : Localization.Away c →+* Localization.AtPrime 𝔭, κ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.AtPrime 𝔭) → ∀ x ∈ F, x ∈ κ.range := by
  first | exact @GlobalTheory.finset_mem_range_of_away_dvd | exact GlobalTheory.finset_mem_range_of_away_dvd | (intros; apply GlobalTheory.finset_mem_range_of_away_dvd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayInjectiveAtPrimeOfDvd

section

@[expose] public section

namespace GlobalTheory

theorem localization_away_injective_of_dvd (R : Type) [CommRing R] [IsNoetherianRing R] (𝔭 : Ideal R) [𝔭.IsPrime] :
    ∃ t ∉ 𝔭, ∀ (c : R), t ∣ c → ∀ κ : Localization.Away c →+* Localization.AtPrime 𝔭,
      κ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.AtPrime 𝔭) →
      Function.Injective κ := by
  classical
  set I : Ideal R := RingHom.ker (algebraMap R (Localization.AtPrime 𝔭)) with hI
  obtain ⟨s, hs⟩ : I.FG := IsNoetherian.noetherian I
  have key : ∀ s : Finset R, (∀ x ∈ s, algebraMap R (Localization.AtPrime 𝔭) x = 0) →
      ∃ t ∉ 𝔭, ∀ x ∈ s, t * x = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, fun h => ‹𝔭.IsPrime›.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
    | insert a s ha ih =>
      intro h
      obtain ⟨t, ht, hts⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
      obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff 𝔭.primeCompl (Localization.AtPrime 𝔭) a).mp
        (h a (Finset.mem_insert_self a s))
      refine ⟨(m : R) * t, 𝔭.primeCompl.mul_mem m.2 ht, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [mul_comm (m : R) t, mul_assoc, hm, mul_zero]
      · rw [mul_assoc, hts x hx, mul_zero]
  obtain ⟨t, ht, hts⟩ := key s (fun x hx => by
    have : x ∈ I := hs ▸ Submodule.subset_span hx
    simpa [hI] using this)
  have hker : ∀ x ∈ I, t * x = 0 := by
    have hle : I ≤ LinearMap.ker (LinearMap.mulLeft R t) := by
      rw [← hs, Submodule.span_le]
      intro x hx
      simp [hts x hx]
    intro x hx
    simpa using hle hx
  refine ⟨t, ht, ?_⟩
  intro c ⟨d, hd⟩ κ hκ
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers c) x
  have hspec := IsLocalization.mk'_spec (Localization.Away c) a m
  have h1 : algebraMap R (Localization.AtPrime 𝔭) a = 0 := by
    have := congrArg κ hspec
    rw [map_mul, hx, zero_mul] at this
    rw [← hκ, RingHom.comp_apply, ← this]
  have hta : t * a = 0 := hker a (by simpa [hI] using h1)
  have hu : IsUnit (algebraMap R (Localization.Away c) t) := by
    have hc := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away c) c
    have hc' : IsUnit (algebraMap R (Localization.Away c) t * algebraMap R (Localization.Away c) d) := by
      rw [← map_mul, ← hd]; exact hc
    exact isUnit_of_mul_isUnit_left hc'
  have ha : algebraMap R (Localization.Away c) a = 0 := by
    have : algebraMap R (Localization.Away c) t * algebraMap R (Localization.Away c) a = 0 := by
      rw [← map_mul, hta, map_zero]
    exact (hu.mul_right_eq_zero).mp this
  show IsLocalization.mk' (Localization.Away c) a m = 0
  rw [IsLocalization.mk'_eq_mul_mk'_one, ha, zero_mul]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayInjectiveAtPrimeOfDvdStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.localization_away_injective_atPrime_of_dvd : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (𝔭 : Ideal R) [𝔭.IsPrime], ∃ t ∉ 𝔭, ∀ (c : R), t ∣ c → ∀ κ : Localization.Away c →+* Localization.AtPrime 𝔭, κ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.AtPrime 𝔭) → Function.Injective κ := by
  first | exact @GlobalTheory.localization_away_injective_of_dvd | exact GlobalTheory.localization_away_injective_of_dvd | (intros; apply GlobalTheory.localization_away_injective_of_dvd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayRangeLeOfDvdOfComp

section

@[expose] public section

namespace GlobalTheory

theorem away_range_le_of_dvd (R : Type) [CommRing R] (P : Type) [CommRing P] (g : R →+* P) (c c' : R)
    (hcc : c ∣ c') (κ : Localization.Away c →+* P) (κ' : Localization.Away c' →+* P)
    (hκ : κ.comp (algebraMap R (Localization.Away c)) = g)
    (hκ' : κ'.comp (algebraMap R (Localization.Away c')) = g) : κ.range ≤ κ'.range := by
  have hu : IsUnit (algebraMap R (Localization.Away c') c) :=
    isUnit_of_dvd_unit (map_dvd _ hcc) (IsLocalization.Away.algebraMap_isUnit c')
  let φ : Localization.Away c →+* Localization.Away c' := IsLocalization.Away.lift c hu
  have hφ : (κ'.comp φ) = κ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers c)
    rw [hκ, RingHom.comp_assoc]
    have : φ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.Away c') :=
      IsLocalization.Away.lift_comp c hu
    rw [this, hκ']
  rintro y ⟨x, rfl⟩
  exact ⟨φ x, by rw [← hφ]; rfl⟩

theorem away_range_le_of_dvd' : ∀ (R : Type) [CommRing R] (P : Type) [CommRing P] (g : R →+* P) (c c' : R), c ∣ c' → ∀ (κ : Localization.Away c →+* P) (κ' : Localization.Away c' →+* P), κ.comp (algebraMap R (Localization.Away c)) = g → κ'.comp (algebraMap R (Localization.Away c')) = g → κ.range ≤ κ'.range :=
  fun R _ P _ g c c' h κ κ' hκ hκ' => away_range_le_of_dvd R P g c c' h κ κ' hκ hκ'

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayRangeLeOfDvdOfCompStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.localization_away_range_le_of_dvd_of_comp : ∀ (R : Type) [CommRing R] (P : Type) [CommRing P] (g : R →+* P) (c c' : R), c ∣ c' → ∀ (κ : Localization.Away c →+* P) (κ' : Localization.Away c' →+* P), κ.comp (algebraMap R (Localization.Away c)) = g → κ'.comp (algebraMap R (Localization.Away c')) = g → κ.range ≤ κ'.range := by
  first | exact @GlobalTheory.away_range_le_of_dvd' | exact GlobalTheory.away_range_le_of_dvd' | (intros; apply GlobalTheory.away_range_le_of_dvd' <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadOfPullbacks

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelSpreadLocal

theorem exists_spread_of_pullbacks : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (d : SiegPre g n ζ (spMap β)) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) [LocallyOfFinitePresentation sY] (u : SiegPre g n ζ sY) (r₀ : R) (ι₀ : Localization.Away r₀ →+* Localization.AtPrime 𝔭) (h : Sp (Localization.Away r₀) ⟶ Y) (e : SiegPre g n ζ (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β))), r₀ ∉ 𝔭 → ι₀.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.AtPrime 𝔭) → h ≫ sY = spMap ((algebraMap R (Localization.Away r₀)).comp β) → SiegPB e d (spMap (algebraMap R (Localization.AtPrime 𝔭))) → SiegPB e u (spMap ι₀ ≫ h) → ∃ r ∉ 𝔭, ∃ (κ : Localization.Away r₀ →+* Localization.Away r) (d' : SiegPre g n ζ (spMap ((algebraMap R (Localization.Away r)).comp β))), κ.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.Away r) ∧ SiegPB d' d (spMap (algebraMap R (Localization.Away r))) ∧ SiegPB d' u (spMap κ ≫ h) := by
  intro g n B _ ζ R _ _ β 𝔭 _ d Y sY _ u r₀ ι₀ h e hr₀ hι₀ hh hed heu
  obtain ⟨t₁, ht₁, hinj⟩ := GlobalTheory.T.localization_away_injective_atPrime_of_dvd R 𝔭
  have hrange := GlobalTheory.T.finset_mem_range_localization_away_of_dvd R 𝔭
  have hmono := GlobalTheory.T.localization_away_range_le_of_dvd_of_comp R (Localization.AtPrime 𝔭) (algebraMap R (Localization.AtPrime 𝔭))
  have spc : ∀ {A₁ A₂ A₃ : Type} [CommRing A₁] [CommRing A₂] [CommRing A₃] (a : A₁ →+* A₂) (b : A₂ →+* A₃),
      spMap (b.comp a) = spMap b ≫ spMap a := by
    intro A₁ A₂ A₃ _ _ _ a b
    simp only [spMap, ← Spec.map_comp]
    rfl
  have unit : ∀ x : R, x ∉ 𝔭 → IsUnit (algebraMap R (Localization.AtPrime 𝔭) x) := fun x hx =>
    IsLocalization.map_units (M := 𝔭.primeCompl) (Localization.AtPrime 𝔭) ⟨x, hx⟩
  have nmul : ∀ x y : R, x ∉ 𝔭 → y ∉ 𝔭 → x * y ∉ 𝔭 := fun x y hx hy hm =>
    ((inferInstance : 𝔭.IsPrime).mem_or_mem hm).elim hx hy
  let lam : ∀ c : R, c ∉ 𝔭 → Localization.Away c →+* Localization.AtPrime 𝔭 := fun c hc =>
    IsLocalization.Away.lift c (unit c hc)
  have lamc : ∀ (c : R) (hc : c ∉ 𝔭), (lam c hc).comp (algebraMap R (Localization.Away c)) =
      algebraMap R (Localization.AtPrime 𝔭) := fun c hc => IsLocalization.Away.lift_comp _ _

  have ht : r₀ * t₁ ∉ 𝔭 := nmul _ _ hr₀ ht₁
  let R₀ : Subring (Localization.AtPrime 𝔭) := (lam _ ht).range
  have memR₀ : ∀ x : R, algebraMap R (Localization.AtPrime 𝔭) x ∈ R₀ := fun x =>
    ⟨algebraMap R _ x, by rw [← RingHom.comp_apply, lamc _ ht]⟩
  let a₀ : R →+* R₀ := (algebraMap R (Localization.AtPrime 𝔭)).codRestrict R₀ memR₀
  obtain ⟨⟨d₀, hd₀⟩, -⟩ := GlobalTheory.siegPre_pullback g n B ζ (Sp R) (Sp R₀) (spMap β) (spMap a₀ ≫ spMap β)
    (spMap a₀) d rfl
  have hsub : R₀.subtype.comp a₀ = algebraMap R (Localization.AtPrime 𝔭) := RingHom.ext fun _ => rfl
  have hed₀ : SiegPB e d₀ (spMap R₀.subtype) :=
    GlobalTheory.SiegelPullComp.pb_cancel hd₀ (by rw [← spc, hsub]; exact hed)
  have memι₀ : ∀ x, ι₀ x ∈ R₀ := fun x =>
    hmono r₀ (r₀ * t₁) (dvd_mul_right _ _) ι₀ (lam _ ht) hι₀ (lamc _ ht) ⟨x, rfl⟩
  let j₀ : Localization.Away r₀ →+* R₀ := ι₀.codRestrict R₀ memι₀
  have hj₀ : R₀.subtype.comp j₀ = ι₀ := RingHom.ext fun _ => rfl
  have heu₀ : SiegPB e u (spMap R₀.subtype ≫ (spMap j₀ ≫ h)) := by
    rw [← Category.assoc, ← spc, hj₀]; exact heu
  obtain ⟨F, hF⟩ := GlobalTheory.T.siegelPullback_spreads_to_intermediate_subring g n B ζ (Localization.AtPrime 𝔭) R₀ _ d₀ Y sY u (spMap j₀ ≫ h) _ e hed₀ heu₀
  obtain ⟨s, hs, hsF⟩ := hrange F

  have hr : r₀ * t₁ * s ∉ 𝔭 := nmul _ _ ht hs
  let lr := lam _ hr
  let R₁ : Subring (Localization.AtPrime 𝔭) := lr.range
  have hle : R₀ ≤ R₁ := hmono _ _ (dvd_mul_right _ _) _ _ (lamc _ ht) (lamc _ hr)
  have hFR : (F : Set (Localization.AtPrime 𝔭)) ⊆ R₁ := fun x hx =>
    hsF _ (dvd_mul_left _ _) lr (lamc _ hr) x hx
  have hlinj : Function.Injective lr :=
    hinj _ ⟨r₀ * s, by ring⟩ lr (lamc _ hr)
  let er : Localization.Away (r₀ * t₁ * s) ≃+* R₁ :=
    RingEquiv.ofBijective lr.rangeRestrict ⟨fun x y hxy => hlinj (congrArg Subtype.val hxy), lr.rangeRestrict_surjective⟩
  have erv : ∀ x, (er x : Localization.AtPrime 𝔭) = lr x := fun _ => rfl
  obtain ⟨⟨d', hd'⟩, -⟩ := GlobalTheory.siegPre_pullback g n B ζ (Sp R) (Sp (Localization.Away (r₀ * t₁ * s)))
    (spMap β) (spMap ((algebraMap R (Localization.Away (r₀ * t₁ * s))).comp β))
    (spMap (algebraMap R (Localization.Away (r₀ * t₁ * s)))) d (spc _ _).symm
  obtain ⟨⟨d₁, hd₁⟩, -⟩ := GlobalTheory.siegPre_pullback g n B ζ _ (Sp R₁) _ _ (spMap er.toRingHom) d' rfl
  have hd₁₀ : SiegPB d₁ d₀ (spMap (Subring.inclusion hle)) := by
    refine GlobalTheory.SiegelPullComp.pb_cancel hd₀ ?_
    have e₁ : spMap (Subring.inclusion hle) ≫ spMap a₀ = spMap er.toRingHom ≫ spMap (algebraMap R (Localization.Away (r₀ * t₁ * s))) := by
      rw [← spc, ← spc]
      congr 1
      refine RingHom.ext fun x => Subtype.ext ?_
      show algebraMap R (Localization.AtPrime 𝔭) x = lr (algebraMap R _ x)
      rw [← RingHom.comp_apply, lamc _ hr]
    rw [e₁]
    exact GlobalTheory.SiegelPullComp.pb_comp hd' hd₁
  have hd₁u := hF R₁ hle hFR _ d₁ hd₁₀
  have hd'd₁ : SiegPB d' d₁ (spMap er.symm.toRingHom) := by
    refine GlobalTheory.SiegelPullComp.pb_cancel hd₁ ?_
    have e₂ : spMap er.symm.toRingHom ≫ spMap er.toRingHom = 𝟙 _ := by
      rw [← spc]
      have : er.symm.toRingHom.comp er.toRingHom = RingHom.id _ := RingHom.ext fun x => er.symm_apply_apply x
      rw [this]
      simp [spMap]
    rw [e₂]
    exact GlobalTheory.SiegelPullComp.pb_id d'
  let κ : Localization.Away r₀ →+* Localization.Away (r₀ * t₁ * s) :=
    er.symm.toRingHom.comp ((Subring.inclusion hle).comp j₀)
  refine ⟨r₀ * t₁ * s, hr, κ, d', ?_, hd', ?_⟩
  · refine RingHom.ext fun x => hlinj ?_
    rw [RingHom.comp_apply, RingHom.comp_apply]
    have hk : er (κ (algebraMap R _ x)) = (Subring.inclusion hle) (j₀ (algebraMap R _ x)) := er.apply_symm_apply _
    calc lr (κ (algebraMap R _ x)) = (er (κ (algebraMap R _ x)) : Localization.AtPrime 𝔭) := rfl
      _ = ((Subring.inclusion hle) (j₀ (algebraMap R _ x)) : Localization.AtPrime 𝔭) := congrArg Subtype.val hk
      _ = ι₀ (algebraMap R _ x) := rfl
      _ = algebraMap R (Localization.AtPrime 𝔭) x := by rw [← RingHom.comp_apply, hι₀]
      _ = lr (algebraMap R _ x) := by rw [← RingHom.comp_apply, lamc _ hr]
  · have e₃ : spMap κ ≫ h = spMap er.symm.toRingHom ≫ (spMap (Subring.inclusion hle) ≫ (spMap j₀ ≫ h)) := by
      simp only [κ, spc, Category.assoc]
    rw [e₃]
    exact GlobalTheory.SiegelPullComp.pb_comp hd₁u hd'd₁

end GlobalTheory.SiegelSpreadLocal
end
end
