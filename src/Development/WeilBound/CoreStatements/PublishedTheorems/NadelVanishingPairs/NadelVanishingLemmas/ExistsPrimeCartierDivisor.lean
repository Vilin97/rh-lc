module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierDivisorMultCharacterize
public import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.HeightOnePrimePrincipalLocal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Mathlib.AlgebraicGeometry.OrderOfVanishing.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOnePointMinimalPrime

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

theorem GlobalTheory.primeIdealOf_minimal_of_coheight_eq_one : ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) (z : X) (hz : z ∈ U), Order.coheight z = 1 → (hU.primeIdealOf ⟨z, hz⟩).asIdeal ≠ ⊥ ∧ ∀ Q : Ideal Γ(X, U), Q.IsPrime → Q ≠ ⊥ → Q ≤ (hU.primeIdealOf ⟨z, hz⟩).asIdeal → Q = (hU.primeIdealOf ⟨z, hz⟩).asIdeal := by
  intro X _ U hU z hz h
  haveI : Nonempty U := ⟨⟨z, hz⟩⟩
  letI := X.presheaf.algebra_section_stalk (⟨z, hz⟩ : U)
  haveI := hU.isLocalization_stalk ⟨z, hz⟩
  have hc : (hU.primeIdealOf ⟨z, hz⟩).asIdeal.height = 1 := by
    have := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf ⟨z, hz⟩).asIdeal
      (X.presheaf.stalk z)
    rw [ringKrullDim_stalk_eq_coheight, h] at this
    exact_mod_cast this.symm
  refine ⟨fun e => ?_, fun Q hQ hQ0 hQP => ?_⟩
  · rw [e, Ideal.height_bot] at hc
    exact zero_ne_one hc
  · by_contra hne
    haveI : (⊥ : Ideal Γ(X, U)).IsPrime := Ideal.isPrime_bot
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.2 hQ0)
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hQP hne)
    rw [Ideal.height_bot, zero_add] at h1
    rw [hc] at h2
    have h4 : (1 : ℕ∞) + 1 ≤ Q.height + 1 := by gcongr
    have h3 : (1 : ℕ∞) + 1 ≤ 1 := h4.trans h2
    exact absurd h3 (by decide)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CodimOnePointMinimalPrime

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.codim_one_point_minimal_prime : ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) (z : X) (hz : z ∈ U), Order.coheight z = 1 → (hU.primeIdealOf ⟨z, hz⟩).asIdeal ≠ ⊥ ∧ ∀ Q : Ideal Γ(X, U), Q.IsPrime → Q ≠ ⊥ → Q ≤ (hU.primeIdealOf ⟨z, hz⟩).asIdeal → Q = (hU.primeIdealOf ⟨z, hz⟩).asIdeal := by
  first | exact @_root_.GlobalTheory.primeIdealOf_minimal_of_coheight_eq_one | exact _root_.GlobalTheory.primeIdealOf_minimal_of_coheight_eq_one | (intros; apply _root_.GlobalTheory.primeIdealOf_minimal_of_coheight_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderAtCodimOneEqOne

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Cartier

theorem ord_fnOf_eq_one_of_generates (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    (hU : IsAffineOpen U) (z : X) (hz : z ∈ U) (a t : Γ(X, U)) (h1 : Order.coheight z = 1)
    (ha : a ≠ 0) (haP : a ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal)
    (ht : t ∉ (hU.primeIdealOf ⟨z, hz⟩).asIdeal)
    (hg : ∀ g ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal, ∃ r, t * g = a * r) :
    Scheme.ord (fnOf U (gen_mem hz) a) z = 1 := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨z, hz⟩ : U)
  haveI := hU.isLocalization_stalk ⟨z, hz⟩
  set P := (hU.primeIdealOf ⟨z, hz⟩).asIdeal with hP
  have halg : ∀ b : Γ(X, U), algebraMap Γ(X, U) (X.presheaf.stalk z) b = X.presheaf.germ U z hz b :=
    fun b => rfl
  have hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk z) =
      Ideal.span {X.presheaf.germ U z hz a} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P (X.presheaf.stalk z)]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro g hgP
      obtain ⟨r, hr⟩ := hg g hgP
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      obtain ⟨u, hu⟩ := (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk z) P t).2 ht
      refine ⟨algebraMap Γ(X, U) (X.presheaf.stalk z) r * ↑u⁻¹, ?_⟩
      have e := congrArg (algebraMap Γ(X, U) (X.presheaf.stalk z)) hr
      rw [map_mul, map_mul, ← hu] at e
      rw [← halg]
      calc algebraMap Γ(X, U) (X.presheaf.stalk z) g
          = ↑u⁻¹ * (↑u * algebraMap Γ(X, U) (X.presheaf.stalk z) g) := by simp
        _ = _ := by rw [e]; ring
    · rw [Ideal.span_le, Set.singleton_subset_iff, ← halg]
      exact Ideal.mem_map_of_mem _ haP
  have hne : X.presheaf.germ U z hz a ≠ 0 := fun h0 =>
    ha (fnOf_injective U (gen_mem hz) (by rw [← algebraMap_germ hz, h0, map_zero, map_zero]))
  rw [← algebraMap_germ hz a, ord_algebraMap h1 hne, ← hmax]
  haveI := (isSimpleModule_iff_isCoatom.2
    (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk z)).out :
      IsSimpleModule _ (X.presheaf.stalk z ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk z)))
  simp [Module.length_eq_one]

end GlobalTheory.Cartier
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.OrderAtCodimOneEqOne

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.order_at_codim_one_eq_one : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen U) (z : X) (hz : z ∈ U) (a t : Γ(X, U)), Order.coheight z = 1 → a ≠ 0 → a ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal → t ∉ (hU.primeIdealOf ⟨z, hz⟩).asIdeal → (∀ g ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal, ∃ r, t * g = a * r) → Scheme.ord (fnOf U (gen_mem hz) a) z = 1 := by
  first | exact @_root_.GlobalTheory.Cartier.ord_fnOf_eq_one_of_generates | exact _root_.GlobalTheory.Cartier.ord_fnOf_eq_one_of_generates | (intros; apply _root_.GlobalTheory.Cartier.ord_fnOf_eq_one_of_generates <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderOffCodimOneEqZero

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

theorem GlobalTheory.Cartier.ord_fnOf_eq_zero_off_center : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen U) (z : X) (hz : z ∈ U) (a t : Γ(X, U)), Order.coheight z = 1 → (∀ g ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal, ∃ r, t * g = a * r) → ∀ (v : X) (hv : v ∈ U), v ∈ X.basicOpen t → v ≠ z → Scheme.ord (fnOf U (gen_mem hv) a) v = 0 := by
  intro X _ _ U hU z hz a t hcz hdiv v hv ht hne
  by_cases ha : v ∈ X.basicOpen a
  · exact UnitAt.ord_eq_zero ((unitAt_fnOf_iff hv _ a).2 ha)
  refine Scheme.ord_eq_zero_of_coheight_neq_one (fun hcv => ?_) _
  have key : ∀ (w : X) (hw : w ∈ U) (f : Γ(X, U)),
      w ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf ⟨w, hw⟩).asIdeal := by
    intro w hw f
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨w, hw⟩ : U)
    haveI := hU.isLocalization_stalk ⟨w, hw⟩
    rw [X.mem_basicOpen f w hw]
    exact IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk w) _ f
  have hle : (hU.primeIdealOf ⟨z, hz⟩).asIdeal ≤ (hU.primeIdealOf ⟨v, hv⟩).asIdeal := by
    intro g hg
    obtain ⟨r, hr⟩ := hdiv g hg
    have haP : a ∈ (hU.primeIdealOf ⟨v, hv⟩).asIdeal := by
      by_contra h
      exact ha ((key v hv a).2 h)
    have htP : t ∉ (hU.primeIdealOf ⟨v, hv⟩).asIdeal := (key v hv t).1 ht
    have htg : t * g ∈ (hU.primeIdealOf ⟨v, hv⟩).asIdeal := hr ▸ Ideal.mul_mem_right _ _ haP
    exact ((hU.primeIdealOf ⟨v, hv⟩).isPrime.mem_or_mem htg).resolve_left htP
  have hsp : z ⤳ v := by
    have h1 := ((PrimeSpectrum.le_iff_specializes _ _).mp hle).map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at h1
  have hvz : v ≤ z := hsp
  have hlt : v < z := lt_of_le_not_ge hvz (fun h => hne (hsp.antisymm h).eq.symm)
  have h2 := Order.coheight_add_one_le hlt
  rw [hcz, hcv] at h2
  exact absurd h2 (by norm_num)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.OrderOffCodimOneEqZero

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.order_off_codim_one_eq_zero : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen U) (z : X) (hz : z ∈ U) (a t : Γ(X, U)), Order.coheight z = 1 → (∀ g ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal, ∃ r, t * g = a * r) → ∀ (v : X) (hv : v ∈ U), v ∈ X.basicOpen t → v ≠ z → Scheme.ord (fnOf U (gen_mem hv) a) v = 0 := by
  first | exact @_root_.GlobalTheory.Cartier.ord_fnOf_eq_zero_off_center | exact _root_.GlobalTheory.Cartier.ord_fnOf_eq_zero_off_center | (intros; apply _root_.GlobalTheory.Cartier.ord_fnOf_eq_zero_off_center <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsPrimeCartierDivisor

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.PrimeDivCartier

theorem exists_local_generator (R S : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [Algebra R S] (p P : Ideal R) [p.IsPrime]
    [IsLocalization.AtPrime S p] [UniqueFactorizationMonoid S] (hP : P.IsPrime) (hPp : P ≤ p)
    (hP0 : P ≠ ⊥) (hmin : ∀ Q : Ideal R, Q.IsPrime → Q ≠ ⊥ → Q ≤ P → Q = P) :
    ∃ a ∈ P, a ≠ 0 ∧ ∃ t ∉ p, ∀ g ∈ P, ∃ r, t * g = a * r :=
  GlobalTheory.T.height_one_prime_principal_local R S p P hP hPp hP0 hmin

theorem primeIdealOf_minimal (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U)
    (z : X) (hz : z ∈ U) (h1 : Order.coheight z = 1) :
    (hU.primeIdealOf ⟨z, hz⟩).asIdeal ≠ ⊥ ∧ ∀ Q : Ideal Γ(X, U), Q.IsPrime → Q ≠ ⊥ →
      Q ≤ (hU.primeIdealOf ⟨z, hz⟩).asIdeal → Q = (hU.primeIdealOf ⟨z, hz⟩).asIdeal :=
  GlobalTheory.T.codim_one_point_minimal_prime X U hU z hz h1

theorem ord_eq_one (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    (hU : IsAffineOpen U) (z : X) (hz : z ∈ U) (a t : Γ(X, U)) (h1 : Order.coheight z = 1)
    (ha0 : a ≠ 0) (ha : a ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal)
    (ht : t ∉ (hU.primeIdealOf ⟨z, hz⟩).asIdeal)
    (hg : ∀ g ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal, ∃ r, t * g = a * r) :
    Scheme.ord (fnOf U (gen_mem hz) a) z = 1 :=
  GlobalTheory.T.order_at_codim_one_eq_one X U hU z hz a t h1 ha0 ha ht hg

theorem ord_eq_zero (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    (hU : IsAffineOpen U) (z : X) (hz : z ∈ U) (a t : Γ(X, U)) (h1 : Order.coheight z = 1)
    (hg : ∀ g ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal, ∃ r, t * g = a * r)
    (v : X) (hv : v ∈ U) (hvt : v ∈ X.basicOpen t) (hvz : v ≠ z) :
    Scheme.ord (fnOf U (gen_mem hv) a) v = 0 :=
  GlobalTheory.T.order_off_codim_one_eq_zero X U hU z hz a t h1 hg v hv hvt hvz


open Classical in
theorem exists_local_eqn (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (hu : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (z : X)
    (h1 : Order.coheight z = 1) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ π : X.functionFieldˣ, ∀ v ∈ U,
      Scheme.ord (π : X.functionField) v = if v = z then 1 else 0 := by
  classical
  by_cases hzx : z ⤳ x
  · obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
    have hzU : z ∈ U := hzx.mem_open U.isOpen hxU
    haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
    haveI := hU.isLocalization_stalk ⟨x, hxU⟩
    haveI := hu x
    have hPp : (hU.primeIdealOf ⟨z, hzU⟩).asIdeal ≤ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
      have h' : (⟨z, hzU⟩ : U) ⤳ ⟨x, hxU⟩ := Topology.IsInducing.subtypeVal.specializes_iff.1 hzx
      exact (PrimeSpectrum.le_iff_specializes _ _).2 (h'.map hU.isoSpec.hom.continuous)
    obtain ⟨hP0, hmin⟩ := primeIdealOf_minimal X U hU z hzU h1
    obtain ⟨a, haP, ha0, t, htp, hg⟩ := exists_local_generator Γ(X, U) (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal (hU.primeIdealOf ⟨z, hzU⟩).asIdeal
      (hU.primeIdealOf ⟨z, hzU⟩).2 hPp hP0 hmin
    have hf0 : fnOf U (gen_mem hxU) a ≠ 0 := fun h =>
      ha0 (fnOf_injective U (gen_mem hxU) (h.trans (map_zero _).symm))
    refine ⟨U ⊓ X.basicOpen t, ⟨hxU, ?_⟩, Units.mk0 _ hf0, fun v hv => ?_⟩
    · exact (Scheme.mem_basicOpen X t x hxU).2 ((IsLocalization.AtPrime.isUnit_to_map_iff _ _ t).2 htp)
    · simp only [Units.val_mk0]
      split_ifs with hvz
      · subst hvz
        exact ord_eq_one X U hU v hzU a t h1 ha0 haP (fun h => htp (hPp h)) hg
      · exact ord_eq_zero X U hU z hzU a t h1 hg v hv.1 hv.2 hvz
  · refine ⟨⟨(closure {z})ᶜ, isClosed_closure.isOpen_compl⟩, ?_, 1, fun v hv => ?_⟩
    · exact fun h => hzx (specializes_iff_mem_closure.2 h)
    · have hvz : v ≠ z := fun e => hv (e ▸ subset_closure rfl)
      rw [if_neg hvz, Units.val_one]
      exact (unitAt_one v).ord_eq_zero

end GlobalTheory.PrimeDivCartier


open GlobalTheory.PrimeDivCartier in
theorem GlobalTheory.primeDivisor_isCartier : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X],
    (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ z : X, Order.coheight z = 1 →
      ∃ D : CartierDiv X, D.mult z = 1 ∧ ∀ v, v ≠ z → D.mult v = 0 := by
  intro X _ _ hu z h1
  classical
  haveI : GlobalTheory.IsNormalScheme X := ⟨fun x => inferInstance, fun x => by
    haveI := hu x; exact UniqueFactorizationMonoid.instIsIntegrallyClosed⟩
  choose U hxU π hπ using exists_local_eqn X hu z h1
  have hunit : ∀ x y, y ∈ U x → UnitAt y ((π x : X.functionField) / π y) := by
    intro x y hy
    have h := (GlobalTheory.T.cartier_divisor_mult_characterize X (0 : CartierDiv X)).2.2.2 y (π x / π y) (fun v hv => by
      have hvx : v ∈ U x := hv.mem_open (U x).isOpen hy
      have hvy : v ∈ U y := hv.mem_open (U y).isOpen (hxU y)
      have e := Scheme.ord_mul (X := X) (x := v) (Units.ne_zero (π x / π y)) (Units.ne_zero (π y))
      rw [← Units.val_mul, div_mul_cancel, hπ x v hvx, hπ y v hvy] at e
      rw [(CartierDiv.isEqn_zero v).mult_eq, Units.val_one, (unitAt_one v).ord_eq_zero]
      split_ifs at e <;> omega)
    simpa using (CartierDiv.isEqn_zero y).iff_unitAt.1 h
  let D : CartierDiv X := show cartierGroup X from
    ⟨fun y => germOf y (π y), fun x => ⟨U x, hxU x, π x, fun y hy => germOf_eq_iff.2 (hunit x y hy)⟩⟩
  have hD : ∀ y, D.IsEqn y (π y) := fun y => rfl
  refine ⟨D, ?_, fun v hv => ?_⟩
  · rw [(hD z).mult_eq, hπ z z (hxU z), if_pos rfl]
  · rw [(hD v).mult_eq, hπ v v (hxU v), if_neg hv]
end
end
