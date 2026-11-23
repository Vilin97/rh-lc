module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinatesFlatLiftStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsFrobeniusLiftStalk
public import Mathlib.Algebra.Ring.Subring.Defs
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Mathlib.Topology.Sheaves.Presheaf
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ModPSquaredStalkSurjective
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartEquationsDifferUnit
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLiftOfUnitMemMap

section

@[expose] public section

set_option autoImplicit false

namespace GlobalTheory.DI


set_option autoImplicit false in
theorem _root_.GlobalTheory.DI.logLift_of_unit_mem_map : ∀ {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) {ι : Type} (F : ι → Kt →+* Kt) (s : Finset ι) (At : Subring Kt), _root_.GlobalTheory.DI.IsFlatLift p π →
    (∀ i ∈ s, ∀ z ∈ At, ∃ w ∈ At, F i z = z ^ p + p * w) → ∀ g : K, g ≠ 0 → g ∈ At.map π →
    g⁻¹ ∈ At.map π → _root_.GlobalTheory.DI.LogLift p π F s (At.map π : Set K) g := by
  intro K Kt _ _ p _ _ π ι F s At hflat hF g hg hmem hinv
  obtain ⟨z, hz, rfl⟩ := Subring.mem_map.mp hmem
  obtain ⟨y, hy, hyz⟩ := Subring.mem_map.mp hinv
  unfold _root_.GlobalTheory.DI.LogLift
  refine ⟨z, rfl, fun i hi => ?_⟩
  obtain ⟨w, hw, hFw⟩ := hF i hi z hz
  refine ⟨y ^ p * w, Subring.mem_map.mpr ⟨y ^ p * w, At.mul_mem (At.pow_mem hy p) hw, rfl⟩, ?_⟩
  have h0 : (p : Kt) * (w - z ^ p * y ^ p * w) = 0 := by
    rw [hflat.ann]
    simp only [map_sub, map_mul, map_pow, hyz]
    rw [← mul_pow, mul_inv_cancel₀ hg, one_pow, one_mul, sub_self]
  rw [hFw]
  linear_combination h0

end GlobalTheory.DI
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLiftPpZero

section

@[expose] public section

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

section LogMul

variable {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p] (π : Kt →+* K)
  {ι : Type} (F : ι → Kt →+* Kt) (s : Finset ι) (A : Subring K)

omit [Fact p.Prime] in
lemma logLift_pp_zero (hπ : IsFlatLift p π) : (p : Kt) * p = 0 := by
  rw [hπ.ann]; simp [map_natCast, CharP.cast_eq_zero]

omit [Fact p.Prime] in
lemma logLift_one : LogLift p π F s (A : Set K) 1 :=
  ⟨1, map_one π, fun i _ => ⟨0, by simp [A.zero_mem], by simp⟩⟩

omit [Fact p.Prime] in
lemma logLift_mul (hπ : IsFlatLift p π) {g g' : K} (hg : LogLift p π F s (A : Set K) g)
    (hg' : LogLift p π F s (A : Set K) g') : LogLift p π F s (A : Set K) (g * g') := by
  obtain ⟨z, hz, hF⟩ := hg
  obtain ⟨z', hz', hF'⟩ := hg'
  have hpp := logLift_pp_zero p π hπ
  refine ⟨z * z', by simp [hz, hz'], fun i hi => ?_⟩
  obtain ⟨w, hw, hFw⟩ := hF i hi
  obtain ⟨w', hw', hFw'⟩ := hF' i hi
  refine ⟨w + w', by rw [map_add (f := _)]; exact A.add_mem hw hw', ?_⟩
  rw [map_mul, hFw, hFw', mul_pow]
  linear_combination (z ^ p * z' ^ p * w * w') * hpp

omit [Fact p.Prime] in
lemma logLift_inv (hπ : IsFlatLift p π) {g : K} (hg0 : g ≠ 0) (hg : LogLift p π F s (A : Set K) g) :
    LogLift p π F s (A : Set K) g⁻¹ := by
  obtain ⟨z, hz, hF⟩ := hg
  have hpp := logLift_pp_zero p π hπ
  have hπp : π (p : Kt) = 0 := by simp [map_natCast, CharP.cast_eq_zero]
  obtain ⟨z', hz'⟩ := hπ.surj g⁻¹
  obtain ⟨e, he⟩ := (hπ.ker (z * z' - 1)).1 (by simp [hz, hz', hg0])
  set u := z' * (1 - p * e) with hu
  have hzu : z * u = 1 := by
    have : z * z' = 1 + p * e := by linear_combination he
    rw [hu, ← mul_assoc, this]; linear_combination (-(e * e)) * hpp
  have hπu : π u = g⁻¹ := by simp [hu, hz', hπp]
  clear_value u
  refine ⟨u, hπu, fun i hi => ?_⟩
  obtain ⟨w, hw, hFw⟩ := hF i hi
  refine ⟨-w, by rw [map_neg]; exact A.neg_mem hw, ?_⟩
  have h1 : F i z * F i u = 1 := by rw [← map_mul, hzu, map_one]
  have h2 : F i z * (u ^ p * (1 + p * -w)) = 1 := by
    rw [hFw]
    have : z ^ p * u ^ p = 1 := by rw [← mul_pow, hzu, one_pow]
    linear_combination (1 - (p:Kt) * w * ((p:Kt) * w)) * this - (w * w) * hpp
  linear_combination (u ^ p * (1 + p * -w)) * h1 - (F i u) * h2

omit [Fact p.Prime] in
lemma logLift_zpow (hπ : IsFlatLift p π) {g : K} (hg0 : g ≠ 0) (hg : LogLift p π F s (A : Set K) g) :
    ∀ n : ℤ, LogLift p π F s (A : Set K) (g ^ n) := by
  have hpow : ∀ {h : K}, LogLift p π F s (A : Set K) h → ∀ k : ℕ, LogLift p π F s (A : Set K) (h ^ k) := by
    intro h hh k
    induction k with
    | zero => simpa using logLift_one p π F s A
    | succ k ih => rw [pow_succ]; exact logLift_mul p π F s A hπ ih hh
  intro n
  cases n with
  | ofNat k => rw [Int.ofNat_eq_coe, zpow_natCast]; exact hpow hg k
  | negSucc k =>
    rw [zpow_negSucc, ← inv_pow]
    exact hpow (logLift_inv p π F s A hπ hg0 hg) (k + 1)

end LogMul

end GlobalTheory.DI
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusLiftUnitTimesCoord

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

theorem unit_mul_logarithmic_lift (p : ℕ) {Kt : Type} [CommRing Kt] (At : Subring Kt)
    (F : Kt →+* Kt) (v v' t : Kt) (_hp : (p : Kt) * p = 0) (hv' : v' ∈ At) (hvv : v * v' = 1)
    (hF : ∃ w ∈ At, F v = v ^ p + p * w) (ht : F t = t ^ p) :
    ∃ w ∈ At, F (v * t) = (v * t) ^ p * (1 + p * w) := by
  obtain ⟨w, hw, hFv⟩ := hF
  refine ⟨v' ^ p * w, At.mul_mem (At.pow_mem hv' p) hw, ?_⟩
  have h1 : v ^ p * v' ^ p = 1 := by rw [← mul_pow, hvv, one_pow]
  rw [map_mul, hFv, ht, mul_pow]
  linear_combination (-(t ^ p * p * w)) * h1

end GlobalTheory.DI
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobeniusLiftUnitTimesCoord

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.frobenius_lift_unit_times_coord : ∀ (p : ℕ) {Kt : Type} [CommRing Kt] (At : Subring Kt) (F : Kt →+* Kt) (v v' t : Kt), (p : Kt) * p = 0 → v' ∈ At → v * v' = 1 → (∃ w ∈ At, F v = v ^ p + p * w) → F t = t ^ p → ∃ w ∈ At, F (v * t) = (v * t) ^ p * (1 + p * w) := by
  first | exact @_root_.GlobalTheory.DI.unit_mul_logarithmic_lift | exact _root_.GlobalTheory.DI.unit_mul_logarithmic_lift | (intros; apply _root_.GlobalTheory.DI.unit_mul_logarithmic_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingImageStalkMap

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI


open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.DI.mem_locRing_iff_exists_stalkIm : ∀ {X Y : Scheme.{0}} [IsIntegral X] (π : X ⟶ Y) (y : X) (h : π (genericPoint X) ⤳ π y), Function.Surjective (π.stalkMap y).hom → ∀ c : X.functionField, c ∈ _root_.GlobalTheory.LogDR.locRing y ↔ ∃ z ∈ _root_.GlobalTheory.DI.stalkIm h, (π.stalkMap (genericPoint X)).hom z = c := by
  intro X Y _ π y h hsurj c
  have hcomm : ∀ b : Y.presheaf.stalk (π y),
      (π.stalkMap (genericPoint X)).hom ((Y.presheaf.stalkSpecializes h).hom b) =
        algebraMap (X.presheaf.stalk y) X.functionField ((π.stalkMap y).hom b) := by
    intro b
    exact Scheme.Hom.stalkSpecializes_stalkMap_apply π _ _
      ((genericPoint_spec X).specializes (Set.mem_univ y)) b
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := hsurj a
    exact ⟨(Y.presheaf.stalkSpecializes h).hom b, ⟨b, rfl⟩, hcomm b⟩
  · rintro ⟨z, ⟨b, rfl⟩, rfl⟩
    exact ⟨(π.stalkMap y).hom b, (hcomm b).symm⟩

end GlobalTheory.DI
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LocalRingImageStalkMap

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.local_ring_image_stalk_map : ∀ {X Y : Scheme.{0}} [IsIntegral X] (π : X ⟶ Y) (y : X) (h : π (genericPoint X) ⤳ π y), Function.Surjective (π.stalkMap y).hom → ∀ c : X.functionField, c ∈ locRing y ↔ ∃ z ∈ stalkIm h, (π.stalkMap (genericPoint X)).hom z = c := by
  first | exact @_root_.GlobalTheory.DI.mem_locRing_iff_exists_stalkIm | exact _root_.GlobalTheory.DI.mem_locRing_iff_exists_stalkIm | (intros; apply _root_.GlobalTheory.DI.mem_locRing_iff_exists_stalkIm <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LiftedStalkMapGermAppLE

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

theorem lifted_stalkMap_germ_appLE {Y Z : Scheme.{0}} (f : Z ⟶ Y) (W : Y.Opens) (W' : Z.Opens)
    (h : W' ≤ f ⁻¹ᵁ W) (z : Z) (hz : z ∈ W') (s : Γ(Y, W)) :
    (f.stalkMap z).hom ((Y.presheaf.germ W (f z) (h hz)).hom s) =
      (Z.presheaf.germ W' z hz).hom ((f.appLE W W' h).hom s) := by
  have h1 := Scheme.Hom.germ_stalkMap_apply f W z (h hz) s
  have h2 := TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE h) z hz ((f.app W).hom s)
  exact h1.trans h2.symm

theorem isLifted_of_sncCharts : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) [IsIntegral X] (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y), IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → ∀ {n s : ℕ} (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec), (∀ i, (L i).IsLB) → ∀ {ι : Type} [Nonempty ι] (C : ι → SncChart g n L σ) (Z : Set X) (U : ι → X.Opens) (hU : ∀ i, U i ≤ π ⁻¹ᵁ (C i).U) (hgen : ∀ i, genericPoint X ∈ U i) (x : ι → Fin n → X.functionFieldˣ) (J : ι → Finset (Fin n)), (∀ i l, (x i l : X.functionField) = fnOf (U i) (hgen i) ((π.appLE (C i).U (U i) (hU i)).hom ((C i).t l))) → (∀ i l, l ∈ J i → ∃ c, (C i).e c = some l) → (∀ i, IsLogChart Z (U i) (x i) (J i)) → IsLifted p Z U x := by
  intro p _ Y X _ q f π hpb n s L σ hL ι _ C Z U hU hgen x J hx hJ hchart
  obtain ⟨i₁⟩ := ‹Nonempty ι›
  have hη : ∀ i, π (genericPoint X) ∈ (C i).U := fun i => hU i (hgen i)
  let πK : Y.presheaf.stalk (π (genericPoint X)) →+* X.functionField := (π.stalkMap (genericPoint X)).hom
  have hflat : IsFlatLift p πK :=
    GlobalTheory.T.etale_coordinates_flat_lift p Y X q f π hpb (C i₁).U (C i₁).t (C i₁).affine (C i₁).etale (genericPoint X) (hη i₁)
  have hpK : (p : X.functionField) = 0 := by
    have h0 := (hflat.ker (p : Y.presheaf.stalk (π (genericPoint X)))).2 ⟨1, by ring⟩
    simpa using h0
  haveI : CharP X.functionField p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hpK
  have hpp := logLift_pp_zero p πK hflat
  choose F hF1 hF2 hF3 using fun i =>
    GlobalTheory.T.exists_frobenius_lift_stalk p q (C i).U (C i).t (C i).affine (C i).etale (π (genericPoint X)) (hη i)

  have hlift : ∀ i l, πK ((Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom ((C i).t l)) =
      (x i l : X.functionField) := by
    intro i l
    rw [hx i l]
    exact lifted_stalkMap_germ_appLE π (C i).U (U i) (hU i) (genericPoint X) (hgen i) ((C i).t l)
  refine ⟨Y.presheaf.stalk (π (genericPoint X)), inferInstance, πK, F, hflat, ?_, ?_, ?_⟩
  · intro i z
    obtain ⟨w, hw⟩ := hF1 i z
    rw [hw, map_add (f := _), map_pow, map_mul, map_natCast, hpK, zero_mul, add_zero]
  · intro i l
    exact ⟨_, hlift i l, hF2 i l⟩
  intro y t hyt a ha
  rcases t.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · obtain ⟨z, hz⟩ := hflat.surj (a : X.functionField)
    exact ⟨z, hz, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  have hsp : π (genericPoint X) ⤳ π y :=
    ((genericPoint_spec X).specializes (Set.mem_univ y)).map π.continuous
  have hsurj := (GlobalTheory.T.mod_p_squared_stalk_surjective p Y X q f π hpb y).1
  have hloc := GlobalTheory.T.local_ring_image_stalk_map π y hsp hsurj
  set At := stalkIm hsp with hAt
  have hmap : (locRing y : Set X.functionField) = (At.map πK : Set X.functionField) := by
    ext c
    rw [SetLike.mem_coe, hloc, SetLike.mem_coe, Subring.mem_map]
  have hstab : ∀ i ∈ t, ∀ z ∈ At, ∃ w ∈ At, F i z = z ^ p + p * w :=
    fun i hi z hz => hF3 i (π y) (hU i (hyt i hi)) hsp z hz
  obtain ⟨u, m, hu, rfl⟩ := ((hchart i₀).logUnit y (hyt i₀ hi₀) a).1 ha
  rw [hmap]

  have hu0 : (u : X.functionField) ≠ 0 := u.ne_zero
  have hU1 : LogLift p πK F t (At.map πK : Set X.functionField) (u : X.functionField) := by
    have h2 := (unitAt_iff hu0).1 hu
    refine logLift_of_unit_mem_map p πK F t At hflat hstab _ hu0 ?_ ?_
    · exact Subring.mem_map.2 ((hloc _).1 h2.1)
    · exact Subring.mem_map.2 ((hloc _).1 h2.2)

  have hcoord : ∀ j ∈ J i₀, LogLift p πK F t (At.map πK : Set X.functionField) (x i₀ j : X.functionField) := by
    intro j hj
    obtain ⟨c, hc⟩ := hJ i₀ j hj
    refine ⟨_, hlift i₀ j, fun i hi => ?_⟩
    obtain ⟨v, hv⟩ := GlobalTheory.T.snc_chart_equations_differ_unit q L σ hL (C i₀) (C i) (π y) (hU i₀ (hyt i₀ hi₀)) (hU i (hyt i hi)) c
    rw [hc] at hv
    change (Y.presheaf.germ (C i₀).U (π y) (hU i₀ (hyt i₀ hi₀))).hom ((C i₀).t j) = _ at hv
    have hv' := congrArg (Y.presheaf.stalkSpecializes hsp).hom hv
    have e1 : ∀ (V : Y.Opens) (hV : π y ∈ V) (r : Γ(Y, V)),
        (Y.presheaf.stalkSpecializes hsp).hom ((Y.presheaf.germ V (π y) hV).hom r) =
          (Y.presheaf.germ V (π (genericPoint X)) (hsp.mem_open V.isOpen hV)).hom r :=
      fun V hV r => TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf hV hsp r
    rw [map_mul] at hv'
    have hv2 : (Y.presheaf.germ (C i₀).U (π (genericPoint X)) (hη i₀)).hom ((C i₀).t j) =
        (Y.presheaf.stalkSpecializes hsp).hom (v : Y.presheaf.stalk (π y)) *
          (Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom (((C i).e c).elim 1 (C i).t) := by
      refine (e1 _ _ _).symm.trans (hv'.trans ?_)
      congr 1
      exact e1 _ _ _
    set sv := (Y.presheaf.stalkSpecializes hsp).hom (v : Y.presheaf.stalk (π y)) with hsv
    set sv' := (Y.presheaf.stalkSpecializes hsp).hom ((v⁻¹ : (Y.presheaf.stalk (π y))ˣ) :
      Y.presheaf.stalk (π y)) with hsv'
    have hsvA : sv ∈ At := ⟨_, rfl⟩
    have hsv'A : sv' ∈ At := ⟨_, rfl⟩
    have hvv : sv * sv' = 1 := by rw [hsv, hsv', ← map_mul, Units.mul_inv, map_one]
    have hkey : ∀ o : Option (Fin n),
        F i ((Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom (o.elim 1 (C i).t)) =
          ((Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom (o.elim 1 (C i).t)) ^ p := by
      rintro (_ | l)
      · show F i ((Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom 1) = _
        simp
      · exact hF2 i l
    obtain ⟨w, hwA, hw⟩ := GlobalTheory.T.frobenius_lift_unit_times_coord p At (F i) sv sv' _ hpp hsv'A hvv (hstab i hi sv hsvA) (hkey ((C i).e c))
    refine ⟨w, Subring.mem_map.2 ⟨w, hwA, rfl⟩, ?_⟩
    rw [hv2]
    exact hw
  rw [Units.val_mul, Units.coe_prod]
  refine logLift_mul p πK F t _ hflat hU1 ?_
  refine Finset.prod_induction _ (LogLift p πK F t (At.map πK : Set X.functionField))
    (fun _ _ => logLift_mul p πK F t _ hflat) (logLift_one p πK F t _) (fun j hj => ?_)
  rw [Units.val_zpow_eq_zpow_val]
  exact logLift_zpow p πK F t _ hflat (x i₀ j).ne_zero (hcoord j hj) (m j)

end GlobalTheory.DI
end
end
end
