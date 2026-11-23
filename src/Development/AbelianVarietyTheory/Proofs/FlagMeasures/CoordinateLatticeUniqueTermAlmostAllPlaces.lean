module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HmUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Equality
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HmUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameLatticeUnimodularGeneratorsExponentZeroStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCoordinateLatticeIsTermTrivialWitnessesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalHermitianFramesGoodAlmostAllPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFrameClassProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTermSplitsUnimodularComplementStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerFramesCoordinateLatticeGoodPlaceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalSameIntegralSpanUnimodular

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.SelfDual

open Matrix GlobalTheory.HL.Eichler GlobalTheory.UnramOrder

theorem exists_orthonormal_same_span : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ b : Fin m → Fin n → E, (∀ i j, hf L Hm (b i) (b j) ∈ L.O) → (∃ P : Matrix (Fin m) (Fin m) E, IsIntM L P ∧ (Matrix.of fun i j => hf L Hm (b i) (b j)) * P = 1) → ∃ b' : Fin m → Fin n → E, (∀ i j, hf L Hm (b' i) (b' j) = if i = j then 1 else 0) ∧ Submodule.span L.O (Set.range b') = Submodule.span L.O (Set.range b) := by
  intro F _ _ _ _ _ E _ _ _ L n m Hm hH b hint₀ hunim
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨htr, -, -, hpir, -, -, -, hnorm⟩ := order_facts L ϖ hϖ
  obtain ⟨P₀, hP₀, hGP₀⟩ := hunim
  have hmem : ∀ i, b i ∈ Submodule.span L.O (Set.range b) := fun i =>
    Submodule.subset_span ⟨i, rfl⟩
  have hsm : ∀ (a : L.O) (v : Fin n → E), a • v = (a : E) • v := fun _ _ => rfl
  let c : L.O →+* L.O := (L.cj : E →+* E).restrict L.O L.O fun x hx => cj_mem L hx
  have hcv : ∀ x : L.O, ((c x : L.O) : E) = L.cj x := fun _ => rfl
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (L.cj_cj x)
  let G : Matrix (Fin m) (Fin m) L.O := fun i j => ⟨hf L Hm (b i) (b j), hint₀ i j⟩
  have hGv : ∀ i j, (G i j : E) = hf L Hm (b i) (b j) := fun _ _ => rfl
  have hG : ∀ i j, c (G i j) = G j i := fun i j => Subtype.ext (hf_cj L hH.1 _ _)
  let Q : Matrix (Fin m) (Fin m) L.O := fun i j => ⟨P₀ i j, hP₀ i j⟩
  have hGQ : G * Q = 1 := by
    ext i j
    have h := congrFun (congrFun hGP₀ i) j
    rw [Matrix.one_apply, apply_ite Subtype.val, OneMemClass.coe_one, ZeroMemClass.coe_zero,
      Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum]
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    exact h
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a => (algebraMap_mem_iff L a).2 a.2
  let i : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O hint
  let : Algebra 𝒪[F] L.O := i.toAlgebra
  have hfix : ∀ x, c x = x → x ∈ (algebraMap 𝒪[F] L.O).range := fun x hx => by
    obtain ⟨a, ha⟩ := exists_int_of_fixed L x.2 (congrArg Subtype.val hx)
    exact ⟨a, Subtype.ext ha.symm⟩
  have hinj : Function.Injective (algebraMap 𝒪[F] L.O) := fun a b h =>
    Subtype.ext (algebraMap_inj L (congrArg Subtype.val h))
  obtain ⟨P, hP, hGP⟩ := GlobalTheory.UnramifiedHermitian.exists_eq_transpose_mul_map (R₀ := 𝒪[F]) c hc hfix
    (by
      obtain ⟨w, hw, h⟩ := htr 1
      exact ⟨⟨w, hw⟩, Subtype.ext (by simpa [hcv] using h)⟩)
    (fun u hu hu' => by
      obtain ⟨v, hv⟩ := hu'.exists_right_inv
      have hv' := congrArg c hv
      rw [map_mul, hu, map_one] at hv'
      obtain ⟨s, rfl⟩ := hfix v (by linear_combination v * hv' - c v * hv)
      obtain ⟨r, rfl⟩ := hfix u hu
      have hr : IsUnit r := IsUnit.of_mul_eq_one s (hinj (by rw [map_mul, hv, map_one]))
      obtain ⟨x, hx, h⟩ := hnorm hr.unit
      exact ⟨⟨x, hx⟩, Subtype.ext h⟩)
    hG (Matrix.isUnit_det_of_right_inverse hGQ)
  have hQ : (P⁻¹)ᵀ * G * (P⁻¹).map c = 1 := by
    rw [hGP, ← Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hP,
      Matrix.transpose_one, Matrix.one_mul, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hP,
      Matrix.map_one _ (map_zero c) (map_one c)]
  refine ⟨fun i => ∑ k, P⁻¹ k i • b k, fun i j => ?_, le_antisymm ?_ ?_⟩
  · have h := congrArg Subtype.val (congrFun (congrFun hQ i) j)
    rw [Matrix.one_apply, apply_ite Subtype.val, OneMemClass.coe_one, ZeroMemClass.coe_zero] at h
    rw [← h]
    simp only [hsm, hf_sum_l, hf_sum_r, Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum,
      Subring.coe_mul, Matrix.transpose_apply, Matrix.map_apply, hcv, hGv]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hmem l)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine (Submodule.mem_span_range_iff_exists_fun L.O).2 ⟨fun i => P i k, ?_⟩
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have h : ∀ l, ∑ i, P i k * P⁻¹ l i = if l = k then 1 else 0 := fun l => by
      rw [← Matrix.one_apply, ← Matrix.nonsing_inv_mul _ hP, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    simp [← Finset.sum_smul, h]

end GlobalTheory.HL.SelfDual
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalSameIntegralSpanUnimodularStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.exists_orthonormal_same_integralSpan_unimodular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ b : Fin m → Fin n → E, (∀ i j, hf L Hm (b i) (b j) ∈ L.O) → (∃ P : Matrix (Fin m) (Fin m) E, IsIntM L P ∧ (Matrix.of fun i j => hf L Hm (b i) (b j)) * P = 1) → ∃ b' : Fin m → Fin n → E, (∀ i j, hf L Hm (b' i) (b' j) = if i = j then 1 else 0) ∧ Submodule.span L.O (Set.range b') = Submodule.span L.O (Set.range b) := by
  first | exact @GlobalTheory.HL.SelfDual.exists_orthonormal_same_span | exact GlobalTheory.HL.SelfDual.exists_orthonormal_same_span | (intros; apply GlobalTheory.HL.SelfDual.exists_orthonormal_same_span <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GoodPlaceGramInvariantMinorsValuationZero

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.StdPlace.UnitVal

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem vE_eq_zero_of_unit (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {c : F}
    (hc : algebraMap F E c ∈ L.O) (hu : ∃ y ∈ L.O, algebraMap F E c * y = 1) :
    vE L ϖ (algebraMap F E c) = 0 := by
  obtain ⟨hadd, -, hint, -⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  obtain ⟨y, hy, hcy⟩ := hu
  have hE : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; omega)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hcy
    exact zero_ne_one hcy
  have hyc : y = algebraMap F E c⁻¹ := by
    have h1 : algebraMap F E c * algebraMap F E c⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
    calc y = (algebraMap F E c⁻¹ * algebraMap F E c) * y := by rw [mul_comm (algebraMap F E c⁻¹), h1, one_mul]
      _ = algebraMap F E c⁻¹ * (algebraMap F E c * y) := by ring
      _ = algebraMap F E c⁻¹ := by rw [hcy, mul_one]
  have hci : c⁻¹ ∈ 𝒪[F] := (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 (hyc ▸ hy)
  have hcO : c ∈ 𝒪[F] := (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 hc
  have h1 := (hint c hc0).2 hcO
  have h2 := (hint c⁻¹ (inv_ne_zero hc0)).2 hci
  have h11 := hadd 1 1 one_ne_zero one_ne_zero
  rw [one_mul] at h11
  have h3 := hadd c c⁻¹ hc0 (inv_ne_zero hc0)
  rw [mul_inv_cancel₀ hc0] at h3
  omega

end GlobalTheory.HL.StdPlace.UnitVal


open GlobalTheory.HL.StdPlace.UnitVal in
theorem GlobalTheory.HL.StdPlace.vE_G_D_eq_zero : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), Good S → vE L S.ϖ S.G = 0 ∧ ∀ l, S.D l ≠ 0 → vE L S.ϖ (S.D l * L.cj (S.D l)) = 0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S hS
  obtain ⟨-, -, ⟨c, -, hGc⟩, -⟩ := GlobalTheory.FrameBasic.main L r k S
  refine ⟨?_, fun l hl => ?_⟩
  · rw [hGc]
    obtain ⟨hG, y, hy, hGy⟩ := hS.G_unit
    exact vE_eq_zero_of_unit L S.ϖ_irr (hGc ▸ hG) ⟨y, hy, hGc ▸ hGy⟩
  · obtain ⟨hD, y, hy, hDy⟩ := hS.D_unit l hl
    obtain ⟨c, hc⟩ := GlobalTheory.UnramOrder.exists_norm L hD
    rw [hc]
    refine vE_eq_zero_of_unit L S.ϖ_irr (hc ▸ L.O.mul_mem hD (GlobalTheory.UnramOrder.cj_mem L hD))
      ⟨y * L.cj y, L.O.mul_mem hy (GlobalTheory.UnramOrder.cj_mem L hy), ?_⟩
    rw [← hc]
    calc S.D l * L.cj (S.D l) * (y * L.cj y) = (S.D l * y) * L.cj (S.D l * y) := by rw [map_mul]; ring
      _ = 1 := by rw [hDy, map_one, mul_one]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GoodPlaceGramInvariantMinorsValuationZeroStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.goodPlace_gramInvariant_minors_valuation_zero : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), Good S → vE L S.ϖ S.G = 0 ∧ ∀ l, S.D l ≠ 0 → vE L S.ϖ (S.D l * L.cj (S.D l)) = 0 := by
  first | exact @GlobalTheory.HL.StdPlace.vE_G_D_eq_zero | exact GlobalTheory.HL.StdPlace.vE_G_D_eq_zero | (intros; apply GlobalTheory.HL.StdPlace.vE_G_D_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordinateLatticeUniqueTermAlmostAllPlaces

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.StdPlace

theorem term_orbit {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (ha : S.a = 0)
    {d d₁ : S.Datum} {Λ Λ₁ : Submodule L.O S.V} (hT : S.IsTerm d Λ) (hT₁ : S.IsTerm d₁ Λ₁)
    (hM : S.M d Λ = S.M d₁ Λ₁) : ∃ h ∈ S.H0, h • Λ₁ = Λ := by
  have : IsArtinianRing E := by
    have := L.free
    have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
    exact IsArtinianRing.of_finite F E
  obtain ⟨u₀, hu₀, hE, hui, hup⟩ := GlobalTheory.T.frameLattice_unimodular_generators_exponent_zero L r k S d Λ hT ha
  obtain ⟨b₀, hbW, hΛ, hbi, hbp⟩ := GlobalTheory.T.hermitianTerm_splits_unimodular_complement L r k S d Λ hT ha
  obtain ⟨c₀, hcW, hΛ₁, hci, hcp⟩ := GlobalTheory.T.hermitianTerm_splits_unimodular_complement L r k S d₁ Λ₁ hT₁ ha
  obtain ⟨u, huo, hus⟩ := GlobalTheory.T.exists_orthonormal_same_integralSpan_unimodular L S.Hm S.herm u₀ hui hup
  obtain ⟨b, hbo, hbs⟩ := GlobalTheory.T.exists_orthonormal_same_integralSpan_unimodular L S.Hm S.herm b₀ hbi hbp
  obtain ⟨c, hco, hcs⟩ := GlobalTheory.T.exists_orthonormal_same_integralSpan_unimodular L S.Hm S.herm c₀ hci hcp
  have hsp : ∀ (w : Fin (k - 1) → S.V) (w₀ : Fin (k - 1) → S.V), (∀ i, w₀ i ∈ S.W0) →
      Submodule.span L.O (Set.range w) = Submodule.span L.O (Set.range w₀) → ∀ i, w i ∈ S.W0 := by
    intro w w₀ h0 he i
    have h1 : w i ∈ Submodule.span L.O (Set.range w₀) := by
      rw [← he]; exact Submodule.subset_span ⟨i, rfl⟩
    have h2 : Submodule.span L.O (Set.range w₀) ≤ S.W0.restrictScalars L.O :=
      Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact h0 j)
    exact h2 h1
  have hbW' := hsp b b₀ hbW hbs
  have hcW' := hsp c c₀ hcW hcs
  have huME : ∀ i, u i ∈ S.ME := by
    intro i
    have h1 : u i ∈ Submodule.span L.O (Set.range u₀) := by
      rw [← hus]; exact Submodule.subset_span ⟨i, rfl⟩
    have h2 : Submodule.span L.O (Set.range u₀) ≤ S.ME.restrictScalars L.O :=
      Submodule.span_le.2 (by
        rintro _ ⟨j, rfl⟩
        rw [← hE]; exact Submodule.subset_span ⟨j, rfl⟩)
    exact h2 h1
  have horth : ∀ {w : S.V}, w ∈ S.W0 → ∀ i, hf L S.Hm w (u i) = 0 := fun hw i => hw _ (huME i)
  have horth' : ∀ {w : S.V}, w ∈ S.W0 → ∀ i, hf L S.Hm (u i) w = 0 := fun hw i => by
    rw [GlobalTheory.FrameBasic.hf_conj L S.herm.1, horth hw i, map_zero]

  let x : Fin (2 * (r + 1) + (k - 1)) → S.V := Fin.append u c
  let y : Fin (2 * (r + 1) + (k - 1)) → S.V := Fin.append u b
  have gx : ∀ i j, hf L S.Hm (x i) (x j) = if i = j then 1 else 0 := by
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [x, huo, Fin.ext_iff]
    · simp [x, horth' (hcW' j), Fin.ext_iff]; omega
    · simp [x, horth (hcW' i), Fin.ext_iff]; omega
    · simp [x, hco, Fin.ext_iff]
  have gy : ∀ i j, hf L S.Hm (y i) (y j) = if i = j then 1 else 0 := by
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [y, huo, Fin.ext_iff]
    · simp [y, horth' (hbW' j), Fin.ext_iff]; omega
    · simp [y, horth (hbW' i), Fin.ext_iff]; omega
    · simp [y, hbo, Fin.ext_iff]
  obtain ⟨g, hg, hgx⟩ := GlobalTheory.HermTuple.witt_tuples L S.Hm S.herm _ x y
    (fun i j => by rw [gx, gy]) (by
      have : (Matrix.of fun i j => hf L S.Hm (x i) (x j)) = 1 := by
        ext i j; simp [gx, Matrix.one_apply]
      rw [this]; simp)
  have hgu : ∀ i, g (u i) = u i := fun i => by
    have := hgx (Fin.castAdd _ i)
    simpa [x, y] using this
  have hgc : ∀ i, g (c i) = b i := fun i => by
    have := hgx (Fin.natAdd _ i)
    simpa [x, y] using this
  have hfix : ∀ v ∈ S.ME, g v = v := by
    intro v hv
    rw [← hE] at hv
    let K : Submodule E S.V := LinearMap.eqLocus (g : S.V →ₗ[E] S.V) LinearMap.id
    have h1 : Submodule.span L.O (Set.range u) ≤ K.restrictScalars L.O :=
      Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hgu i)
    have h2 : Submodule.span E (Set.range u₀) ≤ K :=
      Submodule.span_le.2 (by
        rintro _ ⟨j, rfl⟩
        apply h1
        rw [hus]
        exact Submodule.subset_span ⟨j, rfl⟩)
    exact h2 hv
  have hH0 : g ∈ S.H0 :=
    ⟨hg, GlobalTheory.HL.FrameStab.mem_unipOn' bot_le g fun v hv => by rw [hfix v hv, sub_self]; exact Submodule.zero_mem _⟩
  have hsm : ∀ s : Set S.V, g • Submodule.span L.O s = Submodule.span L.O (g '' s) := fun s => by
    rw [Submodule.pointwise_smul_def, Submodule.map_span]; rfl
  have e1 : g • S.M d Λ = S.M d Λ := by
    rw [hu₀, ← hus, hsm, ← Set.range_comp]
    congr 2
    funext i
    exact hgu i
  have e2 : g • Submodule.span L.O (Set.range c) = Submodule.span L.O (Set.range b) := by
    rw [hsm, ← Set.range_comp]
    congr 2
    funext i
    exact hgc i
  refine ⟨g, hH0, ?_⟩
  have e3 : ∀ A B : Submodule L.O S.V, g • (A ⊔ B) = g • A ⊔ g • B := fun A B => by
    simp only [Submodule.pointwise_smul_def, Submodule.map_sup]
  rw [hΛ₁, ← hM, ← hcs, e3, e1, e2, hbs, ← hΛ]

theorem good_place {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (hk : 4 * r + 7 ≤ k) (hG : Good S) :
    S.Hp = 1 ∧ S.St ⊓ MulAction.stabilizer S.GLV (coordLat S) = S.K0 ∧ ∃ d₀, S.IsTermW d₀ (coordLat S) 1 1 ∧
      S.om d₀ (coordLat S) = 1 ∧ S.H0 ⊓ MulAction.stabilizer S.GLV d₀ = S.complementReferenceCompactSubgroup ∧
      (∀ Λ, S.IsTerm d₀ Λ → ∃ h ∈ S.St, Λ = h • coordLat S) ∧
      (∀ Λ, S.IsTerm d₀ Λ → S.Fr d₀ Λ = S.frameCls S.f S.f' → Λ = coordLat S) ∧
      ∀ d Λ, S.IsTerm d Λ → ∃ h ∈ S.H0, d = h • d₀ := by
  obtain ⟨hvG, hvD⟩ := GlobalTheory.T.goodPlace_gramInvariant_minors_valuation_zero L r k S hG
  have hvth : S.vth = 0 := by simp [Frames.vth, hG.gg]
  have ha : S.a = 0 := by simp [Frames.a, hvth, hvG]
  obtain ⟨d₀, hd₀⟩ := GlobalTheory.T.framesCoordinateLattice_isTerm_trivialWitnesses L r k S hG
  have hT₀ : S.IsTerm d₀ (coordLat S) := ⟨(1, 1), hd₀⟩
  obtain ⟨hom, hM₀, hFr₀, -, -⟩ := GlobalTheory.HL.WitIndep.witness_independence L r k S d₀ _ _ _ hd₀
  have hFr₁ : S.Fr d₀ (coordLat S) = S.frameCls S.f S.f' := hFr₀
  have huniq := fun d Λ h => GlobalTheory.HL.UnimodTerm.term_unique L r k S d Λ h ha
  obtain ⟨-, -, hall⟩ := GlobalTheory.HL.GoodClass.one_class L r k S hG.gg hG.D_unit
  have hint : ∀ d Λ, S.IsTerm d Λ → S.IsIntCls (S.Fr d Λ) := fun d Λ h =>
    (TermBasic.term_basic L r k S d Λ h).2.2.2.2.2.2.1
  have hdd : ∀ d d' Λ, S.IsTerm d Λ → S.IsTerm d' Λ → d' = d := fun d d' Λ h h' =>
    (TermBasic.term_basic L r k S d Λ h).2.2.2.2.2.2.2 d' h'
  have hact := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S
  have hcom := GlobalTheory.HL.ComplAct.main L r k S
  have hcls := GlobalTheory.HL.FrameClass.frame_classes L r k S
  refine ⟨(GlobalTheory.HL.GoodPlace.equality L r k S hk hG.gg hvG hvD).2.1, GlobalTheory.T.stabilizer_framesCoordinateLattice_goodPlace L r k S hG ha d₀ hd₀, d₀, hd₀, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hom]
    have h1 : ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V),
        (∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0) → S.psiOf g gs 1 = 1 := by
      intro g gs hd
      have : ∀ j, S.coef g gs 1 j = 0 := fun j => by
        have := hd j.succ j
        rw [if_neg (by simp [Fin.ext_iff])] at this
        exact this
      simp [Frames.psiOf, this]
    have e1 : S.psi 1 = 1 := h1 _ _ S.dual
    have e2 : S.psi' 1 = 1 := h1 _ _ S.dual'
    simp [e1, e2]
  · ext h
    simp only [Subgroup.mem_inf, Frames.complementReferenceCompactSubgroup, MulAction.mem_stabilizer_iff]
    refine and_congr_right fun hh => ⟨fun e => ?_, fun e => ?_⟩
    · have h1 := hcom d₀ _ hT₀ h hh
      rw [e] at h1
      have := (huniq d₀ _ hT₀).2 _ h1.1 h1.2.2.2.2.2
      exact this
    · have h1 := hcom d₀ _ hT₀ h hh
      have e' : h • coordLat S = coordLat S := e
      rw [e'] at h1
      exact hdd _ _ _ hT₀ h1.1
  · intro Λ hΛ
    obtain ⟨h, hh, e⟩ := hall _ (hint _ _ hΛ)
    refine ⟨h, hh, ?_⟩
    have h2 := hact d₀ _ hT₀ h hh
    exact (huniq d₀ _ h2.1).2 _ hΛ (by rw [h2.2.2.2.2.1, hFr₁, e])
  · intro Λ hΛ e
    exact (huniq d₀ _ hT₀).2 _ hΛ (by rw [e, hFr₁])
  · intro d Λ hΛ
    obtain ⟨s, hs, e⟩ := hall _ (hint _ _ hΛ)
    have hsi := S.St.inv_mem hs
    have h2 := hact d _ hΛ _ hsi
    have hT₂ := h2.1
    have hFr₂ : S.Fr d (s⁻¹ • Λ) = S.Fr d₀ (coordLat S) := by
      rw [h2.2.2.2.2.1, e, hFr₁, smul_smul, inv_mul_cancel, one_smul]
    have hM₂ : S.M d (s⁻¹ • Λ) = S.M d₀ (coordLat S) := by
      have h3 : (S.fr d (s⁻¹ • Λ), S.fr' d (s⁻¹ • Λ)) ∈ S.Fr d₀ (coordLat S) := by
        rw [← hFr₂]; exact (hcls _ _).1
      exact ((hcls _ _).2.1 _ h3).2
    obtain ⟨h, hh, e₁⟩ := term_orbit L r k S ha hT₂ hT₀ hM₂
    refine ⟨h, hh, ?_⟩
    have h4 := (hcom d₀ _ hT₀ h hh).1
    rw [e₁] at h4
    exact hdd _ _ _ h4 hT₂

theorem coordinate_lattice_standard : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → {p | ¬ ((G.S p).gg = false ∧ (G.S p).Hp = 1 ∧ (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) = (G.S p).K0 ∧ ∃ d₀, (G.S p).IsTermW d₀ (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) 1 1 ∧ (G.S p).om d₀ (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) = 1 ∧ (G.S p).H0 ⊓ MulAction.stabilizer (G.S p).GLV d₀ = (G.S p).complementReferenceCompactSubgroup ∧ (∀ Λ, (G.S p).IsTerm d₀ Λ → ∃ h ∈ (G.S p).St, Λ = h • (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V)))) ∧ (∀ Λ, (G.S p).IsTerm d₀ Λ → (G.S p).Fr d₀ Λ = (G.S p).frameCls (G.S p).f (G.S p).f' → Λ = (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V)))) ∧ ∀ d Λ, (G.S p).IsTerm d Λ → ∃ h ∈ (G.S p).H0, d = h • d₀)}.Finite := by
  intro F E _ _ _ _ _ sig A r k G hk
  refine (GlobalTheory.T.globalHermitianFrames_good_almost_all_places A r k G).subset fun p hp hg => hp ?_
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  exact ⟨hg.gg, good_place (A.L p) r k (G.S p) hk hg⟩

end GlobalTheory.HL.StdPlace
end
end
