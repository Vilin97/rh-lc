module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import GroundTheory.PAdicHodge.AxLemma
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldIntegerIffAlgebraicClosureNormStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import GroundTheory.LocalFields.Interface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharactersDetectRestrictNormalInfFiniteLevelStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.NumberTheory.LocalField.Basic
import GroundTheory.LocalFields.Examples
public import GroundTheory.LocalFields.FiniteExtension
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCongruenceFiltrationFiniteTowerBoundStatement
public import GroundTheory.LocalFields.Examples
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationOfPrimeOfGaloisExtensionStatement
public import GroundTheory.LocalFields.KroneckerWeber
public import GroundTheory.LocalFields.Ramification
import Mathlib.Algebra.Order.Star.Int
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AxLemmaFiniteGaloisPadic

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem norm_natCast_self_Om (l : ℕ) [Fact l.Prime] : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  have h : (l : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := (map_natCast _ _).symm
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]

theorem axConstant_le_sq (l : ℕ) [hl : Fact l.Prime] : GroundTheory.PAdicHodge.axConstant l ≤ (l : ℝ) ^ 2 := by
  have h2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  have hexp : (l : ℝ) / ((l : ℝ) - 1) ^ 2 ≤ 2 := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  unfold GroundTheory.PAdicHodge.axConstant
  calc (l : ℝ) ^ ((l : ℝ) / ((l : ℝ) - 1) ^ 2) ≤ (l : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
    _ = (l : ℝ) ^ 2 := by norm_cast

theorem axIn_padic : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)], AxIn ℚ_[l] L l := by
  intro l _ L _ _ _ _ _ _ _ _ _ _
  intro J x hx
  have hO := GlobalTheory.T.localFieldInteger_iff_algebraicClosureNorm l L
  let φ : L →ₐ[ℚ_[l]] Om l := IsScalarTower.toAlgHom ℚ_[l] L (Om l)
  have hφ : ∀ y : L, φ y = algebraMap L (Om l) y := fun y => rfl
  let F : IntermediateField ℚ_[l] L := IntermediateField.fixedField J
  let E : IntermediateField ℚ_[l] (Om l) := F.map φ
  have hmove : ∀ g : Gal(Om l/E), ‖g (φ x) - φ x‖ ≤ 1 := by
    intro g
    let g' : Om l ≃ₐ[ℚ_[l]] Om l := g.restrictScalars ℚ_[l]
    let τ : L ≃ₐ[ℚ_[l]] L := AlgEquiv.restrictNormalHom L g'
    have hτ : ∀ y : L, φ (τ y) = g' (φ y) := fun y => AlgEquiv.restrictNormal_commutes g' L y
    have hτJ : τ ∈ J := by
      rw [← IntermediateField.fixingSubgroup_fixedField J]
      rintro ⟨y, hy⟩
      apply φ.toRingHom.injective
      change φ (τ y) = φ y
      rw [hτ]
      have hyE : φ y ∈ E := ⟨y, hy, rfl⟩
      exact g.commutes ⟨φ y, hyE⟩
    have h1 := (hO (τ x - x)).1.1 (hx τ hτJ)
    rw [map_sub, ← hφ, ← hφ, hτ] at h1
    exact h1
  obtain ⟨Y, hYE, hY⟩ := GroundTheory.PAdicHodge.ax_lemma (K := E) (φ x) hmove
  obtain ⟨y, hyF, rfl⟩ := hYE
  refine ⟨y, fun σ hσ => (IntermediateField.mem_fixedField_iff J y).1 hyF σ hσ, ?_⟩
  rw [(hO _).1, map_mul, map_pow, map_natCast, map_sub, norm_mul, norm_pow, norm_natCast_self_Om, ← hφ, ← hφ]
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hc := axConstant_le_sq l
  rw [mul_one] at hY
  calc ((l : ℝ)⁻¹) ^ 2 * ‖φ x - φ y‖ ≤ ((l : ℝ)⁻¹) ^ 2 * (l : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (hY.trans hc) (by positivity)
    _ = 1 := by rw [inv_pow, inv_mul_cancel₀ (by positivity)]

end GlobalTheory.PMon.Ram
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AxLemmaFiniteGaloisPadicStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.axLemma_finiteGalois_padic : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)], AxIn ℚ_[l] L l := by
  first | exact @GlobalTheory.PMon.Ram.axIn_padic | exact GlobalTheory.PMon.Ram.axIn_padic | (intros; apply GlobalTheory.PMon.Ram.axIn_padic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeIndexMulCardMapInf

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_le_index_mul_card_map_inf (G H : Type) [Group G] [Group H] [Finite H]
    (f : G →* H) (N : Subgroup G) (I : Subgroup H) (hf : Function.Surjective f)
    (hN : N.index ≠ 0) : Nat.card ↥I ≤ N.index * Nat.card ↥(N.map f ⊓ I) := by
  have h1 : (N.map f).relIndex I * Nat.card ↥(N.map f ⊓ I) = Nat.card I := by
    rw [Subgroup.relIndex, mul_comm, ← Subgroup.card_mul_index ((N.map f).subgroupOf I)]
    congr 1
    rw [← Subgroup.inf_subgroupOf_right]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
  have h2 : (N.map f).relIndex I ≤ (N.map f).index := by
    rw [← Subgroup.relIndex_top_right]
    apply Subgroup.relIndex_le_of_le_right le_top
    rw [Subgroup.relIndex_top_right]
    exact Subgroup.index_ne_zero_of_finite
  have h3 : (N.map f).index ≤ N.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Subgroup.index_map_dvd N hf)
  rw [← h1]
  exact Nat.mul_le_mul_right _ (h2.trans h3)

end GlobalTheory.PMon.Ram
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisKerLeRange

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem exists_galois_ker_le_range (l : ℕ) [Fact l.Prime] (U : Subgroup (GQ l)) (S : Set (Om l))
    (hU : IsOpen (U : Set (GQ l))) (hS : S.Finite) :
    ∃ (L : Type) (_ : Field L) (_ : ValuativeRel L) (_ : TopologicalSpace L) (_ : IsNonarchimedeanLocalField L)
      (_ : Algebra ℚ_[l] L) (_ : ValuativeExtension ℚ_[l] L) (_ : FiniteDimensional ℚ_[l] L)
      (_ : IsGalois ℚ_[l] L) (_ : Algebra L (Om l)) (_ : IsScalarTower ℚ_[l] L (Om l)),
      (AlgEquiv.restrictNormalHom L : GQ l →* (L ≃ₐ[ℚ_[l]] L)).ker ≤ U ∧
        S ⊆ Set.range (algebraMap L (Om l)) := by
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff ℚ_[l] (Om l) (U : Set (GQ l))).mp
    (hU.mem_nhds U.one_mem)
  haveI := hS.to_subtype
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let F : IntermediateField ℚ_[l] (Om l) := E ⊔ IntermediateField.adjoin ℚ_[l] S
  let M : IntermediateField ℚ_[l] (Om l) := IntermediateField.normalClosure ℚ_[l] F (Om l)
  haveI : FiniteDimensional ℚ_[l] M := inferInstance
  haveI : Normal ℚ_[l] M := inferInstance
  haveI : IsGalois ℚ_[l] M := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  have hFM : F ≤ M := IntermediateField.le_normalClosure F
  obtain ⟨vr, top, hloc, hext⟩ := exists_isNonarchimedeanLocalField_valuativeExtension ℚ_[l] M
  refine ⟨M, inferInstance, vr, top, hloc, inferInstance, hext, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, ?_⟩
  · rw [IntermediateField.restrictNormalHom_ker]
    intro σ hσ
    apply hEU
    exact (IntermediateField.fixingSubgroup_le (le_trans le_sup_left hFM)) hσ
  · intro x hx
    have : x ∈ M := hFM (le_sup_right (a := E) (IntermediateField.subset_adjoin ℚ_[l] S hx))
    exact ⟨⟨x, this⟩, rfl⟩

end GlobalTheory.PMon.Ram
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrdIsEqCardInertia

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem ordIs_padic_self (l : ℕ) [Fact l.Prime] : OrdIs ℚ_[l] l 1 := by
  unfold OrdIs
  rw [IsDiscreteValuationRing.addVal_uniformizer (GroundTheory.LocalField.Padic.irreducible_natCast_integer l)]
  rfl

theorem ordIs_eq_card_inertia : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)],
    OrdIs L l (Nat.card ↥(lowerRamificationGroup ℚ_[l] L 0)) := by
  intro l _ L _ _ _ _ _ _ _ _ _ _
  have hlL : (l : L) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] L)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hne : ((l : 𝒪[L])) ≠ 0 := by
    intro h
    apply hlL
    have h2 : ((l : 𝒪[L]) : L) = 0 := by rw [h]; rfl
    simpa using h2
  have htop : IsDiscreteValuationRing.addVal 𝒪[L] (l : 𝒪[L]) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  obtain ⟨E, hE⟩ := WithTop.ne_top_iff_exists.1 htop
  have hL : OrdIs L l E := by unfold OrdIs; rw [← hE]; rfl
  obtain ⟨e, he, hEe, hram⟩ := GlobalTheory.T.normalizedValuationOfPrime_of_galoisExtension ℚ_[l] L l E hL
  have h1 := ordIs_padic_self l
  unfold OrdIs at he h1
  have he1 : e = 1 := by
    have := he.symm.trans h1
    exact_mod_cast this
  subst he1
  rw [mul_one] at hEe
  unfold OrdIs
  rw [← hram, ← hEe, ← hE]
  rfl

end GlobalTheory.PMon.Ram
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictNormalHomMemLowerRamificationGroupZero

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem restrictNormalHom_mem_lowerRamificationGroup_zero : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)] (σ : GQ l), (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → AlgEquiv.restrictNormalHom L σ ∈ lowerRamificationGroup ℚ_[l] L 0 := by
  intro l _ L _ _ _ _ _ _ _ _ _ _ σ hσ
  rw [mem_lowerRamificationGroup_iff]
  intro x
  have h01 : ((0 : ℤ) + 1).toNat = 1 := rfl
  rw [h01, pow_one]
  have hx : ‖algebraMap L (Om l) (x : L)‖ ≤ 1 := ((GlobalTheory.T.localFieldInteger_iff_algebraicClosureNorm l L (x : L)).1).1 x.2
  have hc : algebraMap L (Om l) (AlgEquiv.restrictNormalHom L σ (x : L)) = σ (algebraMap L (Om l) (x : L)) :=
    AlgEquiv.restrictNormal_commutes σ L (x : L)
  have hlt : valuation L (AlgEquiv.restrictNormalHom L σ (x : L) - (x : L)) < 1 := by
    rw [(GlobalTheory.T.localFieldInteger_iff_algebraicClosureNorm l L _).2, map_sub, hc]
    exact hσ _ hx
  intro hu
  have h1 := (Valuation.integer.integers (valuation L)).isUnit_iff_valuation_eq_one.1 hu
  have h2 : ((((integerAlgEquiv ℚ_[l] L) ((AlgEquiv.restrictNormalHom L) σ)) x - x : 𝒪[L]) : L) =
      AlgEquiv.restrictNormalHom L σ (x : L) - (x : L) := rfl
  change valuation L ((((integerAlgEquiv ℚ_[l] L) ((AlgEquiv.restrictNormalHom L) σ)) x - x : 𝒪[L]) : L) = 1 at h1
  rw [h2] at h1
  exact hlt.ne h1

end GlobalTheory.PMon.Ram
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDetectedSubgroupTowerRatProof

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem noTowerQ_holds : NoTowerQ := by
  intro l _ N hanti hopen h1 h2 h3
  by_contra hcon
  push Not at hcon
  obtain ⟨k₀, hk₀⟩ := h3 8
  have hex : ∃ k ≥ k₀, ∃ σ ∈ N k, (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) ∧ σ ∉ N (k + 1) := by
    by_contra hno
    push Not at hno
    obtain ⟨j, σ, hσ, hi, hj⟩ := hcon k₀
    have : ∀ i, σ ∈ N (k₀ + i) := by
      intro i
      induction i with
      | zero => exact hσ
      | succ i ih => exact hno (k₀ + i) (by omega) σ ih hi
    exact hj (hanti (by omega : j ≤ k₀ + j) (this j))
  obtain ⟨k, hk, σ₀, hσ₀, hi₀, hn₀⟩ := hex
  have hT : (N k).index ≠ 0 := by
    have : Finite (GQ l ⧸ N k) := Subgroup.quotient_finite_of_isOpen _ (hopen k)
    exact Subgroup.index_ne_zero_of_finite
  set T := (N k).index with hTdef
  choose ι hι x a hxa hdet using fun i : ℕ => hk₀ (k + i) (by omega)
  have hS : (⋃ i ∈ Set.Iic (2 * T), Set.range (x i)).Finite :=
    (Set.finite_Iic _).biUnion fun i _ => by have := hι i; exact Set.finite_range _
  obtain ⟨L, _, _, _, _, _, _, _, _, _, _, hker, hSL⟩ :=
    exists_galois_ker_le_range l (N (k + (2 * T + 8))) _ (hopen _) hS
  set res : GQ l →* (L ≃ₐ[ℚ_[l]] L) := AlgEquiv.restrictNormalHom L with hres
  set I := lowerRamificationGroup ℚ_[l] L 0 with hI
  have hlift : ∀ j ≤ 2 * T + 8, ∀ σ : GQ l, res σ ∈ (N (k + j)).map res → σ ∈ N (k + j) := by
    intro j hj σ ⟨τ, hτ, e⟩
    have h : τ⁻¹ * σ ∈ res.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel]
    have h' : τ⁻¹ * σ ∈ N (k + j) := hanti (by omega) (hker h)
    simpa using (N (k + j)).mul_mem hτ h'
  have hE : 0 < Nat.card I := Nat.card_pos
  have hfin := GlobalTheory.T.inertia_congruenceFiltration_finite_tower_bound ℚ_[l] L l (Nat.card I) T (fun j => (N (k + j)).map res ⊓ I) Fact.out hE
    (ordIs_eq_card_inertia l L) (GlobalTheory.T.axLemma_finiteGalois_padic l L)
    (fun i j hij => inf_le_inf_right _ (Subgroup.map_mono (hanti (by omega)))) inf_le_right
    (fun h => hn₀ (hlift 1 (by omega) σ₀
      (h ⟨⟨σ₀, hσ₀, rfl⟩, restrictNormalHom_mem_lowerRamificationGroup_zero l L σ₀ hi₀⟩).1))
    (by
      rintro _ ⟨⟨σ, hσ, rfl⟩, hσI⟩
      exact ⟨⟨σ ^ l, h1 k σ hσ, map_pow _ _ _⟩, I.pow_mem hσI l⟩)
    (by
      rintro j hj _ ⟨⟨σ, hσ, rfl⟩, hσI⟩ hp
      refine ⟨⟨σ, h2 (k + j) σ (hanti (Nat.zero_le _) hσ) (hlift (j + 1) hj _ ?_), rfl⟩, hσI⟩
      rw [map_pow]; exact hp.1)
    (by
      intro i hi
      have := GlobalTheory.T.characters_detect_restrictNormal_inf_finiteLevel l L 8 (N (k + i)) (N (k + i + 8)) I (ι i) (x i) (a i)
        (fun b => hSL (Set.mem_biUnion (show i ∈ Set.Iic (2 * T) from hi) ⟨b, rfl⟩)) (hxa i) (hdet i)
      simpa [add_assoc] using this)
  have hidx := card_le_index_mul_card_map_inf (GQ l) (L ≃ₐ[ℚ_[l]] L) res (N k) I
    (AlgEquiv.restrictNormalHom_surjective _) hT
  have hlt : T < 2 ^ T := Nat.lt_two_pow_self
  have hpos : 0 < Nat.card ↥((N k).map res ⊓ I) := Nat.card_pos
  simp only [add_zero] at hfin
  nlinarith

end GlobalTheory.PMon.Ram

end
end
end
